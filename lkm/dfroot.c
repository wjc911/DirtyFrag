#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/kmod.h>
#include <linux/kprobes.h>
#include <linux/ktime.h>
#include <linux/module.h>
#include <linux/namei.h>
#include <linux/ptrace.h>
#include <linux/fs.h>
#include <linux/file.h>
#include <linux/miscdevice.h>
#include <linux/string.h>
#include <linux/uaccess.h>
#include <linux/workqueue.h>

MODULE_LICENSE("GPL");
MODULE_DESCRIPTION("DFRoot LKM");

typedef unsigned long (*kallsyms_lookup_name_t)(const char *name);
typedef void *(*umh_setup_t)(const char *path, char **argv, char **envp, gfp_t gfp,
                             void *init, void *cleanup, void *data);
typedef int (*umh_exec_t)(void *info, int wait);
typedef int  (*kern_path_t)(const char *, unsigned int, struct path *);
typedef int  (*invalidate_t)(struct address_space *);
typedef void (*path_put_t)(const struct path *);
typedef ssize_t (*kernel_write_t)(struct file *, const void *, size_t, loff_t *);
/* filp_open is not EXPORT_SYMBOL'd on this GKI kernel, so it must be resolved
 * through kallsyms and called indirectly rather than linked against. */
typedef struct file *(*filp_open_t)(const char *, int, umode_t);
/* Minimal layout of the front of struct kprobe (kernel 6.12):
 *   struct hlist_node hlist;   +0
 *   struct list_head list;     +16
 *   unsigned long nmissed;     +32
 *   kprobe_opcode_t *addr;     +40
 * Reading nmissed and addr out of our own kprobe is how the module reports
 * whether the kernel ever entered the probe (or could not) instead of
 * inferring it. */
typedef unsigned int (*stack_trace_save_t)(unsigned long *store, unsigned int size,
                                           unsigned int skipnr);

/* Audit target classification. Defined before the table so the initialisers can
 * use them. */
#define DF_CLASS_DECIDE 0x01  /* root-check decision / report path        */
#define DF_CLASS_EGRESS 0x02  /* kernel -> userspace event egress         */
#define DF_CLASS_EXPORT 0x04  /* exported, but no caller inside the guard */
#define DF_CLASS_PRIMARY 0x10 /* short-circuited when enforce mode is on  */

/* The audit target table has to exist before the short-circuit handler that
 * looks its own entry up by address, so the type and the table come first. */
struct df_audit {
    const char *name;
    unsigned int flags;
    struct kprobe kp;
    void *addr;
    int state;               /* 0 = untried, 1 = armed, -1 = missing, -2 = refused */
    unsigned int hits;       /* entries into this probe's handler */
};

static struct df_audit df_audits[] = {
    /* name                              flags                                   */
    { "oplus_root_check_post_handler",   DF_CLASS_DECIDE | DF_CLASS_PRIMARY },
    { "oplus_root_check_pre_handler",    DF_CLASS_DECIDE },
    { "oplus_root_check_succ",           DF_CLASS_DECIDE },
    { "oplus_root_check_succ_upload",    DF_CLASS_DECIDE },
    { "oplus_root_killed",               DF_CLASS_DECIDE | DF_CLASS_EXPORT },
    { "oplus_exe_block_ret_handler",     DF_CLASS_DECIDE | DF_CLASS_PRIMARY },
    { "oplus_report_execveat",           DF_CLASS_DECIDE | DF_CLASS_PRIMARY },
    { "oplus_report_execveat_new",       DF_CLASS_DECIDE | DF_CLASS_PRIMARY },
    { "oplus_secure_harden_kevent",      DF_CLASS_DECIDE | DF_CLASS_PRIMARY },
    { "report_security_event",           DF_CLASS_DECIDE | DF_CLASS_PRIMARY },
    { "kevent_send_to_user",             DF_CLASS_EGRESS | DF_CLASS_PRIMARY },
};
#define DF_AUDIT_N ARRAY_SIZE(df_audits)

static struct kprobe defex_enforce_kp;
static struct kprobe defex_umh_kp;
static int defex_enforce_ok;
static int defex_umh_ok;

static int null_pre_handler(struct kprobe *p, struct pt_regs *regs)
{
    (void)p;
    regs->regs[0] = 0;         /* x0 = DEFEX_ALLOW */
    regs->pc = regs->regs[30]; /* skip body: return to caller */
    return 1;
}

/* Closed-loop self-test state: probe the kernel's own printk, then call it. */
static struct df_audit df_selftest = { .name = "_printk" };

/* Stack capture for the decisive experiment.
 *
 * The self-test proved the probe framework calls back into this module
 * (SELFTEST__printk=12), yet all eleven guard targets stayed at zero hits. So
 * the open question is no longer "does kprobe work" but "what code actually runs
 * when the alert fires". A probe on send_sig / netlink_unicast / __alloc_skb
 * fires when the guard emits its event, and the call stack at that moment names
 * the reporter directly instead of us inferring it from string cross-references.
 *
 * Recorded per probe: hit count plus the first captured stack, symbolised
 * lazily at report time so the handler itself stays minimal. */
#define DF_STACK_DEPTH 16
#define DF_STACK_SLOTS 4   /* send_sig, netlink_unicast, __alloc_skb, genlmsg_put */

struct df_stackcap {
    const char *name;
    struct kprobe kp;
    void *addr;
    int state;
    unsigned int hits;
    unsigned int nr;
    unsigned long stack[DF_STACK_DEPTH];
    bool stacked;            /* stack already dumped to the live report */
};

static struct df_stackcap df_caps[DF_STACK_SLOTS] = {
    { .name = "send_sig" },
    { .name = "netlink_unicast" },
    { .name = "__alloc_skb" },
    { .name = "genlmsg_put" },
};
#define DF_CAP_N ARRAY_SIZE(df_caps)

static stack_trace_save_t df_stack_save;

static int df_cap_pre_handler(struct kprobe *p, struct pt_regs *regs)
{
    struct df_stackcap *c = NULL;
    unsigned int i;

    (void)regs;
    for (i = 0; i < DF_CAP_N; i++) {
        if (df_caps[i].addr == (void *)p->addr) {
            c = &df_caps[i];
            break;
        }
    }
    if (!c)
        return 0;

    c->hits++;
    /* Capture once: enough to identify the caller, and this runs in probe
     * context so it must not do more work than necessary. */
    if (c->nr == 0 && df_stack_save)
        c->nr = df_stack_save(c->stack, DF_STACK_DEPTH, 1);
    return 0;
}

static int df_selftest_pre_handler(struct kprobe *p, struct pt_regs *regs)
{
    (void)p;
    (void)regs;
    df_selftest.hits++;
    return 0;
}

/* Report-only handler: counts entries but never touches regs.
 *
 * Counters are installed on EVERY target, not just the short-circuited ones.
 * The first version counted only the primary set, so "all counters zero" could
 * not distinguish "these functions are not on the alert path" from "no probe in
 * this module ever fires". Counting everything makes the two unambiguous, and
 * the handler runs in probe context so it does nothing but an increment. */
static int df_count_pre_handler(struct kprobe *p, struct pt_regs *regs)
{
    unsigned int i;

    (void)regs;
    for (i = 0; i < DF_AUDIT_N; i++) {
        if (df_audits[i].addr == (void *)p->addr) {
            df_audits[i].hits++;
            break;
        }
    }
    return 0;
}

/* Same, and additionally skips the function body. */
static int df_short_pre_handler(struct kprobe *p, struct pt_regs *regs)
{
    df_count_pre_handler(p, regs);
    return null_pre_handler(p, regs);
}

/*
 * ---------------------------------------------------------------------------
 * OPD2515 anti-root probe audit
 * ---------------------------------------------------------------------------
 * The OPPO guard (oplus_secure_guard_new) detects app-UID -> root transitions
 * and /data execve targets, then kills the offending task with SIGKILL and
 * reports a "security event" to userspace through a generic-netlink channel
 * that SecurityGuard / ExSystemService turn into the visible alert.
 *
 * A previous revision of this module tried to stop that with
 *   sh -c "rmmod oplus_secure_guard_new ..."
 * from the usermode helper below.  That cannot work: the guard is already
 * initialised before this module gets to run, and the helper's own
 * root->nobody credential change is itself something the guard watches.
 *
 * What this revision does instead is resolve the guard's decision/report
 * functions by name and register a kprobe on each.  A device audit run on
 * OPD2515 proved all eleven of them resolve and register (11/11 M), including
 * the STB_LOCAL ones, because Android 16 GKI is built with CONFIG_KALLSYMS_ALL
 * and module-local symbols are in kallsyms.
 *
 * Enforce mode (the default) then short-circuits only the DF_CLASS_PRIMARY
 * targets; the remaining targets are registered so a run still reports whether
 * they are present and probeable, but their function bodies are left alone.
 *
 * Why probes are registered by resolved *address* rather than by
 * .symbol_name: several guard functions are STB_LOCAL, and registering by
 * symbol name would re-resolve through the module loader instead of using the
 * address kallsyms already gave us.
 *
 * Result format written to /dev/dfm0 (also printed to dmesg) is a single line:
 *   ARMED k=v,k=v,...
 * where each value is: M (present, probe registered) / N (symbol missing) /
 * R (present, register_kprobe refused), followed by "HITS <name>=<count>" for
 * every short-circuited target.
 */

/*
 * ---------------------------------------------------------------------------
 * OPD2515 anti-root probe audit
 * ---------------------------------------------------------------------------
 * The OPPO guard (oplus_secure_guard_new) detects app-UID -> root transitions
 * and /data execve targets, then kills the offending task with SIGKILL and
 * reports a "security event" to userspace through a generic-netlink channel
 * that SecurityGuard / ExSystemService turn into the visible alert.
 *
 * A previous revision of this module tried to stop that with
 *   sh -c "rmmod oplus_secure_guard_new ..."
 * from the usermode helper below.  That cannot work: the guard is already
 * initialised before this module gets to run, and the helper's own
 * root->nobody credential change is itself something the guard watches.
 *
 * What this revision does instead is resolve the guard's decision/report
 * functions by name and register a kprobe on each.  A device audit run on
 * OPD2515 proved all eleven of them resolve and register (11/11 M), including
 * the STB_LOCAL ones, because Android 16 GKI is built with CONFIG_KALLSYMS_ALL
 * and module-local symbols are in kallsyms.
 *
 * Enforce mode (the default) then short-circuits only the DF_CLASS_PRIMARY
 * targets; the remaining targets are registered so a run still reports whether
 * they are present and probeable, but their function bodies are left alone.
 *
 * Why probes are registered by resolved *address* rather than by
 * .symbol_name: several guard functions are STB_LOCAL, and registering by
 * symbol name would re-resolve through the module loader instead of using the
 * address kallsyms already gave us.
 *
 * Result format written to /dev/dfm0 (also printed to dmesg) is a single line:
 *   ARMED k=v,k=v,...
 * where each value is: M (present, probe registered) / N (symbol missing) /
 * R (present, register_kprobe refused), followed by a HITS line with the
 * per-target short-circuit counts.
 *
 * Short-circuit set (DF_CLASS_PRIMARY). Device evidence (OPD2515, audit build,
 * logcat 22:38:35) fixed it:
 *   OPLUS_KEVENT_RECORD event_type=3
 *   payload:10051,path@@/data/app/.../lib/arm64/libdfroot.so
 * That payload format string is '%d,path@@%s', and the only function in the
 * guard that references it is oplus_report_execveat -- which is why the first
 * enforce attempt still raised the alert: that reporter was observe-only while
 * report_security_event (a different payload format, '$$uid@@%d$$EVENT_TYPE@@%d')
 * was already short-circuited. The primary set is therefore every reporter that
 * can reach the userspace netlink family, plus the UID path and the egress:
 *   oplus_root_check_post_handler - UID path; dispatches into
 *                                   oplus_root_check_succ -> oplus_root_killed
 *   oplus_exe_block_ret_handler   - execve-path wrapper
 *   oplus_report_execveat         - emits '%d,path@@%s' (the observed alert)
 *   oplus_report_execveat_new     - same reporter, alternate entry
 *   oplus_secure_harden_kevent    - a direct async reporter
 *   report_security_event         - shared report primitive (11 call sites)
 *   kevent_send_to_user           - the single netlink egress
 * The remaining four targets stay observe-only.
 */


static int df_audit_ok;

/* Resolved at runtime: neither is safe to link against (filp_open is not
 * exported; kernel_write is, but resolving both keeps one code path). */
static filp_open_t     df_filp_open;
static kernel_write_t  df_kernel_write;

/* Enforce by default: the short-circuit probes are the product, and the
 * userspace gate fails closed if any of them is not armed. There is no way to
 * pass a module parameter when the module is loaded through the page-cache
 * write primitive, so the escape hatches are file based:
 *   create /data/local/tmp/dfroot-enforce   -> force enforce on
 *   create /data/local/tmp/dfroot-audit-only -> force audit (never skip a body)
 * audit-only exists so an evidence run can be taken without touching any guard
 * function body. */
static int df_hook_enforce = 1;
module_param_named(enforce, df_hook_enforce, int, 0444);
MODULE_PARM_DESC(enforce, "1 = short-circuit the primary guard targets (default)");

#define DF_ENFORCE_FLAG "/data/local/tmp/dfroot-enforce"
#define DF_AUDIT_FLAG   "/data/local/tmp/dfroot-audit-only"

static int df_file_exists(const char *path)
{
    struct file *f;

    if (!df_filp_open)
        return 0;
    f = df_filp_open(path, O_RDONLY, 0);
    if (IS_ERR(f))
        return 0;
    filp_close(f, NULL);
    return 1;
}

static void df_enforce_probe(void)
{
    if (df_file_exists(DF_AUDIT_FLAG)) {
        df_hook_enforce = 0;
        pr_info("dfroot: audit-only requested by %s\n", DF_AUDIT_FLAG);
        return;
    }
    if (!df_hook_enforce && df_file_exists(DF_ENFORCE_FLAG)) {
        df_hook_enforce = 1;
        pr_info("dfroot: enforce mode requested by %s\n", DF_ENFORCE_FLAG);
    }
}

/* Write the whole report in one shot.
 *
 * This used to be called once per line, each time opening /dev/dfm0 with a
 * fresh loff_t pos = 0. Every call therefore wrote from offset 0 and clobbered
 * the previous line's head, which is exactly the corruption the device showed:
 *   TRACE ...
 *   oplus_root_check_succ=0/0 ...     <- ARMED line's prefix destroyed
 * A torn report then made bootstrap.c reject the run as "malformed", so the
 * gate never let KernelSU load. Single open, single write, O_TRUNC. */
static void df_audit_write(const char *msg)
{
    struct file *f;
    loff_t pos = 0;

    if (!df_filp_open || !df_kernel_write) {
        pr_warn("dfroot: audit write unavailable (open=%px write=%px)\n",
                df_filp_open, df_kernel_write);
        return;
    }

    /* 0666: the report is a non-sensitive diagnostic that has to be readable by
     * the debuggable app (via run-as) and by an adb shell, neither of which runs
     * as root. bootstrap.c also copies it into the app's own data dir. */
    f = df_filp_open("/dev/dfm0", O_WRONLY | O_CREAT | O_TRUNC, 0666);
    if (IS_ERR(f)) {
        pr_warn("dfroot: audit write: /dev/dfm0 open failed (%ld)\n", PTR_ERR(f));
        return;
    }
    df_kernel_write(f, msg, strlen(msg), &pos);
    filp_close(f, NULL);
}

/*
 * ---------------------------------------------------------------------------
 * Live report (/dev/dfm1)
 * ---------------------------------------------------------------------------
 * The gate report /dev/dfm0 is written exactly once, at module_init, so its
 * HITS line is by construction an init-time snapshot: nothing has called the
 * targets yet, and it never changes afterwards.  SELFTEST__printk=11 in that
 * file is the giveaway - the _printk probe counts every kernel log line on the
 * system, so a report written even seconds after init would show hundreds, not
 * the exact number of pr_info calls this module itself made during init.
 * Treating that frozen file as "probes never fire" is how the previous round
 * got stuck without ever measuring post-init behaviour.
 *
 * /dev/dfm1 is the corrective instrument: a delayed work item appends the live
 * counters every DF_LIVE_INTERVAL_MS with a T+ timestamp, so the counts can be
 * aligned against logcat's OPLUS_KEVENT records.  /dev/dfm0 is never touched -
 * its format is parsed by the bootstrap gate.
 *
 * The differential canary separates the remaining hypotheses.  It is a second,
 * independent kprobe registered on the same __alloc_skb address with its own
 * counter.  If can grows while the capture probe's hits stay frozen, this
 * module's probe was selectively removed or disabled; if both freeze while the
 * self-test keeps growing, kprobes at that address are inert; if all grow, the
 * probe mechanism is healthy and zero guard-target hits mean the guard does
 * not reach userspace through the probed symbols.
 */

#define DF_LIVE_INTERVAL_MS 2000
#define DF_LIVE_MAX_TICKS   600   /* 20 minutes of post-arming coverage */

static struct delayed_work df_live_work;
static unsigned int df_live_ticks;
static s64 df_live_t0_ns;
static bool df_live_stop;

static struct kprobe df_skb_canary;
static int df_skb_canary_ok;
static unsigned int df_skb_canary_hits;

static int df_canary_pre_handler(struct kprobe *p, struct pt_regs *regs)
{
    (void)p;
    (void)regs;
    df_skb_canary_hits++;
    return 0;
}

/* Append-only sibling of df_audit_write: O_APPEND so consecutive snapshots
 * accumulate instead of clobbering.  NOTE: this runs from a kworker, and on
 * this device SELinux (still Enforcing - the selinux_state write does not
 * take) denies kworker-context writes to tmpfs, so the file stays empty.  It
 * is kept for kernels where it works; the readable path is the misc device
 * below, whose read handler runs in the *caller's* context. */
static void df_live_write(const char *msg)
{
    struct file *f;
    loff_t pos = 0;

    if (!df_filp_open || !df_kernel_write)
        return;
    f = df_filp_open("/dev/dfm1", O_WRONLY | O_CREAT | O_APPEND, 0666);
    if (IS_ERR(f))
        return;
    df_kernel_write(f, msg, strlen(msg), &pos);
    filp_close(f, NULL);
}

/* Format the current snapshot: a LIVE0 line (arming-time addresses) plus a
 * LIVE line (counters now).  Shared by the work item and the misc read. */
static int df_live_format(char *buf, size_t size)
{
    unsigned int i;
    int len = 0;
    s64 t_s = (ktime_get_boottime() - df_live_t0_ns) / NSEC_PER_SEC;

    len += scnprintf(buf + len, size - len, "LIVE0 bt0=%lld can_ok=%d",
                     df_live_t0_ns / NSEC_PER_SEC, df_skb_canary_ok);
    for (i = 0; i < DF_AUDIT_N; i++)
        if (df_audits[i].addr)
            len += scnprintf(buf + len, size - len,
                             " %s=%px", df_audits[i].name, df_audits[i].addr);
    for (i = 0; i < DF_CAP_N; i++)
        if (df_caps[i].addr)
            len += scnprintf(buf + len, size - len,
                             " %s=%px", df_caps[i].name, df_caps[i].addr);
    len += scnprintf(buf + len, size - len, "\n");

    len += scnprintf(buf + len, size - len,
                     "LIVE t=+%lld n=%u st=%u can=%u",
                     t_s, df_live_ticks, df_selftest.hits, df_skb_canary_hits);
    for (i = 0; i < DF_CAP_N; i++)
        len += scnprintf(buf + len, size - len, " %s=%u/%lu",
                         df_caps[i].name, df_caps[i].hits, df_caps[i].kp.nmissed);
    for (i = 0; i < DF_AUDIT_N; i++)
        len += scnprintf(buf + len, size - len, " %s=%u/%lu",
                         df_audits[i].name, df_audits[i].hits,
                         df_audits[i].kp.nmissed);
    len += scnprintf(buf + len, size - len, "\n");
    return len;
}

/* Misc device /dev/dfm2 (major 10, minor 221): every read returns the current
 * snapshot.  The file op runs in the reader's process context, so whoever may
 * read the node at all gets live data - unlike the kworker file write above,
 * which this device's SELinux policy denies. */
static ssize_t df_live_read(struct file *f, char __user *ubuf, size_t cnt, loff_t *ppos)
{
    static char buf[2560];
    ssize_t len, ret;

    if (*ppos > 0 || !cnt)
        return 0;
    len = df_live_format(buf, sizeof(buf));
    ret = (ssize_t)len < (ssize_t)cnt ? len : (ssize_t)cnt;
    if (copy_to_user(ubuf, buf, ret))
        return -EFAULT;
    *ppos = ret;
    return ret;
}

static const struct file_operations df_live_fops = {
    .owner  = THIS_MODULE,
    .open   = nonseekable_open,
    .read   = df_live_read,
    .llseek = no_llseek,
};

static struct miscdevice df_live_dev = {
    .minor = 221,           /* fixed so the bridge can mknod without dmesg */
    .name  = "dfm2",
    .fops  = &df_live_fops,
    .mode  = 0666,
};
static int df_live_misc_ok;

static void df_live_tick(struct work_struct *w)
{
    static char buf[2560];
    unsigned int i;
    s64 t_s = (ktime_get_boottime() - df_live_t0_ns) / NSEC_PER_SEC;

    (void)w;

    df_live_ticks++;
    /* One deliberate printk per tick: the self-test counter must advance by at
     * least one per snapshot, proving handlers still run long after init. */
    pr_info("dfroot: live tick n=%u t=+%lld\n", df_live_ticks, t_s);

    df_live_format(buf, sizeof(buf));
    df_live_write(buf);

    /* Stack lines: the first capture per probe is symbolised inline with %pS,
     * so the caller that actually reached the primitive is named in the file
     * itself and needs no offline kallsyms. */
    for (i = 0; i < DF_CAP_N; i++) {
        static char sbuf[2048];
        int slen = 0;
        unsigned int k;

        if (df_caps[i].nr == 0 || df_caps[i].stacked)
            continue;
        df_caps[i].stacked = true;
        slen += scnprintf(sbuf + slen, sizeof(sbuf) - slen,
                          "STACK %s t=+%lld:", df_caps[i].name, t_s);
        for (k = 0; k < df_caps[i].nr; k++)
            slen += scnprintf(sbuf + slen, sizeof(sbuf) - slen,
                              " %pS", (void *)df_caps[i].stack[k]);
        slen += scnprintf(sbuf + slen, sizeof(sbuf) - slen, "\n");
        df_live_write(sbuf);
    }

    if (!df_live_stop && df_live_ticks < DF_LIVE_MAX_TICKS)
        schedule_delayed_work(&df_live_work,
                              msecs_to_jiffies(DF_LIVE_INTERVAL_MS));
}

static void df_live_start(void)
{
    unsigned int i;

    /* Arm the differential canary next to the __alloc_skb capture probe. */
    for (i = 0; i < DF_CAP_N; i++) {
        if (df_caps[i].state == 1 && !strcmp(df_caps[i].name, "__alloc_skb")) {
            memset(&df_skb_canary, 0, sizeof(df_skb_canary));
            df_skb_canary.addr = (kprobe_opcode_t *)df_caps[i].addr;
            df_skb_canary.pre_handler = df_canary_pre_handler;
            df_skb_canary_ok = register_kprobe(&df_skb_canary) == 0;
            if (!df_skb_canary_ok)
                pr_warn("dfroot: skb canary refused\n");
            break;
        }
    }

    df_live_t0_ns = ktime_get_boottime();
    INIT_DELAYED_WORK(&df_live_work, df_live_tick);
    schedule_delayed_work(&df_live_work, msecs_to_jiffies(DF_LIVE_INTERVAL_MS));

    df_live_misc_ok = misc_register(&df_live_dev) == 0;
    if (!df_live_misc_ok)
        pr_warn("dfroot: misc dfm2 registration failed\n");
}

static int __init df_audit_run(kallsyms_lookup_name_t get_addr)
{
    static char line[1024];
    static char hits[1024];
    int len = 0, hlen = 0;
    unsigned int i, hit = 0, shorted = 0, primary = 0;

    /* Closed-loop self-test. _printk is exported and this function is about to
     * call the kernel's own printk path many times, so if the probe mechanism
     * works at all this counter must be non-zero. It separates "my probes do
     * not fire" (mechanism/framework problem, no target selection can fix it)
     * from "my probes fire but the guard does not call these functions". */
    df_selftest.addr = (void *)get_addr("_printk");
    if (df_selftest.addr) {
        memset(&df_selftest.kp, 0, sizeof(df_selftest.kp));
        df_selftest.kp.addr = (kprobe_opcode_t *)df_selftest.addr;
        df_selftest.kp.pre_handler = df_selftest_pre_handler;
        df_selftest.state = register_kprobe(&df_selftest.kp) < 0 ? -2 : 1;
    } else {
        df_selftest.state = -1;
    }

    /* Symbolise stacks at report time; stack_trace_save is what lets us name the
     * caller that actually emitted the event. */
    df_stack_save = (stack_trace_save_t)get_addr("stack_trace_save");

    for (i = 0; i < DF_CAP_N; i++) {
        df_caps[i].addr = (void *)get_addr(df_caps[i].name);
        if (!df_caps[i].addr) {
            df_caps[i].state = -1;
            continue;
        }
        memset(&df_caps[i].kp, 0, sizeof(df_caps[i].kp));
        df_caps[i].kp.addr = (kprobe_opcode_t *)df_caps[i].addr;
        df_caps[i].kp.pre_handler = df_cap_pre_handler;
        df_caps[i].state = register_kprobe(&df_caps[i].kp) < 0 ? -2 : 1;
    }

    for (i = 0; i < DF_AUDIT_N; i++)
        if (df_audits[i].flags & DF_CLASS_PRIMARY)
            primary++;

    len += scnprintf(line + len, sizeof(line) - len,
                     "ARMED mode=%s", df_hook_enforce ? "enforce" : "audit");

    for (i = 0; i < DF_AUDIT_N; i++) {
        struct df_audit *a = &df_audits[i];
        int rc;

        a->addr = (void *)get_addr(a->name);
        if (!a->addr) {
            a->state = -1;
            pr_info("dfroot: %s = MISSING\n", a->name);
            continue;
        }

        memset(&a->kp, 0, sizeof(a->kp));
        a->kp.addr = (kprobe_opcode_t *)a->addr;
        if (df_hook_enforce && (a->flags & DF_CLASS_PRIMARY)) {
            a->kp.pre_handler = df_short_pre_handler;
            shorted++;
        } else {
            a->kp.pre_handler = df_count_pre_handler;
        }

        rc = register_kprobe(&a->kp);
        if (rc < 0) {
            a->state = -2;
            pr_warn("dfroot: %s = REFUSED by register_kprobe (%d)\n", a->name, rc);
        } else {
            a->state = 1;
            hit++;
            pr_info("dfroot: %s = ARMED (%s, %s)\n", a->name,
                    (a->flags & DF_CLASS_EGRESS) ? "egress" : "decision",
                    a->kp.pre_handler ? "short-circuit" : "observe-only");
        }
    }

    /* Report one letter per target, in table order. */
    for (i = 0; i < DF_AUDIT_N; i++) {
        struct df_audit *a = &df_audits[i];

        len += scnprintf(line + len, sizeof(line) - len, " %s=", a->name);
        switch (a->state) {
        case 1:  len += scnprintf(line + len, sizeof(line) - len, "M"); break;
        case -1: len += scnprintf(line + len, sizeof(line) - len, "N"); break;
        case -2: len += scnprintf(line + len, sizeof(line) - len, "R"); break;
        default: len += scnprintf(line + len, sizeof(line) - len, "?"); break;
        }
    }
    len += scnprintf(line + len, sizeof(line) - len,
                     " total=%u/%u shorted=%u/%u\n",
                     hit, (unsigned int)DF_AUDIT_N, shorted, primary);

    /* Second line: entries into each probe's handler, for every target, plus the
     * kernel's own nmissed counter read reflectively out of our struct kprobe
     * (unsigned long at +32 on this kernel). A target with hits=0 is simply not
     * on the alert path; nmissed>0 means the kernel hit the probe but could not
     * run the handler. */
    hlen += scnprintf(hits + hlen, sizeof(hits) - hlen,
                      "HITS total=%u", (unsigned int)DF_AUDIT_N);
    /* The self-test counter goes first: it is the only number that says whether
     * the probe framework invoked any handler in this module at all. */
    hlen += scnprintf(hits + hlen, sizeof(hits) - hlen, " SELFTEST_%s=%u(st=%d)",
                      df_selftest.name, df_selftest.hits, df_selftest.state);
    for (i = 0; i < DF_AUDIT_N; i++) {
        unsigned long missed = 0;
        void *np = (char *)&df_audits[i].kp + 32;

        if (df_audits[i].state == 1)
            memcpy(&missed, np, sizeof(missed));
        hlen += scnprintf(hits + hlen, sizeof(hits) - hlen, " %s=%u/%lu",
                          df_audits[i].name, df_audits[i].hits, missed);
    }
    hlen += scnprintf(hits + hlen, sizeof(hits) - hlen, "\n");

    /* Third line: the decisive trace. For each capture probe, its hit count and
     * the raw kernel addresses of the stack at the moment it fired, so the
     * reporter can be identified offline against /proc/kallsyms. */
    {
        static char cap[3072];
        int clen = 0;

        clen += scnprintf(cap + clen, sizeof(cap) - clen, "TRACE");
        for (i = 0; i < DF_CAP_N; i++) {
            unsigned int k;

            clen += scnprintf(cap + clen, sizeof(cap) - clen,
                              " %s(st=%d,hits=%u)", df_caps[i].name,
                              df_caps[i].state, df_caps[i].hits);
            for (k = 0; k < df_caps[i].nr && clen < (int)sizeof(cap) - 32; k++)
                clen += scnprintf(cap + clen, sizeof(cap) - clen, " %#lx",
                                  df_caps[i].stack[k]);
        }
        clen += scnprintf(cap + clen, sizeof(cap) - clen, "\n");

        /* One report, one write: three separate writes corrupted each other. */
        {
            static char whole[5120];
            int wlen = 0;

            wlen += scnprintf(whole + wlen, sizeof(whole) - wlen, "%s", line);
            wlen += scnprintf(whole + wlen, sizeof(whole) - wlen, "%s", hits);
            wlen += scnprintf(whole + wlen, sizeof(whole) - wlen, "%s", cap);
            df_audit_write(whole);
        }
        pr_info("dfroot: audit %s", line);
        pr_info("dfroot: %s", hits);
        pr_info("dfroot: %s", cap);
    }
    pr_info("dfroot: audit %s", line);
    pr_info("dfroot: %s", hits);

    df_audit_ok = hit > 0;
    return df_audit_ok ? 0 : -ENOENT;
}

static void __exit df_audit_stop(void)
{
    unsigned int i;

    if (df_selftest.state == 1) {
        unregister_kprobe(&df_selftest.kp);
        df_selftest.state = 0;
    }
    for (i = 0; i < DF_CAP_N; i++) {
        if (df_caps[i].state == 1) {
            unregister_kprobe(&df_caps[i].kp);
            df_caps[i].state = 0;
        }
    }
    for (i = 0; i < DF_AUDIT_N; i++) {
        struct df_audit *a = &df_audits[i];

        if (a->state == 1) {
            unregister_kprobe(&a->kp);
            a->state = 0;
        }
    }
}

static int __nocfi __init dfroot_init(void)
{
    kallsyms_lookup_name_t get_addr;
    kern_path_t  kern_path_fn;
    invalidate_t invalidate_fn;
    path_put_t   path_put_fn;
    struct path  p;
    umh_setup_t umh_setup;
    umh_exec_t  umh_exec;
    bool *selinux_state;
    struct kprobe kln_kp;
    void *info;
    int ret;

    // UMH command to run
    static const char sh[] = "/system/bin/sh";
    static char *envp[] = { "PATH=/system/bin", NULL };
    static char *argv[] = { (char *)sh, "-c",
        "touch /dev/dfm0",
        NULL };

    // Symbol finder
    kln_kp = (struct kprobe){ .symbol_name = "kallsyms_lookup_name" };
    if (register_kprobe(&kln_kp) < 0) {
        pr_err("dfroot: kallsyms_lookup_name not found\n");
        return -EINVAL;
    }
    get_addr = (kallsyms_lookup_name_t)kln_kp.addr;
    unregister_kprobe(&kln_kp);

    // Resolve the file helpers used to publish the anti-root probe report.
    df_filp_open    = (filp_open_t)   get_addr("filp_open");
    df_kernel_write = (kernel_write_t)get_addr("kernel_write");
    df_enforce_probe();

    // Invalidate page_cache for crash_dump64
    // NOTE: this can cause issues if a process is currently executing
    //   crash_dump64. We may want to revert to manual restore patching
    kern_path_fn  = (kern_path_t) get_addr("kern_path");
    invalidate_fn = (invalidate_t)get_addr("invalidate_inode_pages2");
    path_put_fn   = (path_put_t)  get_addr("path_put");
    if (!kern_path_fn || !invalidate_fn || !path_put_fn) {
        pr_err("dfroot: cache drop symbols missing\n");
    } else if (kern_path_fn("/apex/com.android.runtime/bin/crash_dump64",
                            LOOKUP_FOLLOW, &p)) {
        pr_err("dfroot: kern_path failed for crash_dump64\n");
    } else {
        invalidate_fn(p.dentry->d_inode->i_mapping);
        path_put_fn(&p);
        pr_info("dfroot: cleared page cache for crash_dump64\n");
    }

    // Disable SELinux
    selinux_state = (bool *)get_addr("selinux_state");
    if (!selinux_state) {
        pr_err("dfroot: selinux_state not found\n");
        return -EINVAL;
    }
    WRITE_ONCE(*selinux_state, false);
    pr_info("dfroot: selinux_state permissive\n");

    // Samsung
    defex_enforce_kp = (struct kprobe){ .addr = (kprobe_opcode_t *)get_addr("task_defex_enforce"),
                                .pre_handler = null_pre_handler };
    defex_enforce_ok = register_kprobe(&defex_enforce_kp) == 0;
    if (!defex_enforce_ok)
        pr_err("dfroot: task_defex_enforce not in this kernel, skipping\n");
    else
        pr_info("dfroot: task_defex_enforce hooked\n");
    
    defex_umh_kp = (struct kprobe){ .addr = (kprobe_opcode_t *)get_addr("task_defex_user_exec"),
                              .pre_handler = null_pre_handler };
    defex_umh_ok = register_kprobe(&defex_umh_kp) == 0;
    if (!defex_umh_ok)
        pr_err("dfroot: task_defex_user_exec not in this kernel, skipping\n");
    else
        pr_info("dfroot: task_defex_user_exec hooked\n");

    // OPD2515: audit (and optionally short-circuit) the OPPO anti-root guard.
    // This must happen before the usermode helper runs, because the helper's
    // credential change is what the guard reacts to.
    df_audit_run(get_addr);
    if (!df_audit_ok)
        pr_warn("dfroot: no anti-root guard target resolved; continuing anyway\n");

    // Live counters on /dev/dfm1: the gate report above is a frozen init-time
    // snapshot, so post-arming probe behaviour is only observable here.
    df_live_start();

    // Run UMH command
    umh_setup = (umh_setup_t)get_addr("call_usermodehelper_setup");
    umh_exec  = (umh_exec_t)get_addr("call_usermodehelper_exec");
    if (!umh_setup || !umh_exec) {
        pr_err("dfroot: usermodehelper symbols missing (setup=%px exec=%px)\n",
               umh_setup, umh_exec);
        return 0;
    }

    info = umh_setup(sh, argv, envp, GFP_KERNEL, NULL, NULL, NULL);
    if (!info) {
        pr_err("dfroot: usermodehelper_setup: returned NULL\n");
        return 0;
    }
    // bypass CONFIG_STATIC_USERMODEHELPER_PATH="" overriding path to ""
    ((struct subprocess_info *)info)->path = sh;

    ret = umh_exec(info, UMH_WAIT_PROC);
    pr_info("dfroot: usermodehelper_exec returned %d\n", ret);
    
    return 0;
}

static void __exit dfroot_exit(void)
{
    df_live_stop = true;
    cancel_delayed_work_sync(&df_live_work);
    if (df_live_misc_ok)
        misc_deregister(&df_live_dev);
    if (df_skb_canary_ok)
        unregister_kprobe(&df_skb_canary);
    if (defex_enforce_ok) unregister_kprobe(&defex_enforce_kp);
    if (defex_umh_ok)     unregister_kprobe(&defex_umh_kp);
    df_audit_stop();
}

module_init(dfroot_init);
module_exit(dfroot_exit);
