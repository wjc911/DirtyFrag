#include <linux/init.h>
#include <linux/kernel.h>
#include <linux/kmod.h>
#include <linux/kprobes.h>
#include <linux/module.h>
#include <linux/namei.h>
#include <linux/ptrace.h>
#include <linux/fs.h>
#include <linux/file.h>
#include <linux/uaccess.h>

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
 * R (present, register_kprobe refused).  bootstrap.c reads this to decide
 * whether the run is allowed to proceed.
 */
#define DF_CLASS_DECIDE 0x01  /* root-check decision / report path        */
#define DF_CLASS_EGRESS 0x02  /* kernel -> userspace event egress         */
#define DF_CLASS_EXPORT 0x04  /* exported, but no caller inside the guard */
/* Short-circuit only the DF_CLASS_PRIMARY targets when enforce mode is on.
 *
 * Device evidence (OPD2515, audit build, logcat 22:38:35) fixed the target set:
 *   OPLUS_KEVENT_RECORD event_type=3
 *   payload:10051,path@@/data/app/.../lib/arm64/libdfroot.so
 * i.e. the alert that actually fires is driven by the /data execve path check
 * on our own native library, not by the app-UID root transition. So the primary
 * set spans both paths plus the single netlink egress:
 *   oplus_root_check_post_handler - UID path; its body continues into an
 *                                   inlined send_sig(9) and the kevent report
 *   report_security_event         - shared report primitive on the execve path
 *   oplus_secure_harden_kevent    - the report site observed firing above
 *   oplus_exe_block_ret_handler   - execve-path decision wrapper
 *   kevent_send_to_user           - netlink egress; skips the skb send itself
 *                                   (consumes the sk_buff, hence no re-entry risk
 *                                   from a return-value rewrite)
 * Two targets stay observe-only because their return semantics must not be
 * rewritten: oplus_heapspray_check and the is_unlocked getter.
 */
#define DF_CLASS_PRIMARY 0x10

struct df_audit {
    const char *name;
    unsigned int flags;
    struct kprobe kp;
    void *addr;
    int state;               /* 0 = untried, 1 = armed, -1 = missing, -2 = refused */
};

static struct df_audit df_audits[] = {
    /* name                              flags                                   */
    { "oplus_root_check_post_handler",   DF_CLASS_DECIDE | DF_CLASS_PRIMARY },
    { "oplus_root_check_pre_handler",    DF_CLASS_DECIDE },
    { "oplus_root_check_succ",           DF_CLASS_DECIDE },
    { "oplus_root_check_succ_upload",    DF_CLASS_DECIDE },
    { "oplus_root_killed",               DF_CLASS_DECIDE | DF_CLASS_EXPORT },
    { "oplus_exe_block_ret_handler",     DF_CLASS_DECIDE | DF_CLASS_PRIMARY },
    { "oplus_report_execveat",           DF_CLASS_DECIDE },
    { "oplus_report_execveat_new",       DF_CLASS_DECIDE },
    { "oplus_secure_harden_kevent",      DF_CLASS_DECIDE | DF_CLASS_PRIMARY },
    { "report_security_event",           DF_CLASS_DECIDE | DF_CLASS_PRIMARY },
    { "kevent_send_to_user",             DF_CLASS_EGRESS | DF_CLASS_PRIMARY },
};
#define DF_AUDIT_N ARRAY_SIZE(df_audits)

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
    f = df_filp_open("/dev/dfm0", O_WRONLY | O_CREAT, 0666);
    if (IS_ERR(f)) {
        pr_warn("dfroot: audit write: /dev/dfm0 open failed (%ld)\n", PTR_ERR(f));
        return;
    }
    df_kernel_write(f, msg, strlen(msg), &pos);
    filp_close(f, NULL);
}

static int __init df_audit_run(kallsyms_lookup_name_t get_addr)
{
    char line[1024];
    int len = 0;
    unsigned int i, hit = 0, shorted = 0, primary = 0;

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
            a->kp.pre_handler = null_pre_handler;
            shorted++;
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

    df_audit_write(line);
    pr_info("dfroot: audit %s", line);

    df_audit_ok = hit > 0;
    return df_audit_ok ? 0 : -ENOENT;
}

static void __exit df_audit_stop(void)
{
    unsigned int i;

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
    if (defex_enforce_ok) unregister_kprobe(&defex_enforce_kp);
    if (defex_umh_ok)     unregister_kprobe(&defex_umh_kp);
    df_audit_stop();
}

module_init(dfroot_init);
module_exit(dfroot_exit);
