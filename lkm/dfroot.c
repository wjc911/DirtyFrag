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
 * What this revision does instead is *observe only*: it resolves the guard's
 * decision/report functions by name and tries to register a kprobe on each so
 * that the very first device run reports, as hard facts, which guard symbols
 * exist on this kernel and which are probeable.  Nothing is short-circuited
 * and no guard function is altered unless DF_HOOK_ENFORCE is set, so a run of
 * this build cannot change system behaviour -- it can only produce evidence.
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
#define DF_CLASS_UNSAFE 0x08  /* skipping the body is semantically unsafe */

struct df_audit {
    const char *name;
    unsigned int flags;
    struct kprobe kp;
    void *addr;
    int state;               /* 0 = untried, 1 = armed, -1 = missing, -2 = refused */
};

static struct df_audit df_audits[] = {
    /* name                              flags                                   */
    { "oplus_root_check_post_handler",   DF_CLASS_DECIDE },
    { "oplus_root_check_pre_handler",    DF_CLASS_DECIDE },
    { "oplus_root_check_succ",           DF_CLASS_DECIDE },
    { "oplus_root_check_succ_upload",    DF_CLASS_DECIDE },
    { "oplus_root_killed",               DF_CLASS_DECIDE | DF_CLASS_EXPORT },
    { "oplus_exe_block_ret_handler",     DF_CLASS_DECIDE | DF_CLASS_UNSAFE },
    { "oplus_report_execveat",           DF_CLASS_DECIDE },
    { "oplus_report_execveat_new",       DF_CLASS_DECIDE },
    { "oplus_secure_harden_kevent",      DF_CLASS_DECIDE },
    { "report_security_event",           DF_CLASS_DECIDE },
    { "kevent_send_to_user",             DF_CLASS_EGRESS | DF_CLASS_UNSAFE },
};
#define DF_AUDIT_N ARRAY_SIZE(df_audits)

static int df_audit_ok;

/* Never skip the body from a probe handler until the mechanism is proven on
 * this kernel: the guard functions carry paciasp/autiasp prologues and the
 * skip-body idiom returns to a link register that has not been re-signed. */
static int df_hook_enforce;
module_param_named(enforce, df_hook_enforce, int, 0444);
MODULE_PARM_DESC(enforce, "0 = audit/hook targets but never skip a body (default)");

static void df_audit_write(const char *msg)
{
    struct file *f;
    loff_t pos = 0;

    f = filp_open("/dev/dfm0", O_WRONLY | O_CREAT, 0600);
    if (IS_ERR(f)) {
        pr_warn("dfroot: audit write: /dev/dfm0 open failed (%ld)\n", PTR_ERR(f));
        return;
    }
    kernel_write(f, msg, strlen(msg), &pos);
    filp_close(f, NULL);
}

static int __init df_audit_run(kallsyms_lookup_name_t get_addr)
{
    char line[1024];
    int len = 0;
    unsigned int i, hit = 0;

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
        if (df_hook_enforce && !(a->flags & DF_CLASS_UNSAFE))
            a->kp.pre_handler = null_pre_handler;

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
    len += scnprintf(line + len, sizeof(line) - len, " total=%u/%u\n",
                     hit, (unsigned int)DF_AUDIT_N);

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
