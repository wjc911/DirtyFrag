#include <dirent.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#define BLKROSET   0x125d
#define KSUD_STAGE "/data/user_de/0/df.root/ksud"
#define KSUD       "/data/adb/ksud"
#define PREFS_PATH "/data/user_de/0/df.root/shared_prefs/dfroot.xml"
#define MODULES_DIR "/data/adb/modules"
/* Anti-root probe report, written by dfroot.ko during module_init, i.e. before
 * this helper is exec'd. Format:
 *   ARMED mode=<audit|enforce> <sym>=<M|N|R> ... total=<hit>/<n> */
#define AUDIT_PATH "/dev/dfm0"

static int pref_true(const char *buf, const char *key)
{
    char needle[64];
    snprintf(needle, sizeof(needle), "name=\"%s\"", key);
    char *p = strstr(buf, needle);
    if (!p) return 0;
    char *tag_end = strchr(p, '>');
    char *v = strstr(p, "value=\"true\"");
    return v && tag_end && v < tag_end;
}

static int read_prefs(char *su_manager, size_t su_manager_size, int *soft_reboot,
                      int *disable_modules)
{
    int fd = open(PREFS_PATH, O_RDONLY);
    if (fd < 0) return -1;

    char buf[4096];
    int n = read(fd, buf, sizeof(buf) - 1);
    close(fd);
    if (n <= 0) return -1;
    buf[n] = '\0';

    char *p = strstr(buf, "name=\"su_manager\">");
    if (!p) return -1;
    p += strlen("name=\"su_manager\">");
    char *end = strchr(p, '<');
    if (!end) return -1;
    size_t len = end - p;
    if (len == 0 || len >= su_manager_size) return -1;
    memcpy(su_manager, p, len);
    su_manager[len] = '\0';

    *soft_reboot = pref_true(buf, "soft_reboot");
    *disable_modules = pref_true(buf, "disable_modules");

    return 0;
}

/* Set when late_load_allowed() approves an enforce-mode run: the module must
 * then stay loaded, because the short-circuit probes live in it. */
static int late_load_resident;

/* Read the anti-root probe report. Returns bytes read, or -1 if unavailable. */
static int read_audit(char *out, size_t out_size)
{
    int fd = open(AUDIT_PATH, O_RDONLY);
    if (fd < 0) return -1;

    int n = read(fd, out, out_size - 1);
    close(fd);
    if (n <= 0) return -1;
    out[n] = '\0';
    return n;
}

/* Count occurrences of the two-byte suffix "=M" (target present and probed). */
static int count_armed(const char *buf)
{
    int n = 0;
    for (const char *p = buf; (p = strstr(p, "=M")) != NULL; p += 2)
        n++;
    return n;
}

/* Decide whether KernelSU may be late-loaded.
 *
 * In the default "audit" mode the module only *reports* which guard symbols it
 * could hook; nothing is short-circuited, so a run that proceeds would still
 * raise the OPPO anti-root alert. Refuse to late-load in that case: an
 * audit-only run must produce evidence, not a root+alert combination.
 *
 * In "enforce" mode require every reported target to be armed, so a partially
 * hooked run fails closed instead of half-suppressing the alert.
 *
 * Returns 1 to proceed, 0 to refuse. *reason is set for logging. */
static int late_load_allowed(const char **reason)
{
    static char buf[2048];
    int n = read_audit(buf, sizeof(buf));

    if (n < 0) {
        *reason = "no anti-root probe report";
        return 0;
    }

    char *mode = strstr(buf, "mode=");
    if (!mode) {
        *reason = "malformed anti-root probe report";
        return 0;
    }

    int total = 0, hit = 0;
    char *tp = strstr(buf, "total=");
    if (tp)
        sscanf(tp + 6, "%d/%d", &hit, &total);

    if (!strncmp(mode + 5, "audit", 5)) {
        *reason = "audit-only build: probes observed, nothing suppressed";
        return 0;
    }

    if (!strncmp(mode + 5, "enforce", 7)) {
        if (total <= 0 || count_armed(buf) != total || hit != total) {
            *reason = "enforce build but not every target armed";
            return 0;
        }
        *reason = "enforce build, all targets armed";
        /* Report resident module: the short-circuit probes live in dfroot.ko and
         * must stay registered for as long as the root session exists, so the
         * caller must not unload the module after a successful late-load. */
        late_load_resident = 1;
        return 1;
    }

    *reason = "unknown anti-root probe mode";
    return 0;
}

static int adopt_zygote_env(void)
{
    FILE *f = popen("pidof zygote64 zygote", "r");
    if (!f) return -1;
    int pid = 0;
    fscanf(f, "%d", &pid);
    pclose(f);
    if (!pid) return -1;

    char path[32];
    snprintf(path, sizeof(path), "/proc/%d/environ", pid);
    int fd = open(path, O_RDONLY);
    if (fd < 0) return -1;
    static char buf[16384];
    int n = read(fd, buf, sizeof(buf) - 1);
    close(fd);
    if (n <= 0) return -1;
    buf[n] = '\0';
    for (char *p = buf, *end = buf + n; p < end; p += strlen(p) + 1)
        putenv(p);
    return 0;
}

static int should_ro(const char *name)
{
    size_t len = strlen(name);
    if (!strcmp(name, "super"))  return 1;
    if (!strcmp(name, "misc"))   return 1;
    if (!strcmp(name, "steady")) return 1;
    if (len >= 2 && name[len - 2] == '_' &&
        (name[len - 1] == 'a' || name[len - 1] == 'b'))
        return 1;
    return 0;
}

static int set_partitions_ro(void)
{
    DIR *dir = opendir("/dev/block/by-name");
    if (!dir)
        return -1;

    struct dirent *ent;
    while ((ent = readdir(dir))) {
        if (!should_ro(ent->d_name))
            continue;

        char path[128];
        snprintf(path, sizeof(path), "/dev/block/by-name/%s", ent->d_name);

        int fd = open(path, O_RDONLY);
        if (fd < 0)
            continue;

        struct stat st;
        if (fstat(fd, &st) == 0 && S_ISBLK(st.st_mode)) {
            int on = 1;
            ioctl(fd, BLKROSET, &on);
        }
        close(fd);
    }

    closedir(dir);
    return 0;
}

static int late_load_running(void)
{
    DIR *d = opendir("/proc");
    if (!d)
        return 0;
    struct dirent *e;
    char path[64], buf[256];
    int found = 0;
    while ((e = readdir(d)) != NULL) {
        char *end;
        strtol(e->d_name, &end, 10);
        if (*end) continue;
        snprintf(path, sizeof(path), "/proc/%s/cmdline", e->d_name);
        int fd = open(path, O_RDONLY | O_CLOEXEC);
        if (fd < 0) continue;
        int n = read(fd, buf, sizeof(buf) - 1);
        close(fd);
        if (n <= 0) continue;
        buf[n] = '\0';
        for (int i = 0; i < n; i++)
            if (!buf[i]) buf[i] = ' ';
        if (strstr(buf, "ksud") && strstr(buf, "late-load")) {
            found = 1;
            break;
        }
    }
    closedir(d);
    return found;
}

static int run_ctx(const char *ctx, char *const argv[])
{
    pid_t pid = fork();
    if (pid < 0)
        return -1;
    if (pid == 0) {
        if (ctx) {
            int fd = open("/proc/self/attr/exec", O_WRONLY);
            if (fd >= 0) { write(fd, ctx, strlen(ctx)); close(fd); }
        }
        execv(argv[0], argv);
        _exit(127);
    }
    int status;
    waitpid(pid, &status, 0);
    return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
}

static void touch(const char *path)
{
    int fd = open(path, O_CREAT | O_WRONLY, 0666);
    if (fd >= 0)
        close(fd);
}

/* Mark every installed module disabled before ksud runs. A broken module
 * otherwise loads on the next boot and bootloops the device. */
static int disable_modules(void)
{
    DIR *dir = opendir(MODULES_DIR);
    if (!dir)
        return -1;

    struct dirent *ent;
    while ((ent = readdir(dir))) {
        if (ent->d_name[0] == '.')
            continue;
        char path[256];
        snprintf(path, sizeof(path), MODULES_DIR "/%s/disable", ent->d_name);
        touch(path);
    }
    closedir(dir);
    return 0;
}

int main(void)
{
    touch("/dev/dfm1");
    char su_manager[256];
    int soft_reboot, disable_mods;
    const char *gate_reason = NULL;
    if (read_prefs(su_manager, sizeof(su_manager), &soft_reboot, &disable_mods) != 0) {
        touch("/dev/dfme0");
        return 1;
    }

    touch("/dev/dfm2");
    if (adopt_zygote_env())
        touch("/dev/dfmw0");

    touch("/dev/dfm3");
    if (set_partitions_ro())
        touch("/dev/dfmw1");

    if (disable_mods) {
        touch("/dev/dfm4");
        if (disable_modules()) {
            touch("/dev/dfme1");
            return 1;
        }
    }

    /* Anti-root gate (see late_load_allowed). Refuse to establish root when the
     * probes are audit-only or only partially armed, so a run cannot produce the
     * root-plus-alert combination the project is trying to eliminate. */
    if (!late_load_allowed(&gate_reason)) {
        touch("/dev/dfmg0");
        /* Device-protected app dir: readable by the app UID, unlike
         * /data/local/tmp (shell_data_file) or /dev (0600, root). */
        FILE *lg = fopen("/data/user_de/0/df.root/files/dfroot-gate.txt", "w");
        if (lg) {
            fprintf(lg, "late-load refused: %s\n", gate_reason);
            fclose(lg);
        }
        run_ctx(NULL, (char *[]){ "/system/bin/rmmod", "dfroot", NULL });
        return 1;
    }

    touch("/dev/dfm5");
    if (run_ctx(NULL, (char *[]){ KSUD_STAGE, "late-load", "--package-name", su_manager, NULL }) == 0) {
        touch("/dev/dfm6");
        if (soft_reboot) {
            while (late_load_running()) sleep(1);
            run_ctx("u:r:ksu:s0", (char *[]){ KSUD, "soft-reboot", NULL });
        }
    } else {
        touch("/dev/dfme2");
    }

    /* Keep the module resident when its probes are what suppresses the alert. */
    if (!late_load_resident)
        run_ctx(NULL, (char *[]){ "/system/bin/rmmod", "dfroot", NULL });
    return 0;
}
