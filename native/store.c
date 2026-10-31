/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The host's side of the article store; see store.h. Options:
 *   --spool DIR          the store's directory; without it there is no store and no client may post
 *   --run-dir DIR        where the mark of a failed sync is copied, on a file system the boot clears
 *   --path-identity ID   the server's path identity, handed to the program, which checks it
 *   --group NAME         a group the server carries, as often as there are groups
 *   --post-from NET      a network allowed to post, as an address with a prefix length; by default
 *                        127.0.0.0/8 and ::1/128 */
#define _GNU_SOURCE
#include "store.h"
#include "dn_session_layout.h"
#include "faults.h"
#include "host.h"
#include <arpa/inet.h>
#include <fcntl.h>
#include <inttypes.h>
#include <netinet/in.h>
#include <poll.h>
#include <pthread.h>
#include <sys/file.h>
#include <sys/random.h>
#include <time.h>
#include <unistd.h>

enum { NETS = 16, BOOT_ID = 36 };

/* The mark a failed sync leaves: the boot it happened in. A name of no shape the store gives, so a
 * start never takes it for an article. */
static const char MARK[] = "sync-failed";

struct net { sa_family_t family; unsigned char addr[16]; unsigned bits; };

static const char *spool_path, *run_path, *identity, *groups[DN_SESSION_GROUPS_MAX];
static size_t group_count;
static struct net nets[NETS];
static const char *net_texts[NETS];
static size_t net_count;
static int logins, spool = -1, run = -1;
static char boot[BOOT_ID + 1];
static unsigned char random_octets[DN_SESSION_RANDOM_LEN];
static pthread_mutex_t marking = PTHREAD_MUTEX_INITIALIZER;

static void add_net(const char *at, const char *text) {
    if (net_count == NETS) dn_harness("%s--post-from: more than %d networks", at, NETS);
    char address[INET6_ADDRSTRLEN];
    const char *slash = strchr(text, '/');
    size_t n = slash ? (size_t)(slash - text) : strlen(text);
    if (n >= sizeof address) dn_harness("%s--post-from: not a network: %s", at, text);
    memcpy(address, text, n);
    address[n] = 0;
    net_texts[net_count] = text;
    struct net *net = &nets[net_count++];
    if (inet_pton(AF_INET, address, net->addr) == 1) net->family = AF_INET;
    else if (inet_pton(AF_INET6, address, net->addr) == 1) net->family = AF_INET6;
    else dn_harness("%s--post-from: not a network: %s", at, text);
    unsigned long most = net->family == AF_INET ? 32 : 128, bits = most;
    if (slash) {
        char *end;
        errno = 0;
        bits = strtoul(slash + 1, &end, 10);
        if (slash[1] < '0' || slash[1] > '9' || errno || *end || bits > most)
            dn_harness("%s--post-from: not a network: %s", at, text);
    }
    net->bits = (unsigned)bits;
}

int dn_store_option(const char *at, const char *name, const char *value) {
    if (!strcmp(name, "--spool")) spool_path = value;
    else if (!strcmp(name, "--run-dir")) run_path = value;
    else if (!strcmp(name, "--path-identity")) identity = value;
    else if (!strcmp(name, "--post-from")) add_net(at, value);
    else if (!strcmp(name, "--group")) {
        if (group_count == DN_SESSION_GROUPS_MAX)
            dn_harness("%s--group: more than %d groups", at, DN_SESSION_GROUPS_MAX);
        groups[group_count++] = value;
    } else return 0;
    return 1;
}

void dn_store_logins(void) {
    logins = 1;
}

__attribute__((noreturn, format(printf, 1, 2))) static void refuse(const char *format, ...) {
    va_list args;
    va_start(args, format);
    dn_end(4, format, args);
}

static void boot_id(char id[static BOOT_ID + 1]) {
    int fd = open("/proc/sys/kernel/random/boot_id", O_RDONLY | O_CLOEXEC);
    if (fd < 0) dn_harness("boot_id: %s", strerror(errno));
    ssize_t n = read(fd, id, BOOT_ID);
    close(fd);
    if (n != BOOT_ID) dn_harness("boot_id: %zd bytes", n);
    id[BOOT_ID] = 0;
}

/* A mark in `dir`: only a whole one of another boot is removed; one of this boot, or one that cannot
 * be read whole, refuses the start. */
static void check_mark(int dir, const char *where, const char *id) {
    int fd = openat(dir, MARK, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) {
        if (errno == ENOENT) return;
        dn_harness("%s/%s: %s", where, MARK, strerror(errno));
    }
    char seen[BOOT_ID + 1] = {0};
    ssize_t n = read(fd, seen, BOOT_ID);
    close(fd);
    if (n != BOOT_ID)
        refuse("%s/%s: a mark that cannot be read whole; once the machine has restarted, remove it", where, MARK);
    if (!memcmp(seen, id, BOOT_ID))
        refuse("%s/%s: a sync failed since the machine started; restart it, or repair the store", where, MARK);
    if (unlinkat(dir, MARK, 0) && errno != ENOENT) dn_harness("%s/%s: %s", where, MARK, strerror(errno));
}

static int open_dir(const char *path) {
    int fd = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (fd < 0) dn_harness("%s: %s", path, strerror(errno));
    return fd;
}

/* The settings together; 0 without a store. */
static int validated(void) {
    if (!spool_path) {
        if (run_path || identity || group_count || net_count) dn_harness("store options without --spool");
        return 0;
    }
    if (!run_path) dn_harness("--spool needs --run-dir");
    if (identity && strlen(identity) > DN_SESSION_IDENTITY_MAX)
        dn_harness("--path-identity: more than %d bytes", DN_SESSION_IDENTITY_MAX);
    for (size_t g = 0; g < group_count; ++g)
        if (!*groups[g] || strlen(groups[g]) > DN_SESSION_GROUP_MAX)
            dn_harness("--group: 1 to %d bytes: %s", DN_SESSION_GROUP_MAX, groups[g]);
    if (!net_count && !logins) {
        add_net("", "127.0.0.0/8");
        add_net("", "::1/128");
    }
    return 1;
}

void dn_store_check(void) {
    if (validated()) {
        close(open_dir(spool_path));
        close(open_dir(run_path));
    }
}

void dn_store_settings(FILE *out) {
    fputs(",\"spool\":", out);
    if (spool_path) dn_json_string(out, spool_path);
    else fputs("null", out);
    fputs(",\"run_dir\":", out);
    if (run_path) dn_json_string(out, run_path);
    else fputs("null", out);
    fputs(",\"path_identity\":", out);
    if (identity) dn_json_string(out, identity);
    else fputs("null", out);
    fputs(",\"groups\":[", out);
    for (size_t g = 0; g < group_count; ++g) {
        if (g) fputc(',', out);
        dn_json_string(out, groups[g]);
    }
    fputs("],\"post_from\":[", out);
    for (size_t k = 0; spool_path && k < net_count; ++k) {
        if (k) fputc(',', out);
        dn_json_string(out, net_texts[k]);
    }
    fputc(']', out);
}

void dn_store_start(void) {
    if (!validated()) return;
    spool = open_dir(spool_path);
    if (flock(spool, LOCK_EX | LOCK_NB)) {
        if (errno == EWOULDBLOCK) refuse("%s: another process holds the spool", spool_path);
        dn_harness("flock %s: %s", spool_path, strerror(errno));
    }
    boot_id(boot);
    check_mark(spool, spool_path, boot);
    run = open_dir(run_path);
    check_mark(run, run_path, boot);
    for (size_t got = 0; got < sizeof random_octets;) {
        ssize_t n = getrandom(random_octets + got, sizeof random_octets - got, 0);
        if (n < 0 && errno != EINTR) dn_harness("getrandom: %s", strerror(errno));
        if (n > 0) got += (size_t)n;
    }
}

void dn_store_fill(unsigned char *next) {
    struct timespec t;
    if (clock_gettime(CLOCK_REALTIME, &t)) dn_harness("clock_gettime: %s", strerror(errno));
    dn_put_word(next + DN_SESSION_NEXT_STORE, spool >= 0);
    dn_put_word(next + DN_SESSION_NEXT_WALL, (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_nsec / 1000000);
    memcpy(next + DN_SESSION_NEXT_RANDOM, random_octets, sizeof random_octets);
    size_t n = identity ? strlen(identity) : 0;
    dn_put_word(next + DN_SESSION_NEXT_IDENTITY_LEN, n);
    memcpy(next + DN_SESSION_NEXT_IDENTITY, identity ? identity : "", n);
    dn_put_word(next + DN_SESSION_NEXT_GROUP_COUNT, group_count);
    for (size_t g = 0; g < group_count; ++g) {
        unsigned char *slot = next + DN_SESSION_NEXT_GROUPS + g * DN_SESSION_GROUP_SLOT;
        size_t len = strlen(groups[g]);
        dn_put_word(slot, len);
        memcpy(slot + 8, groups[g], len);
    }
}

int dn_store_spool(void) { return spool; }

/* Octets of recovery's area, in hexadecimal; they have to lie in it. */
static void print_hex(const unsigned char *rec, uint64_t at, uint64_t n) {
    if (n > DN_SESSION_REC_AREA || at > DN_SESSION_REC_AREA - n)
        dn_violation("recovery names octets outside its area");
    for (uint64_t i = 0; i < n; ++i) fprintf(stderr, "%02x", rec[at + i]);
}

static const char *const corrupt_why[] = {"short", "too-long", "unterminated", "tag", "not-a-record", "format-again"};

void dn_store_recovery_stopped(uint64_t stop, const unsigned char *rec, uint64_t job_class) {
    if (stop == DN_SESSION_RECOVERY_FAILED)
        refuse("recovery failed: a file job failed, class %" PRIu64, job_class);
    uint64_t x = dn_word(rec + DN_SESSION_REC_FAULT_A), y = dn_word(rec + DN_SESSION_REC_FAULT_B);
    uint64_t at = dn_word(rec + DN_SESSION_REC_FAULT_AT), len = dn_word(rec + DN_SESSION_REC_FAULT_LEN);
    fprintf(stderr, "the store is refused: corrupt ");
    switch (dn_word(rec + DN_SESSION_REC_FAULT)) {
    case 1:
        fprintf(stderr, "bad-name ");
        print_hex(rec, DN_SESSION_REC_NAME, dn_word(rec + DN_SESSION_REC_NAME_LEN));
        break;
    case 2: fprintf(stderr, "no-journal"); break;
    case 3:
        if (y - 1 >= sizeof corrupt_why / sizeof *corrupt_why)
            dn_violation("a journal corrupt for reason %" PRIu64, y);
        fprintf(stderr, "journal %" PRIu64 " %s", x, corrupt_why[y - 1]);
        break;
    case 4: fprintf(stderr, "seq-twice %" PRIu64, x); break;
    case 5:
        fprintf(stderr, "number-not-above ");
        print_hex(rec, at, len);
        fprintf(stderr, " %" PRIu64, x);
        break;
    case 6:
        fprintf(stderr, "unknown-group ");
        print_hex(rec, at, len);
        break;
    case 7: fprintf(stderr, "missing-file %" PRIu64, x); break;
    case 8: fprintf(stderr, "wrong-size %" PRIu64, x); break;
    case 9: fprintf(stderr, "exhausted"); break;
    case 11: fprintf(stderr, "too-many %" PRIu64, x); break;
    case 12:
        fprintf(stderr, "id-twice ");
        print_hex(rec, at, len);
        break;
    default: dn_violation("recovery refused the store for reason %" PRIu64, dn_word(rec + DN_SESSION_REC_FAULT));
    }
    fprintf(stderr, "\n");
    exit(4);
}

/* The mark in `dir`, unless the test build fails it at `point`; whether it was left. */
static int leave_mark(int dir, const char *point) {
    if (DN_FAULT(point)) return 0;
    int fd = openat(dir, MARK, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC | O_NOFOLLOW, 0644);
    if (fd < 0) return 0;
    char line[BOOT_ID + 1];
    memcpy(line, boot, BOOT_ID);
    line[BOOT_ID] = '\n';
    ssize_t n;
    do n = write(fd, line, sizeof line);
    while (n < 0 && errno == EINTR);
    return !close(fd) && n == (ssize_t)sizeof line;
}

void dn_store_mark_failed(void) {
    pthread_mutex_lock(&marking);
    int left = leave_mark(spool, "dn/mark-spool") + leave_mark(run, "dn/mark-run");
    pthread_mutex_unlock(&marking);
    if (!left)
        dn_harness_now("a sync failed, and its mark could be left neither in %s nor in %s", spool_path, run_path);
}

int dn_store_may_post(const struct sockaddr_storage *peer) {
    if (spool < 0) return 0;
    const unsigned char *addr = peer->ss_family == AF_INET
                                    ? (const unsigned char *)&((const struct sockaddr_in *)peer)->sin_addr
                                    : (const unsigned char *)&((const struct sockaddr_in6 *)peer)->sin6_addr;
    for (size_t k = 0; k < net_count; ++k) {
        const struct net *net = &nets[k];
        if (net->family != peer->ss_family) continue;
        unsigned whole = net->bits / 8, rest = net->bits % 8;
        if (memcmp(addr, net->addr, whole)) continue;
        if (rest && ((addr[whole] ^ net->addr[whole]) & (0xffu << (8 - rest)) & 0xffu)) continue;
        return 1;
    }
    return 0;
}

void dn_store_log_opened(const struct sockaddr_storage *peer) {
    static uint64_t opened, unlogged;
    if (spool < 0) return;
    ++opened;
    uint64_t value = 0;
    for (size_t k = 0; k < DN_SESSION_RUN_VALUE_LEN; ++k) value = value << 8 | random_octets[k];
    int v4 = peer->ss_family == AF_INET;
    const struct sockaddr_in *a4 = (const struct sockaddr_in *)peer;
    const struct sockaddr_in6 *a6 = (const struct sockaddr_in6 *)peer;
    char text[INET6_ADDRSTRLEN];
    if (!inet_ntop(peer->ss_family, v4 ? (const void *)&a4->sin_addr : (const void *)&a6->sin6_addr, text,
                   sizeof text))
        strcpy(text, "?");
    char line[192];
    int n = unlogged ? snprintf(line, sizeof line, "connections not logged: %" PRIu64 "\n", unlogged) : 0;
    n += snprintf(line + n, sizeof line - (size_t)n, "connection %" PRIu64 ".%" PRIu64 " from %s port %u\n", value,
                  opened, text, (unsigned)ntohs(v4 ? a4->sin_port : a6->sin6_port));
    /* Only when stderr has room now, so that a reader that stalls never stops the server: a write
     * under PIPE_BUF then goes whole. */
    struct pollfd err = {.fd = STDERR_FILENO, .events = POLLOUT};
    if (poll(&err, 1, 0) == 1 && err.revents == POLLOUT && write(STDERR_FILENO, line, (size_t)n) == n)
        unlogged = 0;
    else
        ++unlogged;
}
