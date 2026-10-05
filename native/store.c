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
#include "host.h"
#include <arpa/inet.h>
#include <fcntl.h>
#include <netinet/in.h>
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
static size_t net_count;
static int spool = -1;
static unsigned char random_octets[DN_SESSION_RANDOM_LEN];

static void add_net(const char *text) {
    if (net_count == NETS) dn_harness("--post-from: more than %d networks", NETS);
    char address[INET6_ADDRSTRLEN];
    const char *slash = strchr(text, '/');
    size_t n = slash ? (size_t)(slash - text) : strlen(text);
    if (n >= sizeof address) dn_harness("--post-from: not a network: %s", text);
    memcpy(address, text, n);
    address[n] = 0;
    struct net *net = &nets[net_count++];
    if (inet_pton(AF_INET, address, net->addr) == 1) net->family = AF_INET;
    else if (inet_pton(AF_INET6, address, net->addr) == 1) net->family = AF_INET6;
    else dn_harness("--post-from: not a network: %s", text);
    unsigned most = net->family == AF_INET ? 32 : 128;
    net->bits = slash ? (unsigned)dn_parse_u64(slash + 1, most) : most;
}

int dn_store_option(const char *name, const char *value) {
    if (!strcmp(name, "--spool")) spool_path = value;
    else if (!strcmp(name, "--run-dir")) run_path = value;
    else if (!strcmp(name, "--path-identity")) identity = value;
    else if (!strcmp(name, "--post-from")) add_net(value);
    else if (!strcmp(name, "--group")) {
        if (group_count == DN_SESSION_GROUPS_MAX) dn_harness("--group: more than %d groups", DN_SESSION_GROUPS_MAX);
        groups[group_count++] = value;
    } else return 0;
    return 1;
}

__attribute__((noreturn, format(printf, 1, 2))) static void refuse(const char *format, ...) {
    va_list args;
    va_start(args, format);
    dn_end(4, format, args);
}

static void boot_id(char id[BOOT_ID + 1]) {
    int fd = open("/proc/sys/kernel/random/boot_id", O_RDONLY | O_CLOEXEC);
    if (fd < 0) dn_harness("boot_id: %s", strerror(errno));
    ssize_t n = read(fd, id, BOOT_ID);
    close(fd);
    if (n != BOOT_ID) dn_harness("boot_id: %zd bytes", n);
    id[BOOT_ID] = 0;
}

/* A mark in `dir`: only a whole one of another boot is removed; one of this boot, or one that cannot
 * be read whole, refuses the start. */
static void check_mark(int dir, const char *where, const char *boot) {
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
    if (!memcmp(seen, boot, BOOT_ID))
        refuse("%s/%s: a sync failed since the machine started; restart it, or repair the store", where, MARK);
    if (unlinkat(dir, MARK, 0) && errno != ENOENT) dn_harness("%s/%s: %s", where, MARK, strerror(errno));
}

static int open_dir(const char *path) {
    int fd = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (fd < 0) dn_harness("%s: %s", path, strerror(errno));
    return fd;
}

void dn_store_start(void) {
    if (!spool_path) {
        if (run_path || identity || group_count || net_count) dn_harness("store options without --spool");
        return;
    }
    if (!run_path) dn_harness("--spool needs --run-dir");
    if (identity && strlen(identity) > DN_SESSION_IDENTITY_MAX)
        dn_harness("--path-identity: more than %d bytes", DN_SESSION_IDENTITY_MAX);
    for (size_t g = 0; g < group_count; ++g)
        if (!*groups[g] || strlen(groups[g]) > DN_SESSION_GROUP_MAX)
            dn_harness("--group: 1 to %d bytes: %s", DN_SESSION_GROUP_MAX, groups[g]);
    if (!net_count) {
        add_net("127.0.0.0/8");
        add_net("::1/128");
    }
    spool = open_dir(spool_path);
    if (flock(spool, LOCK_EX | LOCK_NB)) {
        if (errno == EWOULDBLOCK) refuse("%s: another process holds the spool", spool_path);
        dn_harness("flock %s: %s", spool_path, strerror(errno));
    }
    char boot[BOOT_ID + 1];
    boot_id(boot);
    check_mark(spool, spool_path, boot);
    int run = open_dir(run_path);
    check_mark(run, run_path, boot);
    close(run);
    for (size_t got = 0; got < sizeof random_octets;) {
        ssize_t n = getrandom(random_octets + got, sizeof random_octets - got, 0);
        if (n < 0 && errno != EINTR) dn_harness("getrandom: %s", strerror(errno));
        if (n > 0) got += (size_t)n;
    }
}

void dn_store_fill(unsigned char *next) {
    struct timespec t;
    if (clock_gettime(CLOCK_REALTIME, &t)) dn_harness("clock_gettime: %s", strerror(errno));
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
