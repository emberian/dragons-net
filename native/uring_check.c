/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The io_uring layer (uring.h) on the running kernel: what the ring refuses, a kernel that refuses
 * io_uring through a seccomp filter, a queue fuller than it holds, completions past the completion
 * queue, cancellation by token and by descriptor, a message between two rings of two threads, waits
 * that end, and a ring closed with an operation live. Prints the cases as JSON; a case that fails
 * ends the check with status 1. */
#define _GNU_SOURCE
#include "host.h"
#include "uring.h"
#include <fcntl.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stddef.h>
#include <sys/prctl.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>

enum { K_RECV = 1, K_SEND, K_CANCEL, K_NOP, K_DENIED, K_MESSAGE, K_POLL };

static const uint8_t ops[] = {IORING_OP_RECV, IORING_OP_SEND, IORING_OP_ASYNC_CANCEL, IORING_OP_NOP,
                              IORING_OP_MSG_RING, IORING_OP_POLL_ADD};
static unsigned cases;

static void open_ring(struct dn_ring *r, unsigned entries) {
    char why[256];
    if (dn_ring_open(r, entries, ops, sizeof ops, why, sizeof why)) dn_harness("%s", why);
}

static void enter(struct dn_ring *r, unsigned wait, int64_t timeout_ms) {
    int e = dn_ring_enter(r, wait, timeout_ms);
    if (e) dn_harness("io_uring_enter: %s", strerror(-e));
}

static struct io_uring_sqe *get(struct dn_ring *r, uint64_t token) {
    struct io_uring_sqe *s = dn_ring_get(r, token);
    if (!s) dn_violation("no submission entry free for %llx", (unsigned long long)token);
    return s;
}

/* The completion of `token` into `c`, waiting for it; others met on the way are counted in `others`. */
static void wait_for(struct dn_ring *r, uint64_t token, unsigned *others, struct io_uring_cqe *c) {
    for (int rounds = 0; rounds < 100; ++rounds) {
        while (dn_ring_take(r, c, NULL)) {
            if (c->user_data == token) return;
            ++*others;
        }
        enter(r, 1, 1000);
    }
    dn_violation("no completion of %llx", (unsigned long long)token);
}

/* Every completion there is reaped, each given to `seen`, within a bound: a cancellation that never
 * ends fails the check by name. */
static void drain(struct dn_ring *r, const char *what, void (*seen)(const struct io_uring_cqe *c)) {
    struct io_uring_cqe c;
    for (int rounds = 0; r->live && rounds < 100; ++rounds) {
        enter(r, 1, 1000);
        while (dn_ring_take(r, &c, NULL)) seen(&c);
    }
    if (r->live) dn_violation("%s: %llu operations never ended", what, (unsigned long long)r->live);
}

static int received, cancel, cancelled, counted;

static void by_token(const struct io_uring_cqe *c) {
    *(DN_TOKEN_KIND(c->user_data) == K_RECV ? &received : &cancel) = c->res;
}

static void by_descriptor(const struct io_uring_cqe *c) {
    if (DN_TOKEN_KIND(c->user_data) == K_CANCEL) counted = c->res;
    else if (c->res == -ECANCELED) ++cancelled;
    else dn_violation("an operation cancelled by descriptor ended %d", c->res);
}

static void sent_three(const struct io_uring_cqe *c) {
    if (c->res != 3) dn_violation("the send took %d bytes", c->res);
}

static uint64_t now_ms(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_nsec / 1000000;
}

static void refusals(void) {
    struct dn_ring r;
    char why[256];
    if (!dn_ring_open(&r, 6, ops, sizeof ops, why, sizeof why) || !strstr(why, "not a power of two"))
        dn_violation("a ring of 6 entries was not refused: %s", why);
    const uint8_t unknown[] = {IORING_OP_RECV, 255};
    if (!dn_ring_open(&r, 8, unknown, sizeof unknown, why, sizeof why) || !strstr(why, "lacks operation 255"))
        dn_violation("an operation the kernel lacks was not refused: %s", why);
    cases += 2;
    /* An operation the ring was not opened for, and an allowed one with a flag, are refused by the
     * kernel itself. */
    open_ring(&r, 8);
    struct io_uring_sqe *s = get(&r, DN_TOKEN(K_DENIED, 0, 1));
    s->opcode = IORING_OP_OPENAT;
    s->fd = AT_FDCWD;
    s->addr = (uint64_t)(uintptr_t)"/";
    s = get(&r, DN_TOKEN(K_DENIED, 1, 1));
    s->opcode = IORING_OP_NOP;
    s->flags = IOSQE_ASYNC;
    unsigned others = 0;
    for (unsigned k = 0; k < 2; ++k) {
        struct io_uring_cqe c;
        wait_for(&r, DN_TOKEN(K_DENIED, k, 1), &others, &c);
        if (c.res != -EACCES) dn_violation("a restricted submission %u ended %d, not -EACCES", k, c.res);
    }
    if (others || r.live) dn_violation("refused submissions left %u others and %llu live", others,
                                       (unsigned long long)r.live);
    /* Nor may anything be registered once the ring is enabled. */
    int fd = 0;
    if (syscall(__NR_io_uring_register, r.fd, IORING_REGISTER_FILES, &fd, 1) != -1 || errno != EACCES)
        dn_violation("registering a file on an enabled ring was not refused with EACCES: %s", strerror(errno));
    dn_ring_close(&r);
    cases += 3;
}

/* In a child whose seccomp filter answers io_uring_setup with `code`, the ring is refused with
 * `said`, as a container's filter or kernel.io_uring_disabled refuses it. */
static void refused_by_kernel(int code, const char *said) {
    pid_t child = fork();
    if (child < 0) dn_harness("fork: %s", strerror(errno));
    if (child == 0) {
        struct sock_filter rules[] = {
            BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, arch)),
            BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, AUDIT_ARCH_X86_64, 1, 0),
            BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
            BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
            BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, __NR_io_uring_setup, 0, 1),
            BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | ((unsigned)code & SECCOMP_RET_DATA)),
            BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
        };
        struct sock_fprog program = {sizeof rules / sizeof rules[0], rules};
        if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) || prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &program))
            _exit(3);
        struct dn_ring r;
        char why[256];
        _exit(dn_ring_open(&r, 8, ops, sizeof ops, why, sizeof why) && strstr(why, said) ? 0 : 4);
    }
    int status;
    if (waitpid(child, &status, 0) != child) dn_harness("waitpid: %s", strerror(errno));
    if (!WIFEXITED(status) || WEXITSTATUS(status) == 3) dn_harness("installing a seccomp filter failed (%d)", status);
    if (WEXITSTATUS(status)) dn_violation("io_uring_setup failing with %d was not refused as %s", code, said);
    cases += 1;
}

/* More submissions than the queue holds, and more completions than the completion queue holds:
 * none is lost and each is reaped once. */
static void floods(void) {
    struct dn_ring r;
    open_ring(&r, 4);
    unsigned prepared = 0;
    struct io_uring_sqe *s;
    while ((s = dn_ring_get(&r, DN_TOKEN(K_NOP, prepared, 1)))) {
        s->opcode = IORING_OP_NOP;
        ++prepared;
    }
    if (prepared != r.sq_entries) dn_violation("%u entries prepared of %u", prepared, r.sq_entries);
    unsigned total = 0;
    /* Submitting without reaping fills the completion queue twice over. */
    for (unsigned round = 0; round < 6; ++round) {
        enter(&r, 0, 0);
        while ((s = dn_ring_get(&r, DN_TOKEN(K_NOP, prepared, 1)))) {
            s->opcode = IORING_OP_NOP;
            ++prepared;
        }
    }
    struct io_uring_cqe c;
    unsigned char *seen = calloc(prepared, 1);
    if (!seen) dn_harness("calloc");
    for (int rounds = 0; total < prepared && rounds < 1000; ++rounds) {
        enter(&r, 0, 0);
        while (dn_ring_take(&r, &c, NULL)) {
            unsigned slot = DN_TOKEN_SLOT(c.user_data);
            if (c.res != 0 || slot >= prepared || seen[slot]++)
                dn_violation("the completion of entry %u ended %d, or came twice", slot, c.res);
            ++total;
        }
    }
    free(seen);
    if (total != prepared || r.live) dn_violation("%u completions of %u, %llu live", total, prepared,
                                                  (unsigned long long)r.live);
    dn_ring_close(&r);
    cases += 1;
}

/* A receive that never completes, cancelled by its token and then by its descriptor: each posts its
 * own completion, -ECANCELED, besides the cancel's. Data sent arrives whole. */
static void cancels(void) {
    int pair[2];
    if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, pair)) dn_harness("socketpair: %s", strerror(errno));
    struct dn_ring r;
    open_ring(&r, 8);
    char buffer[16];
    dn_prep_recv(get(&r, DN_TOKEN(K_RECV, 0, 7)), pair[0], buffer, sizeof buffer);
    enter(&r, 0, 0);
    dn_prep_cancel(get(&r, DN_TOKEN(K_CANCEL, 0, 7)), DN_TOKEN(K_RECV, 0, 7));
    struct io_uring_cqe c;
    received = cancel = 1;
    drain(&r, "a cancel by token", by_token);
    if (received != -ECANCELED || cancel != 0)
        dn_violation("by token: the receive ended %d, the cancel %d", received, cancel);
    /* By descriptor: a receive and a poll on one socket. */
    dn_prep_recv(get(&r, DN_TOKEN(K_RECV, 1, 8)), pair[0], buffer, sizeof buffer);
    dn_prep_poll(get(&r, DN_TOKEN(K_POLL, 1, 8)), pair[0], POLLIN);
    enter(&r, 0, 0);
    dn_prep_cancel_fd(get(&r, DN_TOKEN(K_CANCEL, 1, 8)), pair[0]);
    cancelled = 0;
    counted = -1;
    drain(&r, "a cancel by descriptor", by_descriptor);
    if (cancelled != 2 || counted != 2)
        dn_violation("by descriptor: %d cancelled, the cancel said %d", cancelled, counted);
    /* A send and a receive that meet. */
    dn_prep_recv(get(&r, DN_TOKEN(K_RECV, 2, 9)), pair[1], buffer, sizeof buffer);
    dn_prep_send(get(&r, DN_TOKEN(K_SEND, 2, 9)), pair[0], "abc", 3, 0);
    unsigned others = 0;
    wait_for(&r, DN_TOKEN(K_RECV, 2, 9), &others, &c);
    if (c.res != 3 || memcmp(buffer, "abc", 3)) dn_violation("a receive took %d bytes", c.res);
    drain(&r, "a send", sent_three);
    dn_ring_close(&r);
    close(pair[0]);
    close(pair[1]);
    cases += 3;
}

/* A wait with nothing to come ends at its time, not before; one of no time does not wait. */
static void waits(void) {
    struct dn_ring r;
    open_ring(&r, 4);
    uint64_t start = now_ms();
    enter(&r, 1, 60);
    uint64_t took = now_ms() - start;
    if (took < 60 || took > 5000) dn_violation("a wait of 60 ms took %llu", (unsigned long long)took);
    start = now_ms();
    enter(&r, 1, 0);
    took = now_ms() - start;
    if (took > 50) dn_violation("a wait of no time took %llu ms", (unsigned long long)took);
    dn_ring_close(&r);
    cases += 2;
}

static struct dn_ring receiver;
static int receiver_fd = -1;
static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t opened = PTHREAD_COND_INITIALIZER;

static int is_message(uint64_t token) { return DN_TOKEN_KIND(token) == K_MESSAGE; }

/* Another thread's ring, opened in that thread, which waits for one message. */
static void *receive(void *unused) {
    (void)unused;
    open_ring(&receiver, 4);
    pthread_mutex_lock(&lock);
    receiver_fd = receiver.fd;
    pthread_cond_signal(&opened);
    pthread_mutex_unlock(&lock);
    struct io_uring_cqe c;
    for (int rounds = 0; rounds < 100; ++rounds) {
        enter(&receiver, 1, 1000);
        if (dn_ring_take(&receiver, &c, is_message)) {
            if (c.user_data != DN_TOKEN(K_MESSAGE, 5, 3) || c.res != 42 || receiver.live)
                dn_violation("the message came as %llx %d, %llu live", (unsigned long long)c.user_data, c.res,
                             (unsigned long long)receiver.live);
            dn_ring_close(&receiver);
            return NULL;
        }
    }
    dn_violation("no message came");
}

static void messages(void) {
    pthread_t thread;
    if (pthread_create(&thread, NULL, receive, NULL)) dn_harness("pthread_create");
    pthread_mutex_lock(&lock);
    while (receiver_fd < 0) pthread_cond_wait(&opened, &lock);
    pthread_mutex_unlock(&lock);
    struct dn_ring r;
    open_ring(&r, 4);
    dn_prep_message(get(&r, DN_TOKEN(K_MESSAGE, 0, 1)), receiver_fd, DN_TOKEN(K_MESSAGE, 5, 3), 42);
    unsigned others = 0;
    struct io_uring_cqe c;
    wait_for(&r, DN_TOKEN(K_MESSAGE, 0, 1), &others, &c);
    if (c.res != 0) dn_violation("sending the message ended %d", c.res);
    pthread_join(thread, NULL);
    dn_ring_close(&r);
    cases += 1;
}

/* Closing a ring with a receive live ends the process rather than leave the kernel writing into
 * freed memory. */
static void closed_live(void) {
    pid_t child = fork();
    if (child < 0) dn_harness("fork: %s", strerror(errno));
    if (child == 0) {
        dn_expect_faults();
        int pair[2];
        if (socketpair(AF_UNIX, SOCK_STREAM, 0, pair)) _exit(9);
        struct dn_ring r;
        open_ring(&r, 4);
        static char buffer[8];
        dn_prep_recv(get(&r, DN_TOKEN(K_RECV, 0, 1)), pair[0], buffer, sizeof buffer);
        enter(&r, 0, 0);
        fclose(stderr);
        dn_ring_close(&r);
        _exit(0);
    }
    int status;
    if (waitpid(child, &status, 0) != child) dn_harness("waitpid: %s", strerror(errno));
    if (!WIFSIGNALED(status) || WTERMSIG(status) != SIGABRT)
        dn_violation("a ring closed with a receive live did not abort (status %d)", status);
    cases += 1;
}

int main(void) {
    refusals();
    refused_by_kernel(EPERM, "refused here");
    refused_by_kernel(ENOSYS, "not in this kernel");
    floods();
    cancels();
    waits();
    messages();
    closed_live();
    printf("{\"uring_cases\":%u}\n", cases);
    return 0;
}
