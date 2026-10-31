/* SPDX-License-Identifier: AGPL-3.0-or-later
 * io_uring without liburing (uring.h). The rings are shared with the kernel: an entry is written
 * before the tail that publishes it is stored with release, the kernel's tail is loaded with acquire
 * before the entries it covers are read, and a head is moved on with release once its entry is
 * copied out, as io_uring(7) has it. */
#define _GNU_SOURCE
#include "uring.h"
#include "faults.h"
#include <errno.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

/* What the kernel gives that this file relies on: one mapping for both queues, no completion ever dropped,
 * submissions read once, and a wait with a timeout. */
static const struct { unsigned bit; const char *name; } needed[] = {
    {IORING_FEAT_SINGLE_MMAP, "single mapping"}, {IORING_FEAT_NODROP, "no dropped completions"},
    {IORING_FEAT_SUBMIT_STABLE, "stable submissions"}, {IORING_FEAT_EXT_ARG, "waits with a timeout"}};

__attribute__((format(printf, 3, 4))) static int refused(char *why, size_t why_len, const char *format, ...) {
    va_list args;
    va_start(args, format);
    vsnprintf(why, why_len, format, args);
    va_end(args);
    return -1;
}

static int unmapped(struct dn_ring *r) {
    if (r->rings && r->rings != MAP_FAILED) munmap(r->rings, r->rings_len);
    if (r->sqes && (void *)r->sqes != MAP_FAILED) munmap(r->sqes, r->sqes_len);
    close(r->fd);
    r->fd = -1;
    return -1;
}

static int registered(int fd, unsigned op, void *arg, unsigned n) {
    return (int)syscall(__NR_io_uring_register, fd, op, arg, n);
}

/* Whether every operation of `ops` is one the kernel has. */
static int probed(int fd, const uint8_t *ops, size_t n, char *why, size_t why_len) {
    size_t size = sizeof(struct io_uring_probe) + 256 * sizeof(struct io_uring_probe_op);
    struct io_uring_probe *probe = calloc(1, size);
    if (!probe) return refused(why, why_len, "io_uring: no memory for the probe");
    if (registered(fd, IORING_REGISTER_PROBE, probe, 256)) {
        free(probe);
        return refused(why, why_len, "io_uring: the probe failed: %s", strerror(errno));
    }
    for (size_t i = 0; i < n; ++i)
        if (ops[i] > probe->last_op || !(probe->ops[ops[i]].flags & IO_URING_OP_SUPPORTED)) {
            free(probe);
            return refused(why, why_len, "io_uring: the kernel lacks operation %u", ops[i]);
        }
    free(probe);
    return 0;
}

/* Only the operations of `ops` from now on, and no registration but the one that enables the ring:
 * with restrictions in place the kernel refuses every flag not allowed, and recent kernels restrict
 * registration only once a rule names one. */
static int restricted(int fd, const uint8_t *ops, size_t n, char *why, size_t why_len) {
    struct io_uring_restriction rules[257];
    if (n > 256) return refused(why, why_len, "io_uring: %zu operations", n);
    memset(rules, 0, sizeof rules);
    for (size_t i = 0; i < n; ++i) {
        rules[i].opcode = IORING_RESTRICTION_SQE_OP;
        rules[i].sqe_op = ops[i];
    }
    rules[n].opcode = IORING_RESTRICTION_REGISTER_OP;
    rules[n].register_op = IORING_REGISTER_ENABLE_RINGS;
    if (registered(fd, IORING_REGISTER_RESTRICTIONS, rules, (unsigned)n + 1))
        return refused(why, why_len, "io_uring: restricting the ring failed: %s", strerror(errno));
    if (registered(fd, IORING_REGISTER_ENABLE_RINGS, NULL, 0))
        return refused(why, why_len, "io_uring: enabling the ring failed: %s", strerror(errno));
    return 0;
}

int dn_ring_open(struct dn_ring *r, unsigned entries, const uint8_t *ops, size_t n, char *why, size_t why_len) {
    memset(r, 0, sizeof *r);
    r->fd = -1;
    if (entries < 1 || entries > 4096 || (entries & (entries - 1)))
        return refused(why, why_len, "io_uring: %u entries is not a power of two up to 4096", entries);
    struct io_uring_params p;
    memset(&p, 0, sizeof p);
    p.flags = IORING_SETUP_R_DISABLED | IORING_SETUP_SINGLE_ISSUER | IORING_SETUP_DEFER_TASKRUN |
              IORING_SETUP_SUBMIT_ALL | IORING_SETUP_NO_SQARRAY | IORING_SETUP_CQSIZE;
    p.cq_entries = 2 * entries;
    /* The test build's `dn/uring-setup` fails the setup with the error number it was enabled with. */
    r->fd = DN_FAULT("dn/uring-setup") ? -1 : (int)syscall(__NR_io_uring_setup, entries, &p);
    if (r->fd < 0) {
        int code = errno;
        if (code == ENOSYS) return refused(why, why_len, "io_uring: not in this kernel");
        if (code == EPERM)
            return refused(why, why_len,
                           "io_uring: refused here (a seccomp filter or kernel.io_uring_disabled)");
        if (code == EINVAL)
            return refused(why, why_len, "io_uring: the kernel lacks a setup flag (it is older than 6.6)");
        return refused(why, why_len, "io_uring: the setup failed: %s", strerror(code));
    }
    uint64_t lacking = 0;
    DN_FAULT_INFO("dn/uring-features", lacking);
    r->features = p.features & ~(unsigned)lacking;
    for (size_t i = 0; i < sizeof needed / sizeof needed[0]; ++i)
        if (!(r->features & needed[i].bit)) {
            refused(why, why_len, "io_uring: the kernel lacks the feature of %s", needed[i].name);
            return unmapped(r);
        }
    size_t sq_len = p.sq_off.array + p.sq_entries * sizeof(unsigned);
    size_t cq_len = p.cq_off.cqes + p.cq_entries * sizeof(struct io_uring_cqe);
    r->rings_len = sq_len > cq_len ? sq_len : cq_len;
    r->sqes_len = p.sq_entries * sizeof(struct io_uring_sqe);
    r->rings = mmap(NULL, r->rings_len, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, r->fd, IORING_OFF_SQ_RING);
    r->sqes = mmap(NULL, r->sqes_len, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, r->fd, IORING_OFF_SQES);
    if (r->rings == MAP_FAILED || (void *)r->sqes == MAP_FAILED) {
        refused(why, why_len, "io_uring: mapping the ring failed: %s", strerror(errno));
        return unmapped(r);
    }
    unsigned char *base = r->rings;
    r->sq_head = (unsigned *)(base + p.sq_off.head);
    r->sq_tail = (unsigned *)(base + p.sq_off.tail);
    r->sq_mask = *(unsigned *)(base + p.sq_off.ring_mask);
    r->sq_entries = *(unsigned *)(base + p.sq_off.ring_entries);
    r->cq_head = (unsigned *)(base + p.cq_off.head);
    r->cq_tail = (unsigned *)(base + p.cq_off.tail);
    r->cq_mask = *(unsigned *)(base + p.cq_off.ring_mask);
    r->cq_entries = *(unsigned *)(base + p.cq_off.ring_entries);
    r->cqes = (struct io_uring_cqe *)(base + p.cq_off.cqes);
    r->sq_local = *r->sq_tail;
    if (probed(r->fd, ops, n, why, why_len) || restricted(r->fd, ops, n, why, why_len)) return unmapped(r);
    return 0;
}

struct io_uring_sqe *dn_ring_get(struct dn_ring *r, uint64_t token) {
    if (r->sq_local - __atomic_load_n(r->sq_head, __ATOMIC_ACQUIRE) >= r->sq_entries) return NULL;
    struct io_uring_sqe *s = &r->sqes[r->sq_local & r->sq_mask];
    memset(s, 0, sizeof *s);
    s->user_data = token;
    ++r->sq_local;
    ++r->live;
    return s;
}

static uint64_t monotonic_ms(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_nsec / 1000000;
}

int dn_ring_enter(struct dn_ring *r, unsigned wait, int64_t timeout_ms) {
    uint64_t until = timeout_ms > 0 ? monotonic_ms() + (uint64_t)timeout_ms : 0;
    if (timeout_ms == 0) wait = 0;
    for (;;) {
        __atomic_store_n(r->sq_tail, r->sq_local, __ATOMIC_RELEASE);
        unsigned submit = r->sq_local - __atomic_load_n(r->sq_head, __ATOMIC_ACQUIRE);
        /* Completions of a ring that defers its work are posted only inside this call. */
        unsigned flags = IORING_ENTER_GETEVENTS;
        struct __kernel_timespec ts = {0, 0};
        struct io_uring_getevents_arg arg = {0, 0, 0, 0};
        if (wait && timeout_ms > 0) {
            uint64_t now = monotonic_ms(), left = until > now ? until - now : 0;
            ts.tv_sec = (long long)(left / 1000);
            ts.tv_nsec = (long long)(left % 1000) * 1000000;
            arg.ts = (uint64_t)(uintptr_t)&ts;
            flags |= IORING_ENTER_EXT_ARG;
        }
        /* The test build's `dn/uring-short` cuts a submission to one entry, which then waits for
         * nothing, as a submission the kernel cuts short does not; its `dn/uring-enter` fails the call
         * with the error number it was enabled with. */
        unsigned asked = submit > 1 && DN_FAULT("dn/uring-short") ? 1 : submit;
        long got = DN_FAULT("dn/uring-enter") ? -1
                   : syscall(__NR_io_uring_enter, r->fd, asked, asked < submit ? 0 : wait, flags,
                             flags & IORING_ENTER_EXT_ARG ? (void *)&arg : NULL,
                             flags & IORING_ENTER_EXT_ARG ? sizeof arg : 0);
        if (got < 0) {
            int code = errno;
            if (code == ETIME) return 0;
            if (code == EINTR) continue;
            /* The completion queue is full, or the kernel is short of memory for a request: the
             * caller reaps what is there and comes back, and what is not yet submitted waits; with
             * nothing to reap it comes back at once, spinning through the shortage. */
            if (code == EBUSY || code == EAGAIN) return 0;
            return -code;
        }
        /* A submission cut short waited for nothing and left the rest in the queue: submit that, and
         * wait then. */
        if ((unsigned)got < submit && __atomic_load_n(r->sq_head, __ATOMIC_ACQUIRE) != r->sq_local) continue;
        return 0;
    }
}

int dn_ring_take(struct dn_ring *r, struct io_uring_cqe *cqe, int (*foreign)(uint64_t token)) {
    unsigned head = *r->cq_head;
    if (head == __atomic_load_n(r->cq_tail, __ATOMIC_ACQUIRE)) return 0;
    *cqe = r->cqes[head & r->cq_mask];
    __atomic_store_n(r->cq_head, head + 1, __ATOMIC_RELEASE);
    if (!foreign || !foreign(cqe->user_data)) {
        if (!r->live) {
            fprintf(stderr, "io_uring: a completion of user data %llx with nothing live\n",
                    (unsigned long long)cqe->user_data);
            abort();
        }
        --r->live;
    }
    return 1;
}

void dn_ring_close(struct dn_ring *r) {
    if (r->fd < 0) return;
    if (r->live) {
        fprintf(stderr, "io_uring: the ring closed with %llu operations live\n", (unsigned long long)r->live);
        abort();
    }
    unmapped(r);
}

void dn_prep_recv(struct io_uring_sqe *s, int fd, void *buffer, unsigned len) {
    s->opcode = IORING_OP_RECV;
    s->fd = fd;
    s->addr = (uint64_t)(uintptr_t)buffer;
    s->len = len;
}

void dn_prep_send(struct io_uring_sqe *s, int fd, const void *buffer, unsigned len, int flags) {
    s->opcode = IORING_OP_SEND;
    s->fd = fd;
    s->addr = (uint64_t)(uintptr_t)buffer;
    s->len = len;
    s->msg_flags = (unsigned)(flags | MSG_NOSIGNAL);
}

void dn_prep_accept(struct io_uring_sqe *s, int fd, void *address, unsigned *address_len) {
    s->opcode = IORING_OP_ACCEPT;
    s->fd = fd;
    s->addr = (uint64_t)(uintptr_t)address;
    s->addr2 = (uint64_t)(uintptr_t)address_len;
    s->accept_flags = SOCK_NONBLOCK | SOCK_CLOEXEC;
}

void dn_prep_poll(struct io_uring_sqe *s, int fd, unsigned events) {
    s->opcode = IORING_OP_POLL_ADD;
    s->fd = fd;
    s->poll32_events = events;
}

void dn_prep_cancel_fd(struct io_uring_sqe *s, int fd) {
    s->opcode = IORING_OP_ASYNC_CANCEL;
    s->fd = fd;
    s->cancel_flags = IORING_ASYNC_CANCEL_FD | IORING_ASYNC_CANCEL_ALL;
}

void dn_prep_cancel(struct io_uring_sqe *s, uint64_t token) {
    s->opcode = IORING_OP_ASYNC_CANCEL;
    s->fd = -1;
    s->addr = token;
}

void dn_prep_message(struct io_uring_sqe *s, int ring_fd, uint64_t token, int32_t res) {
    s->opcode = IORING_OP_MSG_RING;
    s->fd = ring_fd;
    s->addr = IORING_MSG_DATA;
    s->len = (uint32_t)res;
    s->off = token;
}
