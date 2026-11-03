/* SPDX-License-Identifier: AGPL-3.0-or-later
 * io_uring through its three system calls, without liburing: one ring for the thread that opened it. It opens disabled,
 * restricted to its owner's operations, then enabled; it needs Linux 6.6 and refuses older kernels by name. Operations
 * carry a kind, slot and generation token; the ring closes only with nothing in flight. */
#ifndef DN_URING_H
#define DN_URING_H

#include <linux/io_uring.h>
#include <stddef.h>
#include <stdint.h>

struct dn_ring {
    int fd;
    unsigned features;
    unsigned *sq_head, *sq_tail, sq_mask, sq_entries, sq_local;
    struct io_uring_sqe *sqes;
    unsigned *cq_head, *cq_tail, cq_mask, cq_entries;
    struct io_uring_cqe *cqes;
    void *rings;
    size_t rings_len, sqes_len;
    uint64_t live;    /* submitted or prepared, and not yet reaped */
};

/* user_data: the generation in the high 32 bits, the slot in the next 24, the kind in the low 8. */
#define DN_TOKEN(kind, slot, gen) \
    (((uint64_t)(uint32_t)(gen) << 32) | ((uint64_t)((slot) & 0xffffffu) << 8) | (uint64_t)((kind) & 0xffu))
#define DN_TOKEN_KIND(t) ((unsigned)((t) & 0xffu))
#define DN_TOKEN_SLOT(t) ((unsigned)(((t) >> 8) & 0xffffffu))
#define DN_TOKEN_GEN(t) ((uint32_t)((t) >> 32))

/* Opens a ring of `entries` submissions (a power of two to 4096, completions twice that), only `ops` allowed, no flags.
 * Nonzero, reason in `why`, when io_uring is missing or refused, the kernel predates 6.6, or lacks an operation. */
int dn_ring_open(struct dn_ring *r, unsigned entries, const uint8_t *ops, size_t n, char *why, size_t why_len);

/* A cleared submission entry with `token` as user data, counted live. NULL when every entry is prepared and
 * unsubmitted; `dn_ring_enter` then makes room. */
struct io_uring_sqe *dn_ring_get(struct dn_ring *r, uint64_t token);

/* Submits what is prepared and waits for `wait` completions or `timeout_ms` (negative: no limit; 0: no wait). Returns 0
 * or a fatal negative error; interruptions, a full completion queue and short submissions are handled here. */
int dn_ring_enter(struct dn_ring *r, unsigned wait, int64_t timeout_ms);

/* The next ready completion: 1 and the entry in `cqe`; 0 when none is ready. Its operation is no longer live, unless
 * `foreign` says another ring's message posted it. */
int dn_ring_take(struct dn_ring *r, struct io_uring_cqe *cqe, int (*foreign)(uint64_t token));

/* Unmaps and closes the ring; aborts if an operation is still live, since the kernel would write into freed memory. */
void dn_ring_close(struct dn_ring *r);

/* The submissions every host makes. */
void dn_prep_recv(struct io_uring_sqe *s, int fd, void *buffer, unsigned len);
void dn_prep_send(struct io_uring_sqe *s, int fd, const void *buffer, unsigned len, int flags);
void dn_prep_accept(struct io_uring_sqe *s, int fd, void *address, unsigned *address_len);
void dn_prep_poll(struct io_uring_sqe *s, int fd, unsigned events);
/* Cancels every live operation on `fd`; each still posts its own completion, and so does this. */
void dn_prep_cancel_fd(struct io_uring_sqe *s, int fd);
/* Cancels the live operation whose user data is `token`. */
void dn_prep_cancel(struct io_uring_sqe *s, uint64_t token);
/* Posts a completion of `res` and user data `token` on the ring whose descriptor is `ring_fd`. */
void dn_prep_message(struct io_uring_sqe *s, int ring_fd, uint64_t token, int32_t res);

#endif
