/* SPDX-License-Identifier: AGPL-3.0-or-later
 * io_uring through its three system calls, without liburing: one ring, used by the one thread that
 * opened it. The ring is opened disabled, restricted to the operations its owner names, and only then
 * enabled, so that nothing else can be submitted on it nor registered. It needs Linux 6.6, for the
 * newest setup flag it passes, and refuses an older or locked-down kernel by name rather than falling
 * back to anything.
 *
 * Every operation carries a token in its user data: its kind, the slot it belongs to and the slot's
 * generation, so that a completion is applied to the incarnation that submitted it. The ring counts
 * what is submitted and not yet reaped; it is closed only once that is zero, since the kernel keeps
 * writing into the buffers of operations in flight even after their descriptors are closed. */
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

/* Opens a ring of `entries` submissions (a power of two up to 4096, completions twice that) on which
 * only the `n` operations of `ops` may be submitted, none with flags. Nonzero with the reason in
 * `why` when the kernel cannot give one: io_uring missing or refused (ENOSYS, EPERM), a kernel
 * before 6.6, an operation or a feature it lacks. */
int dn_ring_open(struct dn_ring *r, unsigned entries, const uint8_t *ops, size_t n, char *why, size_t why_len);

/* A cleared submission entry with `token` as its user data, counted live; NULL when every entry is
 * prepared and not yet submitted, after which `dn_ring_enter` makes room. */
struct io_uring_sqe *dn_ring_get(struct dn_ring *r, uint64_t token);

/* Submits what is prepared and waits until `wait` completions are ready or `timeout_ms` has passed
 * (negative: no limit; 0: does not wait). Returns 0, or a negative error number the ring cannot go
 * on after; an interruption, a full completion queue and a short submission are dealt with here. */
int dn_ring_enter(struct dn_ring *r, unsigned wait, int64_t timeout_ms);

/* The next completion, if one is ready: 1 and the entry in `cqe`, its operation no longer live,
 * unless `foreign` says it was posted by another ring's message; 0 when none is. */
int dn_ring_take(struct dn_ring *r, struct io_uring_cqe *cqe, int (*foreign)(uint64_t token));

/* Unmaps and closes the ring: aborts the process if an operation is still live, since the kernel
 * would go on writing into memory the caller is about to free. */
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
