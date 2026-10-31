/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The echo host on io_uring (uring.h), beside the poll host (echo_server.c), whose options, admission
 * and counters it keeps, so that the same tests run against both. Every payload byte goes through
 * generated dn_echo. A send is submitted as soon as the last completes, so a reply reaches the kernel
 * sooner than the poll host's, which waits to be told the socket is writable.
 *
 * A thread a core it may run on, pinned there, each with its own ring and its own copy of the Cake
 * image: the build assembles the generated code and its runtime COPIES times, every global symbol
 * prefixed with the copy's number, since one image cannot be entered by two threads. The main thread
 * owns the listener and the admission count: it accepts only while fewer than SLOTS connections are
 * held in all, hands each to the next thread as a message on that thread's ring, and learns from a
 * message on its own when one is let go.
 *
 * A thread keeps at most one receive or send in flight a connection, and reads only once the reply
 * has gone whole. A connection ends by its end of input, an error, its idle deadline or the stop; its
 * operations are cancelled and every one reaped before its descriptor is closed and its slot given
 * back, so a completion always finds the incarnation that submitted it, which the generation in its
 * token says. SIGTERM or SIGINT stops accepting, stops every thread the same way, waits for each,
 * and only then closes the rings. A start that fails once a thread has started stops those that did,
 * in that order, and ends the host with status 1. A kernel without io_uring, or older than 6.6, is
 * refused at the start, by name, with status 1. */
#define _GNU_SOURCE
#include "accept_policy.h"
#include "faults.h"
#include "host.h"
#include "uring.h"
#include <arpa/inet.h>
#include <inttypes.h>
#include <poll.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <sys/resource.h>
#include <sys/signalfd.h>
#include <sys/socket.h>
#include <sys/utsname.h>
#include <time.h>

enum { SLOTS = 32, CAPACITY = 4096, COPIES = 8, ENTRIES = 128, ACCEPT_BACKOFF_MS = 50 };
enum { K_RECV = 1, K_SEND, K_CANCEL, K_ACCEPT, K_SIGNAL, K_TOLD, K_HANDED, K_FREED, K_STOP };

typedef uint32_t echo_fn(uint64_t, uint64_t, uint64_t, uint64_t);
#define COPY(k) \
    extern echo_fn copy##k##_dn_echo; \
    extern void copy##k##_dn_runtime_setup(void), copy##k##_cml_main(void);
COPY(0) COPY(1) COPY(2) COPY(3) COPY(4) COPY(5) COPY(6) COPY(7)
#undef COPY
#define COPY(k) {copy##k##_dn_echo, copy##k##_dn_runtime_setup, copy##k##_cml_main}
static const struct { echo_fn *echo; void (*setup)(void), (*enter)(void); } copies[COPIES] = {
    COPY(0), COPY(1), COPY(2), COPY(3), COPY(4), COPY(5), COPY(6), COPY(7)};
#undef COPY

static const uint8_t worker_ops[] = {IORING_OP_RECV, IORING_OP_SEND, IORING_OP_ASYNC_CANCEL,
                                     IORING_OP_MSG_RING};
static const uint8_t main_ops[] = {IORING_OP_ACCEPT, IORING_OP_POLL_ADD, IORING_OP_ASYNC_CANCEL,
                                   IORING_OP_MSG_RING};

struct slot {
    int fd;          /* -1 when free */
    uint32_t gen;    /* of the connection the slot holds or held last; it wraps, which no completion can
                        mistake, since a slot is taken again only once every one of its last is reaped */
    int ops;         /* submitted and not yet reaped, cancels among them */
    int closing;     /* its operations are being cancelled; it closes once the last is reaped */
    unsigned char in[CAPACITY], out[CAPACITY];
    size_t length, sent;
    uint64_t active;
};

struct counts {
    uint64_t calls, bytes, sends, partial, expired, expired_pending, send_renewals, recv_renewals, cancelled;
};

struct worker {
    pthread_t thread;
    int created;     /* the thread runs, or ran */
    unsigned index, cpu;
    struct dn_ring ring;
    int ring_fd;     /* for messages, set once the ring is open; read under `lock` */
    int ready, failed, stopping;
    int awaiting_late;  /* the test build's: a connection handed over after the stop is still to come */
    char why[256];
    struct slot slots[SLOTS];
    unsigned held;   /* slots with a descriptor */
    struct counts n;
};

static unsigned write_chunk = CAPACITY, idle_ms = 30000, send_buffer, threads;
static cpu_set_t cpus;
static struct worker workers[COPIES];
static int main_ring_fd = -1;
static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t started = PTHREAD_COND_INITIALIZER;

static uint64_t millis(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) dn_harness_now("clock_gettime: %s", strerror(errno));
    return (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_nsec / 1000000;
}

static unsigned number(const char *text, unsigned maximum) { return (unsigned)dn_parse_u64(text, maximum); }

static struct io_uring_sqe *sqe(struct dn_ring *r, uint64_t token) {
    struct io_uring_sqe *s = dn_ring_get(r, token);
    if (s) return s;
    int e = dn_ring_enter(r, 0, 0);
    if (e) dn_harness_now("io_uring_enter: %s", strerror(-e));
    if (!(s = dn_ring_get(r, token))) dn_harness_now("io_uring: no submission entry free");
    return s;
}

static int worker_foreign(uint64_t token) {
    unsigned kind = DN_TOKEN_KIND(token);
    return kind == K_HANDED || kind == K_STOP;
}

static int main_foreign(uint64_t token) { return DN_TOKEN_KIND(token) == K_FREED; }

static void arm_recv(struct worker *w, unsigned i) {
    struct slot *s = &w->slots[i];
    dn_prep_recv(sqe(&w->ring, DN_TOKEN(K_RECV, i, s->gen)), s->fd, s->in, CAPACITY);
    ++s->ops;
}

static void arm_send(struct worker *w, unsigned i) {
    struct slot *s = &w->slots[i];
    size_t remaining = s->length - s->sent, chunk = remaining < write_chunk ? remaining : write_chunk;
    dn_prep_send(sqe(&w->ring, DN_TOKEN(K_SEND, i, s->gen)), s->fd, s->out + s->sent, (unsigned)chunk, 0);
    ++s->ops;
}

/* The slot's last operation is reaped: its descriptor closes and the main thread learns of the
 * place given back. */
static void finish(struct worker *w, unsigned i) {
    struct slot *s = &w->slots[i];
    close(s->fd);
    s->fd = -1;
    s->closing = 0;
    s->length = s->sent = 0;
    --w->held;
    dn_prep_message(sqe(&w->ring, DN_TOKEN(K_TOLD, i, 0)), main_ring_fd, DN_TOKEN(K_FREED, w->index, 0), 0);
}

/* Ends the connection of slot `i`: at once if nothing of it is in flight, else once its cancelled
 * operations are reaped. */
static void end(struct worker *w, unsigned i) {
    struct slot *s = &w->slots[i];
    if (s->closing) return;
    s->closing = 1;
    if (!s->ops) {
        finish(w, i);
        return;
    }
    dn_prep_cancel_fd(sqe(&w->ring, DN_TOKEN(K_CANCEL, i, s->gen)), s->fd);
    ++s->ops;
}

static void renew(struct slot *s, uint64_t *count) {
    s->active = millis();
    ++*count;
}

/* A connection the main thread accepted, given a free slot: there is one, since it admits no more
 * than SLOTS in all. */
static void take(struct worker *w, int fd) {
    unsigned i = 0;
    while (i < SLOTS && (w->slots[i].fd >= 0 || w->slots[i].ops)) ++i;
    if (i == SLOTS) dn_violation_now("thread %u was handed a connection with every slot taken", w->index);
    struct slot *s = &w->slots[i];
    s->fd = fd;
    ++s->gen;
    s->length = s->sent = 0;
    s->active = millis();
    ++w->held;
    /* One handed over just before the stop is closed at once. */
    if (w->stopping) w->awaiting_late = 0;
    if (w->stopping) end(w, i);
    else arm_recv(w, i);
}

static void completed(struct worker *w, const struct io_uring_cqe *c) {
    uint64_t t = c->user_data;
    unsigned kind = DN_TOKEN_KIND(t), i = DN_TOKEN_SLOT(t);
    if (kind == K_HANDED) {
        take(w, c->res);
        return;
    }
    if (kind == K_STOP) {
        w->stopping = 1;
        /* The test build's `dn/echo-late` keeps the thread for a connection handed over after its stop. */
        w->awaiting_late = DN_FAULT("dn/echo-late");
        for (unsigned k = 0; k < SLOTS; ++k)
            if (w->slots[k].fd >= 0) end(w, k);
        return;
    }
    if (kind == K_TOLD) {
        if (c->res < 0)
            dn_harness_now("thread %u could not tell of a slot given back: %s", w->index, strerror(-c->res));
        return;
    }
    if (i >= SLOTS || (kind != K_RECV && kind != K_SEND && kind != K_CANCEL))
        dn_violation_now("thread %u: a completion of token %" PRIx64, w->index, t);
    struct slot *s = &w->slots[i];
    /* The test build's `dn/stale` makes a receive's completion look as if the connection before had
     * submitted it. */
    if (kind == K_RECV && DN_FAULT("dn/stale")) t -= (uint64_t)1 << 32;
    if (s->fd < 0 || DN_TOKEN_GEN(t) != s->gen || !s->ops)
        dn_violation_now("thread %u: a completion for generation %" PRIu32 " of slot %u, which is at %" PRIu32
                         " with %d live", w->index, DN_TOKEN_GEN(t), i, s->gen, s->ops);
    --s->ops;
    if (c->res == -ECANCELED) ++w->n.cancelled;
    if (s->closing || kind == K_CANCEL) {
        if (s->closing && !s->ops) finish(w, i);
        return;
    }
    if (c->res <= 0) {
        /* the end of input, an error, or a send that took nothing */
        end(w, i);
        return;
    }
    if (kind == K_RECV) {
        uint64_t got = (uint64_t)c->res;
        uint64_t produced = copies[w->index].echo((uintptr_t)s->in, (uintptr_t)s->out, got, CAPACITY);
        if (produced != got)
            dn_violation_now("generated echo contract failed: %" PRIu64 " for %" PRIu64, produced, got);
        ++w->n.calls;
        w->n.bytes += produced;
        s->length = (size_t)produced;
        s->sent = 0;
        renew(s, &w->n.recv_renewals);
        arm_send(w, i);
        return;
    }
    ++w->n.sends;
    size_t n = (size_t)c->res, remaining = s->length - s->sent;
    if (n > remaining) dn_violation_now("a send took %zu bytes of %zu", n, remaining);
    if (n < remaining) ++w->n.partial;
    s->sent += n;
    renew(s, &w->n.send_renewals);
    if (s->sent < s->length) {
        arm_send(w, i);
    } else {
        s->length = s->sent = 0;
        arm_recv(w, i);
    }
}

/* Each connection idle for its time ends, one still holding a reply counted apart; says how long
 * until the next deadline, -1 for none. */
static int64_t expire(struct worker *w) {
    uint64_t now = millis();
    int64_t next = -1;
    for (unsigned i = 0; i < SLOTS; ++i) {
        struct slot *s = &w->slots[i];
        if (s->fd < 0 || s->closing) continue;
        if (now - s->active >= idle_ms) {
            if (s->length) ++w->n.expired_pending;
            ++w->n.expired;
            end(w, i);
            continue;
        }
        int64_t left = (int64_t)(s->active + idle_ms - now);
        if (next < 0 || left < next) next = left;
    }
    return next;
}

static void *serve(void *arg) {
    struct worker *w = arg;
    uint64_t lost = 0;
    cpu_set_t one;
    CPU_ZERO(&one);
    CPU_SET(w->cpu, &one);
    int pinned = pthread_setaffinity_np(pthread_self(), sizeof one, &one);
    /* The test build's `dn/echo-thread` fails the start of the thread whose number is one less than
     * the number it was enabled with. */
    if (DN_FAULT_INFO("dn/echo-thread", lost) && lost == w->index + 1) {
        snprintf(w->why, sizeof w->why, "a fault was planted");
    } else if (pinned) {
        snprintf(w->why, sizeof w->why, "pinning to CPU %u: %s", w->cpu, strerror(pinned));
    } else if (!dn_ring_open(&w->ring, ENTRIES, worker_ops, sizeof worker_ops, w->why, sizeof w->why)) {
        copies[w->index].setup();
        copies[w->index].enter();
    }
    pthread_mutex_lock(&lock);
    w->failed = w->ring.fd < 0;
    w->ring_fd = w->ring.fd;
    w->ready = 1;
    pthread_cond_broadcast(&started);
    pthread_mutex_unlock(&lock);
    if (w->failed) return NULL;
    for (;;) {
        int64_t wait = expire(w);
        if (w->stopping && !w->held && !w->ring.live && !w->awaiting_late) break;
        int e = dn_ring_enter(&w->ring, 1, wait);
        if (e) dn_harness_now("thread %u: io_uring_enter: %s", w->index, strerror(-e));
        struct io_uring_cqe c;
        while (dn_ring_take(&w->ring, &c, worker_foreign)) completed(w, &c);
    }
    dn_ring_close(&w->ring);
    return NULL;
}

/* What the main thread owns. */
static struct dn_ring ring;
static int listener = -1, signals = -1, late_peer = -1, stopping, accepting, signal_armed, result, late;
static unsigned admitted, next_thread;
static uint64_t paused_until, accepted, accept_errors, accept_retries;

/* The test build's `dn/echo-stop-lost` sends the stops to no ring. */
static void tell_stop(void) {
    for (unsigned k = 0; k < threads; ++k)
        if (!workers[k].failed && workers[k].ring_fd >= 0)
            dn_prep_message(sqe(&ring, DN_TOKEN(K_TOLD, k, 0)),
                            DN_FAULT("dn/echo-stop-lost") ? -1 : workers[k].ring_fd, DN_TOKEN(K_STOP, 0, 0), 0);
}

static void stop(void) {
    if (stopping) return;
    stopping = 1;
    if (accepting) dn_prep_cancel(sqe(&ring, DN_TOKEN(K_CANCEL, 0, 0)), DN_TOKEN(K_ACCEPT, 0, 0));
    if (signal_armed) dn_prep_cancel(sqe(&ring, DN_TOKEN(K_CANCEL, 1, 0)), DN_TOKEN(K_SIGNAL, 0, 0));
    tell_stop();
    late = DN_FAULT("dn/echo-late");
}

/* Hands the accepted `fd` to the next thread, or closes it if its socket cannot be shaped. The test
 * build's `dn/echo-sndbuf` fails the shaping, and its `dn/echo-handover` sends the message to no
 * ring. */
static void hand(int fd) {
    if (send_buffer) {
        int size = (int)send_buffer;
        if (DN_FAULT("dn/echo-sndbuf") || setsockopt(fd, SOL_SOCKET, SO_SNDBUF, &size, sizeof size)) {
            close(fd);
            return;
        }
    }
    ++admitted;
    ++accepted;
    unsigned k = next_thread;
    next_thread = (next_thread + 1) % threads;
    int target = DN_FAULT("dn/echo-handover") ? -1 : workers[k].ring_fd;
    dn_prep_message(sqe(&ring, DN_TOKEN(K_TOLD, (unsigned)fd, 1)), target, DN_TOKEN(K_HANDED, 0, 0), fd);
}

static void main_completed(const struct io_uring_cqe *c) {
    uint64_t t = c->user_data;
    switch (DN_TOKEN_KIND(t)) {
    case K_FREED: {
        if (!admitted) dn_violation_now("a slot given back with none admitted");
        --admitted;
        /* The test build's `dn/echo-late` hands a connection over, its peer kept open, once a thread has
         * shown it took its stop by giving a place back, as a hand-over the thread takes only after its
         * stop would be. */
        int pair[2];
        if (late && !socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, pair)) {
            late = 0;
            late_peer = pair[1];
            hand(pair[0]);
        }
        return;
    }
    case K_ACCEPT:
        accepting = 0;
        if (c->res >= 0) {
            if (stopping) close(c->res);
            else hand(c->res);
            return;
        }
        if (c->res == -ECANCELED) return;
        switch (dn_accept_action(-c->res)) {
        case DN_ACCEPT_RETRY:
            ++accept_retries;
            return;
        case DN_ACCEPT_PAUSE:
            /* Keep serving what is held; come back to the listener once the resource has had a
             * moment to free up. */
            ++accept_errors;
            paused_until = millis() + ACCEPT_BACKOFF_MS;
            return;
        case DN_ACCEPT_FATAL:
        default:
            fprintf(stderr, "accept: %s\n", strerror(-c->res));
            result = 1;
            stop();
            return;
        }
    case K_SIGNAL: {
        signal_armed = 0;
        if (c->res == -ECANCELED) return;
        struct signalfd_siginfo si;
        if (read(signals, &si, sizeof si) == (ssize_t)sizeof si || c->res < 0) stop();
        return;
    }
    case K_TOLD:
        /* A message a thread could not take: a connection handed over is closed and its place given
         * back; a stop lost would leave the thread serving, and the host waiting for it for good. */
        if (c->res < 0 && DN_TOKEN_GEN(t) == 1) {
            close((int)DN_TOKEN_SLOT(t));
            --admitted;
        } else if (c->res < 0) {
            dn_harness_now("could not tell thread %u to stop: %s", DN_TOKEN_SLOT(t), strerror(-c->res));
        }
        return;
    case K_CANCEL:
        return;
    default:
        dn_violation_now("a completion of token %" PRIx64 " on the main ring", t);
    }
}

/* The threads, a core the process may run on each, as many as the image has copies and the
 * descriptors allow beside the slots. */
static unsigned thread_count(unsigned asked, rlim_t descriptors) {
    int cores = CPU_COUNT(&cpus);
    /* standard streams, listener, signals and the main ring */
    rlim_t fixed = 6 + SLOTS;
    rlim_t room = descriptors > fixed ? descriptors - fixed : 0;
    unsigned n = asked ? asked : cores < 1 ? 1 : cores > COPIES ? COPIES : (unsigned)cores;
    if (!asked && room < n) n = (unsigned)room;
    if (n < 1 || n > room) return 0;
    return n;
}

/* Each thread pinned to the next core of those the process may run on. */
static void start_threads(void) {
    unsigned cpu = 0;
    for (unsigned k = 0; k < threads; ++k) {
        while (!CPU_ISSET(cpu % CPU_SETSIZE, &cpus)) ++cpu;
        workers[k] = (struct worker){.index = k, .cpu = cpu % CPU_SETSIZE, .ring_fd = -1};
        ++cpu;
        workers[k].ring.fd = -1;
        for (unsigned i = 0; i < SLOTS; ++i) workers[k].slots[i].fd = -1;
        /* The test build's `dn/echo-create` fails the creation of the thread whose number is one less than
         * the number it was enabled with. */
        uint64_t refused = 0;
        int e = DN_FAULT_INFO("dn/echo-create", refused) && refused == k + 1
                    ? EAGAIN : pthread_create(&workers[k].thread, NULL, serve, &workers[k]);
        workers[k].created = !e;
        if (e) {
            snprintf(workers[k].why, sizeof workers[k].why, "pthread_create: %s", strerror(e));
            workers[k].failed = workers[k].ready = 1;
        }
    }
    pthread_mutex_lock(&lock);
    for (unsigned k = 0; k < threads; ++k)
        while (!workers[k].ready) pthread_cond_wait(&started, &lock);
    pthread_mutex_unlock(&lock);
}

int main(int argc, char **argv) {
    unsigned port = 0, asked = 0;
    for (int i = 1; i < argc; i += 2) {
        if (i + 1 == argc) { fputs("option needs a value\n", stderr); return 2; }
        if (!strcmp(argv[i], "--port")) port = number(argv[i+1], 65535);
        else if (!strcmp(argv[i], "--write-chunk")) write_chunk = number(argv[i+1], CAPACITY);
        else if (!strcmp(argv[i], "--idle-ms")) idle_ms = number(argv[i+1], 60000);
        else if (!strcmp(argv[i], "--send-buffer")) send_buffer = number(argv[i+1], 1 << 20);
        else if (!strcmp(argv[i], "--threads")) asked = number(argv[i+1], COPIES);
        else { fputs("unknown option\n", stderr); return 2; }
    }
    if (!write_chunk || idle_ms < 50) {
        fputs("the write chunk must be positive and the idle time at least 50 ms\n", stderr);
        return 2;
    }
    struct rlimit descriptors;
    if (getrlimit(RLIMIT_NOFILE, &descriptors)) { perror("getrlimit"); return 1; }
    if (sched_getaffinity(0, sizeof cpus, &cpus)) { perror("sched_getaffinity"); return 1; }
    if (!(threads = thread_count(asked, descriptors.rlim_cur))) {
        fputs("too few file descriptors for the slot table and the threads\n", stderr);
        return 1;
    }
    /* Every thread inherits the mask: the signals come only through the descriptor. */
    sigset_t mask;
    sigemptyset(&mask);
    sigaddset(&mask, SIGTERM);
    sigaddset(&mask, SIGINT);
    if (pthread_sigmask(SIG_BLOCK, &mask, NULL)) { perror("pthread_sigmask"); return 1; }
    if ((signals = signalfd(-1, &mask, SFD_NONBLOCK | SFD_CLOEXEC)) < 0) { perror("signalfd"); return 1; }
    struct sigaction ignore = {0};
    ignore.sa_handler = SIG_IGN;
    if (sigaction(SIGPIPE, &ignore, NULL)) { perror("sigaction"); return 1; }
    char why[256];
    if (dn_ring_open(&ring, ENTRIES, main_ops, sizeof main_ops, why, sizeof why)) {
        fprintf(stderr, "%s\n", why);
        return 1;
    }
    main_ring_fd = ring.fd;
    listener = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (listener < 0) { perror("socket"); return 1; }
    int one = 1;
    struct sockaddr_in address = { .sin_family = AF_INET, .sin_port = htons((uint16_t)port),
                                  .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
    socklen_t address_len = sizeof address;
    if (setsockopt(listener, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one) ||
        bind(listener, (struct sockaddr *)&address, sizeof address) || listen(listener, SLOTS) ||
        getsockname(listener, (struct sockaddr *)&address, &address_len)) {
        perror("listener");
        return 1;
    }
    start_threads();
    for (unsigned k = 0; k < threads; ++k)
        if (workers[k].failed) {
            fprintf(stderr, "thread %u could not start: %s; stopping the others\n", k, workers[k].why);
            result = 1;
            stopping = 1;
        }
    struct utsname host;
    if (!stopping && uname(&host)) {
        perror("uname");
        result = stopping = 1;
    }
    if (!stopping) {
        printf("{\"port\":%u,\"slots\":%u,\"buffer_bytes\":%u,\"threads\":%u,\"kernel\":\"%s\","
               "\"io_uring_features\":%u}\n",
               (unsigned)ntohs(address.sin_port), SLOTS, CAPACITY, threads, host.release, ring.features);
        if (fflush(stdout)) {
            perror("fflush");
            result = stopping = 1;
        }
    }
    if (stopping) tell_stop();
    while (!stopping || ring.live || late) {
        int64_t wait = -1;
        if (!stopping && !signal_armed) {
            dn_prep_poll(sqe(&ring, DN_TOKEN(K_SIGNAL, 0, 0)), signals, POLLIN);
            signal_armed = 1;
        }
        if (!stopping && !accepting && admitted < SLOTS) {
            uint64_t now = millis();
            if (now >= paused_until) {
                dn_prep_accept(sqe(&ring, DN_TOKEN(K_ACCEPT, 0, 0)), listener, NULL, NULL);
                accepting = 1;
            } else {
                wait = (int64_t)(paused_until - now);
            }
        }
        int e = dn_ring_enter(&ring, 1, wait);
        if (e) dn_harness_now("io_uring_enter: %s", strerror(-e));
        struct io_uring_cqe c;
        while (dn_ring_take(&ring, &c, main_foreign)) main_completed(&c);
    }
    /* Each thread ends once its connections are closed and its ring is drained; the messages they
     * send meanwhile land on this ring, which is closed only after them. */
    struct counts total = {0};
    for (unsigned k = 0; k < threads; ++k) {
        if (workers[k].created) pthread_join(workers[k].thread, NULL);
        struct counts *n = &workers[k].n;
        total.calls += n->calls;
        total.bytes += n->bytes;
        total.sends += n->sends;
        total.partial += n->partial;
        total.expired += n->expired;
        total.expired_pending += n->expired_pending;
        total.send_renewals += n->send_renewals;
        total.recv_renewals += n->recv_renewals;
        total.cancelled += n->cancelled;
    }
    dn_ring_close(&ring);
    close(listener);
    close(signals);
    if (late_peer >= 0) close(late_peer);
    fprintf(stderr, "{\"kernel_calls\":%" PRIu64 ",\"kernel_bytes\":%" PRIu64
            ",\"send_calls\":%" PRIu64 ",\"partial_progress\":%" PRIu64
            ",\"accepted\":%" PRIu64 ",\"idle_expired\":%" PRIu64
            ",\"accept_errors\":%" PRIu64 ",\"expired_pending\":%" PRIu64
            ",\"send_renewals\":%" PRIu64 ",\"recv_renewals\":%" PRIu64
            ",\"accept_retries\":%" PRIu64 ",\"cancelled\":%" PRIu64 ",\"threads\":%u}\n",
            total.calls, total.bytes, total.sends, total.partial, accepted, total.expired, accept_errors,
            total.expired_pending, total.send_renewals, total.recv_renewals, accept_retries, total.cancelled,
            threads);
    return result;
}
