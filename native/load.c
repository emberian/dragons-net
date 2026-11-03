// SPDX-License-Identifier: AGPL-3.0-or-later
/*
 * dn-load: an open-loop load for a TCP server with known replies; `--requests FILE` gives the exchanges. Requests fall
 * due at `--rate` regardless of the server, latency from due time to reply (wrk2's coordinated-omission correction).
 * Prints a JSON record; status 0 if all replies were right and connections lasted, 1 otherwise, 2 on usage error.
 */
#define _GNU_SOURCE
#include <errno.h>
#include <inttypes.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

/* A log-linear histogram of nanoseconds: exact below 128, then 64 cells a power of two. A cell's width is under 1/64 of
 * its values. */
enum { EXACT = 128, CELLS = EXACT + 57 * 64 };

struct histogram {
    uint64_t count[CELLS];
    uint64_t total, max;
};

static unsigned cell_of(uint64_t v) {
    if (v < EXACT) return (unsigned)v;
    unsigned shift = 63 - (unsigned)__builtin_clzll(v) - 6;
    return EXACT + (shift - 1) * 64 + (unsigned)((v >> shift) - 64);
}

/* The largest value a cell holds. */
static uint64_t cell_top(unsigned cell) {
    if (cell < EXACT) return cell;
    unsigned shift = (cell - EXACT) / 64 + 1;
    uint64_t m = (cell - EXACT) % 64 + 64;
    return ((m + 1) << shift) - 1;
}

static void record_n(struct histogram *h, uint64_t v, uint64_t n) {
    h->count[cell_of(v)] += n;
    h->total += n;
    if (n && v > h->max) h->max = v;
}

static void record(struct histogram *h, uint64_t v) { record_n(h, v, 1); }

static void merge(struct histogram *into, const struct histogram *h) {
    for (unsigned i = 0; i < CELLS; i++) into->count[i] += h->count[i];
    into->total += h->total;
    if (h->max > into->max) into->max = h->max;
}

/* The least value at least a share `q` of the values do not exceed, to the cell. */
static uint64_t quantile(const struct histogram *h, double q) {
    uint64_t rank = (uint64_t)(q * (double)h->total), seen = 0;
    if ((double)rank < q * (double)h->total) rank++;
    if (rank < 1) rank = 1;
    for (unsigned i = 0; i < CELLS; i++)
        if ((seen += h->count[i]) >= rank) return cell_top(i) < h->max ? cell_top(i) : h->max;
    return h->max;
}

struct exchange {
    const uint8_t *send, *expect;
    uint32_t send_len, expect_len;
};

/* A slow reader's requests: request 0 again until their replies come to this. */
enum { SLOW_CHUNK = 16, SLOW_OCTETS = 16 << 20 };

static struct exchange opening, slow_burst, *requests;
static uint32_t request_count;

struct conn {
    int fd, slow, opened, waiting, at;
    const struct exchange *now;
    uint32_t sent, got;
    uint64_t due, period, key, rng;
};

struct worker {
    pthread_t thread;
    int index, conns, slow, heap_n, draining;
    struct conn **heap;
    struct histogram latency, late;
    uint64_t completed, served, answered, sent, wrong, lost, owed, slow_octets, slow_paced, into_ns, past_ns;
    char why[160];
};

static struct sockaddr_in server;
static double rate;
static int conns_total, threads_total = 1, slow_total;
static uint64_t slow_ns = 10000000u, start_ns, measure_from, measure_to, end_ns;

static uint64_t now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec;
}

static int in_window(uint64_t t) { return t >= measure_from && t < measure_to; }

static uint64_t next_random(uint64_t *s) {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    return *s;
}

__attribute__((noreturn)) static void usage(const char *why) {
    fprintf(stderr, "dn-load: %s\n", why);
    exit(2);
}

/* A min-heap of connections by `key`: when each next has something to do. `at` is its place, -1
 * when out of the heap. */
static void heap_swap(struct worker *w, int a, int b) {
    struct conn *t = w->heap[a];
    w->heap[a] = w->heap[b];
    w->heap[b] = t;
    w->heap[a]->at = a;
    w->heap[b]->at = b;
}

static struct conn *heap_pop(struct worker *w) {
    struct conn *top = w->heap[0];
    heap_swap(w, 0, --w->heap_n);
    top->at = -1;
    for (int i = 0;;) {
        int l = 2 * i + 1, r = l + 1, m = i;
        if (l < w->heap_n && w->heap[l]->key < w->heap[m]->key) m = l;
        if (r < w->heap_n && w->heap[r]->key < w->heap[m]->key) m = r;
        if (m == i) break;
        heap_swap(w, i, m);
        i = m;
    }
    return top;
}

static void heap_remove(struct worker *w, struct conn *c) {
    if (c->at < 0) return;
    c->key = 0;
    for (int i = c->at; i; i = (i - 1) / 2) heap_swap(w, i, (i - 1) / 2);
    heap_pop(w);
}

static void heap_push(struct worker *w, struct conn *c, uint64_t key) {
    heap_remove(w, c);
    c->key = key;
    c->at = w->heap_n;
    w->heap[w->heap_n++] = c;
    for (int i = c->at; i && w->heap[(i - 1) / 2]->key > w->heap[i]->key; i = (i - 1) / 2) heap_swap(w, i, (i - 1) / 2);
}

static int connect_to(int slow) {
    int fd = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0), one = 1, small = 4096;
    if (fd < 0) return -1;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
    if (slow) setsockopt(fd, SOL_SOCKET, SO_RCVBUF, &small, sizeof small);
    if (connect(fd, (struct sockaddr *)&server, sizeof server) && errno != EINPROGRESS) {
        close(fd);
        return -1;
    }
    return fd;
}

static void drop(struct worker *w, struct conn *c, int ep, uint64_t *count, const char *why) {
    if (!w->why[0]) snprintf(w->why, sizeof w->why, "%s", why);
    (*count)++;
    heap_remove(w, c);
    epoll_ctl(ep, EPOLL_CTL_DEL, c->fd, NULL);
    close(c->fd);
    c->fd = -1;
}

/* A slow reader keeps its pace till the window closes, then takes what is left as fast as it can. */
static int paced(const struct worker *w, const struct conn *c) {
    return c->slow && !w->draining;
}

/* A paced reader is not told of its input: it takes it at its times. */
static uint32_t events(const struct worker *w, const struct conn *c, int out) {
    return (paced(w, c) ? 0 : EPOLLIN) | (out ? EPOLLOUT : 0);
}

static void interest(const struct worker *w, struct conn *c, int ep, int out) {
    struct epoll_event e = {.events = events(w, c, out), .data.ptr = c};
    epoll_ctl(ep, EPOLL_CTL_MOD, c->fd, &e);
}

/* Send what is left of the request: 0 once it is all in the kernel. */
static int push(struct worker *w, struct conn *c, int ep) {
    while (c->sent < c->now->send_len) {
        ssize_t n = send(c->fd, c->now->send + c->sent, c->now->send_len - c->sent, MSG_NOSIGNAL | MSG_DONTWAIT);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0 && errno == EAGAIN) {
            interest(w, c, ep, 1);
            return 1;
        }
        if (n <= 0) {
            drop(w, c, ep, &w->lost, "a send failed");
            return -1;
        }
        c->sent += (uint32_t)n;
    }
    return 0;
}

static void begin(struct worker *w, struct conn *c, int ep, uint64_t t) {
    c->now = c->slow ? &slow_burst : &requests[next_random(&c->rng) % request_count];
    c->sent = c->got = 0;
    c->waiting = 1;
    if (c->slow) {
        c->due = t;
    } else {
        w->sent++;
        if (in_window(c->due)) record(&w->late, t - c->due);
    }
    if (push(w, c, ep) >= 0 && c->slow) heap_push(w, c, t + slow_ns);
}

/* A reply is whole: time it, and send the next request or wait for its time. */
static void finished(struct worker *w, struct conn *c, int ep, uint64_t t) {
    c->waiting = 0;
    c->got = 0;
    w->answered++;
    if (c->slow) {
        /* Once the window has closed a slow reader takes what it asked for, and asks no more. */
        if (paced(w, c)) begin(w, c, ep, t);
        return;
    }
    if (in_window(t)) w->served++;
    if (in_window(c->due)) {
        record(&w->latency, t > c->due ? t - c->due : 0);
        w->completed++;
    }
    /* The greatest delay of a reply carried into the window from the warm-up, and of one past its end. */
    uint64_t *edge = c->due < measure_from && in_window(t) ? &w->into_ns
                     : in_window(c->due) && t >= measure_to ? &w->past_ns
                                                           : NULL;
    if (edge && t - c->due > *edge) *edge = t - c->due;
    c->due += c->period;
    if (c->due >= measure_to) return;
    if (c->due <= t) begin(w, c, ep, t);
    else heap_push(w, c, c->due);
}

/* Take what the server sent; a slow connection takes one chunk at most. */
static void take(struct worker *w, struct conn *c, int ep, uint64_t t) {
    uint8_t buf[65536];
    for (;;) {
        const struct exchange *x = c->opened ? (c->waiting ? c->now : NULL) : &opening;
        size_t want = x ? x->expect_len - c->got : 1;
        if (paced(w, c) && want > SLOW_CHUNK) want = SLOW_CHUNK;
        if (want > sizeof buf) want = sizeof buf;
        ssize_t n = recv(c->fd, buf, want, MSG_DONTWAIT);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0 && errno == EAGAIN) return;
        if (n == 0) {
            drop(w, c, ep, &w->lost, "the server closed a connection");
            return;
        }
        if (n < 0) {
            drop(w, c, ep, &w->lost, "a receive failed");
            return;
        }
        if (!x) {
            drop(w, c, ep, &w->wrong, "octets came with no request in flight");
            return;
        }
        if (memcmp(buf, x->expect + c->got, (size_t)n)) {
            drop(w, c, ep, &w->wrong, "a reply differs");
            return;
        }
        if (c->slow) {
            w->slow_octets += (uint64_t)n;
            if (paced(w, c)) w->slow_paced += (uint64_t)n;
        }
        if ((c->got += (uint32_t)n) < x->expect_len) {
            if (paced(w, c)) return;
            continue;
        }
        if (c->opened) {
            finished(w, c, ep, t);
            return;
        }
        c->opened = 1;
        c->got = 0;
        if (c->slow) begin(w, c, ep, t);
        else if (c->due < measure_to) heap_push(w, c, c->due);
        return;
    }
}

/* At the end: each request of the window still unanswered is owed, timed to the end. */
static void settle(struct worker *w, struct conn *c) {
    if (c->slow || !c->period) return;
    uint64_t due = c->due < measure_from ? c->due + (measure_from - c->due + c->period - 1) / c->period * c->period
                                         : c->due;
    /* At most some thousands of steps, each a run of requests timed as its last, a lower bound. */
    uint64_t each = (measure_to - measure_from) / 4096 / c->period + 1;
    for (; due < measure_to; due += each * c->period) {
        uint64_t n = (measure_to - due + c->period - 1) / c->period;
        if (n > each) n = each;
        record_n(&w->latency, end_ns - (due + (n - 1) * c->period), n);
        w->owed += n;
    }
}

static void *work(void *arg) {
    struct worker *w = arg;
    prctl(PR_SET_TIMERSLACK, 1UL, 0UL, 0UL, 0UL);
    int n = w->conns + w->slow, ep = epoll_create1(EPOLL_CLOEXEC);
    struct conn *cs = calloc((size_t)n, sizeof *cs);
    struct epoll_event *evs = calloc((size_t)n, sizeof *evs);
    w->heap = calloc((size_t)n, sizeof *w->heap);
    if (ep < 0 || !cs || !evs || !w->heap) {
        snprintf(w->why, sizeof w->why, "out of memory or descriptors");
        w->lost += (uint64_t)n;
        return NULL;
    }
    double per_conn = rate / conns_total;
    for (int i = 0; i < n; i++) {
        struct conn *c = &cs[i];
        c->slow = i >= w->conns;
        c->at = -1;
        c->rng = 0x9e3779b97f4a7c15u ^ ((uint64_t)w->index << 32) ^ (uint64_t)(i + 1);
        c->period = c->slow ? 0 : (uint64_t)(1e9 / per_conn);
        c->due = start_ns + (c->period ? next_random(&c->rng) % c->period : 0);
        if ((c->fd = connect_to(c->slow)) < 0) {
            snprintf(w->why, sizeof w->why, "connect: %s", strerror(errno));
            w->lost++;
            continue;
        }
        struct epoll_event e = {.events = events(w, c, 0), .data.ptr = c};
        epoll_ctl(ep, EPOLL_CTL_ADD, c->fd, &e);
        c->opened = !opening.expect_len;
        c->now = &opening;
        if (opening.send_len && push(w, c, ep) < 0) continue;
        if (c->slow) heap_push(w, c, start_ns);
        else if (c->opened && c->due < measure_to) heap_push(w, c, c->due);
    }
    for (;;) {
        uint64_t t = now_ns();
        if (t >= end_ns) break;
        if (!w->draining && t >= measure_to) {
            w->draining = 1;
            for (int i = 0; i < n; i++)
                if (cs[i].slow && cs[i].fd >= 0) {
                    heap_remove(w, &cs[i]);
                    interest(w, &cs[i], ep, cs[i].now && cs[i].sent < cs[i].now->send_len);
                }
        }
        while (w->heap_n && w->heap[0]->key <= t) {
            struct conn *c = heap_pop(w);
            if (!c->slow) begin(w, c, ep, t);
            else if (c->opened && !c->waiting) begin(w, c, ep, t);
            else {
                take(w, c, ep, t);
                if (c->fd >= 0 && c->at < 0 && (c->waiting || !c->opened)) heap_push(w, c, t + slow_ns);
            }
        }
        uint64_t wake = w->heap_n && w->heap[0]->key < end_ns ? w->heap[0]->key : end_ns;
        struct timespec ts = {.tv_sec = (time_t)((wake - t) / 1000000000u),
                              .tv_nsec = (long)((wake - t) % 1000000000u)};
        int got = epoll_pwait2(ep, evs, n, &ts, NULL);
        if (got < 0 && errno != EINTR) {
            snprintf(w->why, sizeof w->why, "epoll_pwait2: %s", strerror(errno));
            w->lost++;
            break;
        }
        for (int k = 0; k < got; k++) {
            struct conn *c = evs[k].data.ptr;
            if (c->fd < 0) continue;
            t = now_ns();
            if (evs[k].events & EPOLLOUT) {
                interest(w, c, ep, 0);
                if (push(w, c, ep) < 0) continue;
            }
            /* A slow connection is told only of an error or a hang-up: it then takes what is left. */
            if (evs[k].events & (EPOLLIN | EPOLLHUP | EPOLLERR)) take(w, c, ep, t);
        }
    }
    for (int i = 0; i < n; i++) {
        if (cs[i].fd < 0) continue;
        settle(w, &cs[i]);
        close(cs[i].fd);
    }
    free(cs);
    free(evs);
    free(w->heap);
    close(ep);
    return NULL;
}

static uint32_t le32(const uint8_t *p) {
    return (uint32_t)p[0] | (uint32_t)p[1] << 8 | (uint32_t)p[2] << 16 | (uint32_t)p[3] << 24;
}

static int exchange_at(const uint8_t *b, size_t len, size_t *at, struct exchange *x) {
    for (int part = 0; part < 2; part++) {
        if (len - *at < 4) return -1;
        uint32_t n = le32(b + *at);
        if (len - *at - 4 < n) return -1;
        if (part) x->expect = b + *at + 4, x->expect_len = n;
        else x->send = b + *at + 4, x->send_len = n;
        *at += 4 + (size_t)n;
    }
    return 0;
}

static uint8_t *repeated(const uint8_t *octets, uint32_t len, uint32_t times) {
    uint8_t *out = malloc((size_t)len * times);
    if (!out) usage("out of memory");
    for (uint32_t i = 0; i < times; i++) memcpy(out + (size_t)i * len, octets, len);
    return out;
}

static void read_requests(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) usage("--requests: cannot open it");
    size_t cap = 1 << 16, len = 0, at = 0;
    uint8_t *b = malloc(cap);
    for (size_t r; b && (r = fread(b + len, 1, cap - len, f)) > 0;)
        if ((len += r) == cap) b = realloc(b, cap *= 2);
    fclose(f);
    if (!b) usage("out of memory");
    if (exchange_at(b, len, &at, &opening)) usage("--requests: no opening");
    size_t room = 16;
    requests = malloc(room * sizeof *requests);
    while (requests && at < len) {
        if (request_count == room) requests = realloc(requests, (room *= 2) * sizeof *requests);
        if (!requests) break;
        if (exchange_at(b, len, &at, &requests[request_count]) || !requests[request_count].send_len ||
            !requests[request_count].expect_len)
            usage("--requests: a request cut short or empty");
        request_count++;
    }
    if (!requests) usage("out of memory");
    if (!request_count) usage("--requests: no request");
    uint32_t times = (SLOW_OCTETS + requests[0].expect_len - 1) / requests[0].expect_len;
    slow_burst = (struct exchange){repeated(requests[0].send, requests[0].send_len, times),
                                   repeated(requests[0].expect, requests[0].expect_len, times),
                                   requests[0].send_len * times, requests[0].expect_len * times};
}

static void print_histogram(const char *name, const struct histogram *h, const char *after) {
    static const double qs[] = {0.5, 0.9, 0.99, 0.999, 0.9999};
    static const char *const names[] = {"p50", "p90", "p99", "p999", "p9999"};
    printf("  \"%s\": {\"count\": %" PRIu64 ", \"max\": %" PRIu64, name, h->total, h->max);
    for (unsigned i = 0; i < 5; i++) printf(", \"%s\": %" PRIu64, names[i], quantile(h, qs[i]));
    printf(", \"cells\": [");
    const char *sep = "";
    for (unsigned i = 0; i < CELLS; i++)
        if (h->count[i]) printf("%s[%" PRIu64 ", %" PRIu64 "]", sep, cell_top(i), h->count[i]), sep = ", ";
    printf("]}%s\n", after);
}

static long number(const char *v, long lo, long hi, const char *name) {
    char *end;
    errno = 0;
    long n = strtol(v, &end, 10);
    if (errno || end == v || *end || n < lo || n > hi) {
        char why[100];
        snprintf(why, sizeof why, "%s takes %ld to %ld", name, lo, hi);
        usage(why);
    }
    return n;
}

static long micros(struct timeval t) {
    return (long)t.tv_sec * 1000000 + (long)t.tv_usec;
}

/* Sleep until `when` on the monotonic clock. */
static void until(uint64_t when) {
    struct timespec ts = {.tv_sec = (time_t)(when / 1000000000u), .tv_nsec = (long)(when % 1000000000u)};
    while (clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &ts, NULL) == EINTR) {
    }
}

int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1], "--cells")) {
        for (unsigned i = 0; i < CELLS; i++) printf("%" PRIu64 "\n", cell_top(i));
        return 0;
    }
    const char *path = NULL;
    long port = 0, seconds = 5, warmup = 1;
    conns_total = 8;
    for (int i = 1; i < argc; i += 2) {
        if (i + 1 >= argc) usage("an option without its value");
        const char *k = argv[i], *v = argv[i + 1];
        if (!strcmp(k, "--port")) port = number(v, 1, 65535, k);
        else if (!strcmp(k, "--requests")) path = v;
        else if (!strcmp(k, "--conns")) conns_total = (int)number(v, 1, 100000, k);
        else if (!strcmp(k, "--threads")) threads_total = (int)number(v, 1, 64, k);
        else if (!strcmp(k, "--rate")) rate = (double)number(v, 1, 100000000, k);
        else if (!strcmp(k, "--seconds")) seconds = number(v, 1, 3600, k);
        else if (!strcmp(k, "--warmup")) warmup = number(v, 0, 600, k);
        else if (!strcmp(k, "--slow")) slow_total = (int)number(v, 0, 10000, k);
        else if (!strcmp(k, "--slow-ms")) slow_ns = (uint64_t)number(v, 1, 10000, k) * 1000000u;
        else usage("an unknown option");
    }
    if (!path || !port || !rate) usage("--port, --requests and --rate are needed");
    if (threads_total > conns_total) threads_total = conns_total;
    read_requests(path);
    server = (struct sockaddr_in){.sin_family = AF_INET, .sin_port = htons((uint16_t)port),
                                  .sin_addr.s_addr = htonl(INADDR_LOOPBACK)};
    signal(SIGPIPE, SIG_IGN);
    prctl(PR_SET_TIMERSLACK, 1UL, 0UL, 0UL, 0UL);

    struct worker *ws = calloc((size_t)threads_total, sizeof *ws);
    struct histogram *latency = calloc(1, sizeof *latency), *late = calloc(1, sizeof *late);
    if (!ws || !latency || !late) usage("out of memory");
    start_ns = now_ns() + 100000000u;
    measure_from = start_ns + (uint64_t)warmup * 1000000000u;
    measure_to = measure_from + (uint64_t)seconds * 1000000000u;
    end_ns = measure_to + 2000000000u;
    for (int i = 0; i < threads_total; i++) {
        ws[i].index = i;
        ws[i].conns = conns_total / threads_total + (i < conns_total % threads_total);
        ws[i].slow = slow_total / threads_total + (i < slow_total % threads_total);
        if (pthread_create(&ws[i].thread, NULL, work, &ws[i])) usage("pthread_create failed");
    }
    /* The load's own time is taken over the window, as the server's is. */
    struct rusage from, to;
    until(measure_from);
    getrusage(RUSAGE_SELF, &from);
    fputs("window\n", stderr);
    fflush(stderr);
    until(measure_to);
    getrusage(RUSAGE_SELF, &to);
    fputs("end\n", stderr);
    fflush(stderr);
    uint64_t completed = 0, served = 0, answered = 0, sent = 0, wrong = 0, lost = 0, owed = 0, slow_octets = 0,
             slow_paced = 0, into_ns = 0, past_ns = 0;
    const char *why = "";
    for (int i = 0; i < threads_total; i++) {
        pthread_join(ws[i].thread, NULL);
        merge(latency, &ws[i].latency);
        merge(late, &ws[i].late);
        completed += ws[i].completed, served += ws[i].served, answered += ws[i].answered, sent += ws[i].sent;
        wrong += ws[i].wrong, lost += ws[i].lost, owed += ws[i].owed, slow_octets += ws[i].slow_octets;
        slow_paced += ws[i].slow_paced;
        if (ws[i].into_ns > into_ns) into_ns = ws[i].into_ns;
        if (ws[i].past_ns > past_ns) past_ns = ws[i].past_ns;
        if (!*why) why = ws[i].why;
    }
    printf("{\n  \"conns\": %d, \"slow\": %d, \"threads\": %d, \"rate\": %.0f, \"seconds\": %ld, \"warmup\": %ld,\n",
           conns_total, slow_total, threads_total, rate, seconds, warmup);
    printf("  \"requests\": %" PRIu32 ", \"sent\": %" PRIu64 ", \"answered\": %" PRIu64 ", \"served\": %" PRIu64
           ", \"completed\": %" PRIu64 ", \"achieved\": %.1f,\n",
           request_count, sent, answered, served, completed, (double)served / (double)seconds);
    printf("  \"slow_octets\": %" PRIu64 ", \"slow_paced\": %" PRIu64 ", \"wrong\": %" PRIu64 ", \"lost\": %" PRIu64
           ", \"owed\": %" PRIu64 ",\n", slow_octets, slow_paced, wrong, lost, owed);
    printf("  \"into_window_ns\": %" PRIu64 ", \"past_window_ns\": %" PRIu64 ",\n", into_ns, past_ns);
    printf("  \"why\": \"%s\", \"cpu_user_us\": %ld, \"cpu_system_us\": %ld,\n", why,
           micros(to.ru_utime) - micros(from.ru_utime), micros(to.ru_stime) - micros(from.ru_stime));
    print_histogram("latency_ns", latency, ",");
    print_histogram("send_late_ns", late, "");
    printf("}\n");
    return wrong || lost ? 1 : 0;
}
