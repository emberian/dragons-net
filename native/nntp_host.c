/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The NNTP server's host: sockets and the clock for the session's program (DN.Server.Session),
 * which runs as the program's `main` and reaches the host through two external calls on arrays in
 * its heap (docs/decisions/0003-nntp-slice.md). The host knows sockets and the clock and nothing of
 * the protocol.
 *
 *   dn_next  gives out what one poll reported, at most a batch of events, before polling again:
 *            connections taken in turn, input only from a connection that asked for it and has
 *            nothing untaken, at most one input a connection a batch, new connections only while
 *            an index is free. The poll waits until something is ready or the time the program
 *            asked to be woken at; the first batch does not wait, so that the program can recover
 *            its store before the host listens.
 *   dn_emit  carries out each action for the connection's current generation and writes back how
 *            much of each send the kernel took. A graceful close shuts down sending and reads and
 *            drops what still comes, for 30 s at most and 5 s of silence, outside the table. File
 *            jobs go to the workers of jobs.c; their completions come back with a later batch. The
 *            host listens from the first emit that says to, and keeps listening.
 *
 * Every action is checked against the layout; one that breaks it ends the process with status 1.
 * A run the program stops because the host broke the contract ends it with status 3. SIGTERM or
 * SIGINT closes every socket and ends the run inside a call, with status 0. `--spool` and the other
 * options of store.c give the store; a store refused at start ends the host with status 4.
 *
 * `--address A` and `--port N` choose where it listens: by default 127.0.0.1 and a port the kernel
 * picks, printed as JSON on standard output once it listens. `--revision` and `--source` name the revision and the
 * address of the source the replies give; `--send-buffer N` sets SO_SNDBUF on each connection, and
 * each sends its replies at once (TCP_NODELAY). Only for tests, and costing nothing unless given:
 * `--clock-fd N` takes the time from N instead of CLOCK_MONOTONIC — a line with a number of
 * milliseconds sets it, and it moves only then, so nothing waits for it before that — and
 * `--report-fd N` receives a line for each turn: `turn`, the time handed to the program, its events
 * (`open` with the client's port, `recv` with the bytes in hex, `end`, `writable`, `closed`, each
 * with the index and generation), `|`, its actions (`send` with whether to read, how much the kernel
 * took and the bytes, `graceful`, `close`), `| wake` and the time the program asked to be woken at
 * — or, when the program stops the run in that turn, `| stopped` and its code. */
#define _GNU_SOURCE
#include "accept_policy.h"
#include "jobs.h"
#include "session_calls.h"
#include "store.h"
#include <arpa/inet.h>
#include <dirent.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <poll.h>
#include <signal.h>
#include <sys/resource.h>
#include <sys/signalfd.h>
#include <sys/socket.h>
#include <time.h>

enum { CONNS = DN_SESSION_CONNS, LINGERING = 64, LINGER_TOTAL_MS = 30000, LINGER_QUIET_MS = 5000,
       LINGER_READS = 32, ACCEPT_PAUSE_MS = 100, MAX_LINE = 256, TRACE_BYTES = 1 << 18 };

struct conn {
    int fd;          /* -1 when the index is free */
    uint64_t gen;    /* the generation last given out at this index */
    int reading;     /* the last send asked to read and was taken whole; kept until the next send or
                        the end of input */
    int unsent;      /* the last send left bytes: poll for writing */
    int lost;        /* a send failed; the socket is closed, its close still to be reported */
    short ready;     /* what the last poll reported, not yet given out */
    unsigned port;   /* the client's, for the report */
};

struct lingering { int fd; uint64_t until, quiet_until, since; };

static struct conn conns[CONNS];
static struct lingering lingering[LINGERING];
static int listener = -1, signals = -1, clock_fd = -1, report_fd = -1, jobs_done = -1;
static int accept_ready, started, awaiting_emit, carrying, listening;
static unsigned start, listen_port;
static uint64_t now_virtual, accept_paused_until, turn_events, turn_actions, lingered;
static int send_buffer, pausing;
static const char *revision, *source;
static char clock_text[MAX_LINE], trace[TRACE_BYTES];
static size_t clock_len, trace_len;

static uint64_t now_ms(void) {
    if (clock_fd >= 0) return now_virtual;
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) dn_harness("clock_gettime: %s", strerror(errno));
    return (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_nsec / 1000000;
}

static void traced(const char *format, ...) __attribute__((format(printf, 1, 2)));
static void traced(const char *format, ...) {
    va_list args;
    va_start(args, format);
    int n = vsnprintf(trace + trace_len, sizeof trace - trace_len, format, args);
    va_end(args);
    if (n < 0 || (size_t)n >= sizeof trace - trace_len) dn_harness("report: a turn of more than %d bytes", TRACE_BYTES);
    trace_len += (size_t)n;
}

static void traced_bytes(const unsigned char *p, uint64_t n) {
    if (!n) {
        traced(" -");
        return;
    }
    if (trace_len + 1 + 2 * n >= sizeof trace) dn_harness("report: a turn of more than %d bytes", TRACE_BYTES);
    static const char digits[] = "0123456789abcdef";
    trace[trace_len++] = ' ';
    for (uint64_t k = 0; k < n; ++k) {
        trace[trace_len++] = digits[p[k] >> 4];
        trace[trace_len++] = digits[p[k] & 15];
    }
}

/* The events of the batch just given out, as the program finds them. */
static void trace_events(const unsigned char *a, uint64_t now) {
    static const char *const names[] = {[DN_SESSION_OPENED] = "open", [DN_SESSION_RECEIVED] = "recv",
                                        [DN_SESSION_INPUT_ENDED] = "end", [DN_SESSION_WRITABLE] = "writable",
                                        [DN_SESSION_CLOSED] = "closed"};
    trace_len = 0;
    traced("turn %" PRIu64, now);
    for (uint64_t k = 0; k < turn_events; ++k) {
        const unsigned char *slot = a + DN_SESSION_NEXT_EVENTS + k * DN_SESSION_EVENT_SLOT;
        uint64_t kind = dn_word(slot + DN_SESSION_EVENT_KIND), idx = dn_word(slot + DN_SESSION_EVENT_IDX);
        traced(" %s %" PRIu64 " %" PRIu64, names[kind], idx, dn_word(slot + DN_SESSION_EVENT_GEN));
        if (kind == DN_SESSION_OPENED) traced(" %u", conns[idx].port);
        if (kind == DN_SESSION_RECEIVED)
            traced_bytes(slot + DN_SESSION_EVENT_HEAD, dn_word(slot + DN_SESSION_EVENT_LEN));
    }
    traced(" |");
}

static void report_line(void) {
    for (size_t done = 0; done < trace_len;) {
        ssize_t n = write(report_fd, trace + done, trace_len - done);
        if (n < 0 && errno != EINTR) dn_harness("report: %s", strerror(errno));
        if (n > 0) done += (size_t)n;
    }
}

/* The turn's line, once the program has said when to wake it. */
static void report(uint64_t wake) {
    traced(" | wake %" PRIu64 "\n", wake);
    report_line();
}

/* Every socket closed, and the run ends inside the call. */
__attribute__((noreturn)) static void stop_serving(const char *why) {
    for (int i = 0; i < CONNS; ++i)
        if (conns[i].fd >= 0) close(conns[i].fd);
    for (int i = 0; i < LINGERING; ++i)
        if (lingering[i].fd >= 0) close(lingering[i].fd);
    close(listener);
    fprintf(stderr, "stopped: %s\n", why);
    exit(0);
}

static void free_index(struct conn *c) {
    if (c->fd >= 0) close(c->fd);
    c->fd = -1;
    c->reading = c->unsent = c->lost = 0;
    c->ready = 0;
}

static int free_indexes(void) {
    int n = 0;
    for (int i = 0; i < CONNS; ++i) n += conns[i].fd < 0 && !conns[i].lost;
    return n;
}

/* Shut down sending and keep reading, outside the table; with every place taken, the one that has
 * lingered longest gives its place up. */
static void linger(int fd) {
    if (shutdown(fd, SHUT_WR) && errno != ENOTCONN) {
        close(fd);
        return;
    }
    int at = 0;
    for (int i = 0; i < LINGERING; ++i) {
        if (lingering[i].fd < 0) {
            at = i;
            break;
        }
        if (lingering[i].since < lingering[at].since) at = i;
    }
    if (lingering[at].fd >= 0) close(lingering[at].fd);
    uint64_t now = now_ms();
    lingering[at] = (struct lingering){fd, now + LINGER_TOTAL_MS, now + LINGER_QUIET_MS, ++lingered};
}

/* Read and drop what a lingering socket still receives, a bounded number of reads a turn; close it
 * at its end or its time. */
static void drain(struct lingering *l, short revents) {
    if (revents) {
        char sink[512];
        ssize_t n = 0;
        for (int reads = 0; reads < LINGER_READS && (n = recv(l->fd, sink, sizeof sink, MSG_DONTWAIT)) > 0; ++reads)
            l->quiet_until = now_ms() + LINGER_QUIET_MS;
        if (n == 0 || (n < 0 && errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR)) {
            close(l->fd);
            l->fd = -1;
            return;
        }
    }
    uint64_t now = now_ms();
    if (now >= l->until || now >= l->quiet_until) {
        close(l->fd);
        l->fd = -1;
    }
}

/* The lines the clock descriptor has sent, each the time in milliseconds; a line cut between two
 * reads waits for its end. */
static void read_clock(void) {
    ssize_t n = read(clock_fd, clock_text + clock_len, sizeof clock_text - 1 - clock_len);
    if (n == 0) stop_serving("the clock ended");
    if (n < 0) {
        if (errno == EINTR || errno == EAGAIN) return;
        dn_harness("clock: %s", strerror(errno));
    }
    clock_len += (size_t)n;
    char *end;
    while ((end = memchr(clock_text, '\n', clock_len))) {
        *end = 0;
        uint64_t t = dn_parse_u64(clock_text, (UINT64_C(1) << 62) - 1);
        if (t < now_virtual) dn_harness("the clock went back from %" PRIu64 " to %" PRIu64, now_virtual, t);
        now_virtual = t;
        clock_len -= (size_t)(end + 1 - clock_text);
        memmove(clock_text, end + 1, clock_len);
    }
    if (clock_len == sizeof clock_text - 1) dn_harness("clock: a line of %zu bytes", clock_len);
}

/* The poll timeout `timeout` shortened to reach `at`: 0 once it has passed; with a clock from a
 * descriptor, time moves only when the clock says so, so nothing is waited for before that. */
static int until(uint64_t at, int timeout) {
    if (!at) return timeout;
    uint64_t now = now_ms();
    int left;
    if (at <= now) left = 0;
    else if (clock_fd >= 0) return timeout;
    else left = at - now > INT_MAX ? INT_MAX : (int)(at - now);
    return timeout < 0 || left < timeout ? left : timeout;
}

/* Poll until something is ready to give out or `wake` has come. */
static void wait_for(uint64_t wake) {
    for (;;) {
        struct pollfd fds[4 + CONNS + LINGERING];
        int n = 0, conn_at[CONNS], linger_at[LINGERING];
        int paused = now_ms() < accept_paused_until;
        int taking = listening && free_indexes() > 0 && !paused;
        fds[n++] = (struct pollfd){.fd = signals, .events = POLLIN};
        fds[n++] = (struct pollfd){.fd = taking ? listener : -1, .events = POLLIN};
        fds[n++] = (struct pollfd){.fd = clock_fd, .events = POLLIN};
        fds[n++] = (struct pollfd){.fd = jobs_done, .events = POLLIN};
        int timeout = until(wake, -1);
        if (paused) timeout = until(accept_paused_until, timeout);
        for (int i = 0; i < CONNS; ++i) {
            conn_at[i] = -1;
            struct conn *c = &conns[i];
            if (c->fd < 0) continue;
            conn_at[i] = n;
            short wanted = (short)((c->reading ? POLLIN : 0) | (c->unsent ? POLLOUT : 0));
            fds[n++] = (struct pollfd){.fd = c->fd, .events = wanted};
        }
        for (int i = 0; i < LINGERING; ++i) {
            linger_at[i] = -1;
            if (lingering[i].fd < 0) continue;
            linger_at[i] = n;
            fds[n++] = (struct pollfd){.fd = lingering[i].fd, .events = POLLIN};
            uint64_t end = lingering[i].until < lingering[i].quiet_until ? lingering[i].until
                                                                          : lingering[i].quiet_until;
            timeout = until(end, timeout);
        }
        int got = poll(fds, (nfds_t)n, timeout);
        if (got < 0) {
            if (errno == EINTR) continue;
            dn_harness("poll: %s", strerror(errno));
        }
        if (fds[0].revents) stop_serving("a signal");
        if (fds[2].revents) read_clock();
        for (int i = 0; i < LINGERING; ++i)
            if (linger_at[i] >= 0) drain(&lingering[i], fds[linger_at[i]].revents);
        int news = fds[1].revents != 0;
        if (news) accept_ready = 1;
        news |= dn_jobs_ready();
        for (int i = 0; i < CONNS; ++i) {
            if (conn_at[i] < 0) continue;
            conns[i].ready = fds[conn_at[i]].revents;
            news |= conns[i].ready != 0;
        }
        for (int i = 0; i < CONNS; ++i) news |= conns[i].lost;
        if (news || (wake && now_ms() >= wake)) return;
    }
}

/* One more event into the batch. */
static void event(unsigned char *a, uint64_t kind, int idx, uint64_t gen, uint64_t len) {
    unsigned char *slot = a + DN_SESSION_NEXT_EVENTS + turn_events * DN_SESSION_EVENT_SLOT;
    dn_put_word(slot + DN_SESSION_EVENT_KIND, kind);
    dn_put_word(slot + DN_SESSION_EVENT_IDX, (uint64_t)idx);
    dn_put_word(slot + DN_SESSION_EVENT_GEN, gen);
    dn_put_word(slot + DN_SESSION_EVENT_LEN, len);
    dn_put_word(slot + DN_SESSION_EVENT_POST, 0);
    ++turn_events;
}

/* What one connection has to report, if anything. */
static void give_out(unsigned char *a, int i) {
    struct conn *c = &conns[i];
    if (c->lost) {
        event(a, DN_SESSION_CLOSED, i, c->gen, 0);
        free_index(c);
        return;
    }
    short r = c->ready;
    c->ready = 0;
    if (c->fd < 0 || !r) return;
    if ((r & POLLIN) && c->reading) {
        unsigned char *slot = a + DN_SESSION_NEXT_EVENTS + turn_events * DN_SESSION_EVENT_SLOT;
        ssize_t n = recv(c->fd, slot + DN_SESSION_EVENT_HEAD, DN_SESSION_DATA, MSG_DONTWAIT);
        if (n > 0) {
            event(a, DN_SESSION_RECEIVED, i, c->gen, (uint64_t)n);
        } else if (n == 0) {
            c->reading = 0;
            event(a, DN_SESSION_INPUT_ENDED, i, c->gen, 0);
        } else if (errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR) {
            event(a, DN_SESSION_CLOSED, i, c->gen, 0);
            free_index(c);
        }
        return;
    }
    if (r & (POLLERR | POLLHUP | POLLNVAL)) {
        event(a, DN_SESSION_CLOSED, i, c->gen, 0);
        free_index(c);
        return;
    }
    if ((r & POLLOUT) && c->unsent) {
        c->unsent = 0;
        event(a, DN_SESSION_WRITABLE, i, c->gen, 0);
    }
}

static void take_connections(unsigned char *a, uint64_t now) {
    while (accept_ready && turn_events < DN_SESSION_BATCH && free_indexes() > 0) {
        struct sockaddr_storage peer;
        socklen_t peer_len = sizeof peer;
        int fd = accept4(listener, (struct sockaddr *)&peer, &peer_len, SOCK_NONBLOCK | SOCK_CLOEXEC);
        if (fd < 0) {
            int code = errno;
            switch (dn_accept_action(code)) {
            case DN_ACCEPT_RETRY:
                if (code == EAGAIN || code == EWOULDBLOCK) accept_ready = 0;
                continue;
            case DN_ACCEPT_PAUSE:
                if (!pausing) fprintf(stderr, "accept: %s; pausing\n", strerror(code));
                pausing = 1;
                accept_ready = 0;
                accept_paused_until = now + ACCEPT_PAUSE_MS;
                return;
            case DN_ACCEPT_FATAL:
            default:
                dn_harness("accept: %s", strerror(code));
            }
        }
        pausing = 0;
        static const int one = 1;
        if (setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one) ||
            (send_buffer && setsockopt(fd, SOL_SOCKET, SO_SNDBUF, &send_buffer, sizeof send_buffer))) {
            close(fd);
            continue;
        }
        int i = 0;
        while (conns[i].fd >= 0 || conns[i].lost) ++i;
        in_port_t port = peer.ss_family == AF_INET ? ((struct sockaddr_in *)&peer)->sin_port
                                                   : ((struct sockaddr_in6 *)&peer)->sin6_port;
        conns[i] = (struct conn){.fd = fd, .gen = conns[i].gen + 1, .port = ntohs(port)};
        event(a, DN_SESSION_OPENED, i, conns[i].gen, 0);
        dn_put_word(a + DN_SESSION_NEXT_EVENTS + (turn_events - 1) * DN_SESSION_EVENT_SLOT + DN_SESSION_EVENT_POST,
                    (uint64_t)dn_store_may_post(&peer));
    }
}

void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen) {
    dn_session_call(c, clen, a, alen, DN_SESSION_NEXT_OFF, DN_SESSION_NEXT_LEN, "dn_next");
    if (awaiting_emit) dn_violation("dn_next: the program fetched again without handing over its answers");
    uint64_t wake = 0;
    int first = !started;
    if (started) {
        wake = dn_word(a + DN_SESSION_NEXT_WAKE);
        if (report_fd >= 0) report(wake);
    }
    started = 1;
    if (!carrying && !first) wait_for(wake);
    uint64_t now = now_ms();
    turn_events = 0;
    for (unsigned k = 0; k < CONNS && turn_events < DN_SESSION_BATCH; ++k) give_out(a, (int)((start + k) % CONNS));
    start = (start + 1) % CONNS;
    take_connections(a, now);
    carrying = 0;
    for (int i = 0; i < CONNS; ++i) carrying |= conns[i].ready != 0 || conns[i].lost;
    carrying |= accept_ready && free_indexes() > 0;
    dn_jobs_give(a);
    dn_put_word(a + DN_SESSION_NEXT_COUNT, turn_events);
    dn_put_word(a + DN_SESSION_NEXT_CLOCK, now);
    size_t rl = strlen(revision), sl = strlen(source);
    dn_put_word(a + DN_SESSION_NEXT_REV_LEN, rl);
    memcpy(a + DN_SESSION_NEXT_REV, revision, rl);
    dn_put_word(a + DN_SESSION_NEXT_SRC_LEN, sl);
    memcpy(a + DN_SESSION_NEXT_SRC, source, sl);
    dn_store_fill(a);
    if (report_fd >= 0) trace_events(a, now);
    awaiting_emit = 1;
}

/* Listen, and say where. */
static void start_listening(void) {
    if (listen(listener, CONNS)) dn_harness("listen: %s", strerror(errno));
    listening = 1;
    printf("{\"port\":%u,\"conns\":%d}\n", listen_port, CONNS);
    if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
}

/* The actions of the turn, with what the kernel took of each send. */
static void trace_actions(const unsigned char *a) {
    for (int k = 0; k < CONNS; ++k) {
        const unsigned char *slot = a + DN_SESSION_EMIT_ACTIONS + (size_t)k * DN_SESSION_ACTION_SLOT;
        uint64_t kind = dn_word(slot + DN_SESSION_ACTION_KIND), gen = dn_word(slot + DN_SESSION_ACTION_GEN);
        if (kind == DN_SESSION_SEND) {
            traced(" send %d %" PRIu64 " %" PRIu64 " %" PRIu64, k, gen, dn_word(slot + DN_SESSION_ACTION_READ),
                   dn_word(slot + DN_SESSION_ACTION_TAKEN));
            traced_bytes(slot + DN_SESSION_ACTION_HEAD, dn_word(slot + DN_SESSION_ACTION_LEN));
        } else if (kind) {
            traced(" %s %d %" PRIu64, kind == DN_SESSION_CLOSE_GRACEFULLY ? "graceful" : "close", k, gen);
        }
    }
}

void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen) {
    dn_session_call(c, clen, a, alen, DN_SESSION_EMIT_OFF, DN_SESSION_EMIT_LEN, "dn_emit");
    if (!awaiting_emit) dn_violation("dn_emit: the program answered without fetching");
    uint64_t count = dn_word(a + DN_SESSION_EMIT_COUNT);
    turn_actions = 0;
    for (int k = 0; k < CONNS; ++k) {
        unsigned char *slot = a + DN_SESSION_EMIT_ACTIONS + (size_t)k * DN_SESSION_ACTION_SLOT;
        uint64_t kind = dn_word(slot + DN_SESSION_ACTION_KIND);
        if (kind == 0) continue;
        ++turn_actions;
        uint64_t idx = dn_word(slot + DN_SESSION_ACTION_IDX), gen = dn_word(slot + DN_SESSION_ACTION_GEN);
        uint64_t len = dn_word(slot + DN_SESSION_ACTION_LEN), read = dn_word(slot + DN_SESSION_ACTION_READ);
        if (idx != (uint64_t)k) dn_violation("dn_emit: the slot of connection %d holds an action for %" PRIu64, k, idx);
        if (kind != DN_SESSION_SEND && kind != DN_SESSION_CLOSE_GRACEFULLY && kind != DN_SESSION_CLOSE_NOW)
            dn_violation("dn_emit: an action of kind %" PRIu64, kind);
        if (kind == DN_SESSION_SEND && (len > DN_SESSION_DATA || read > 1))
            dn_violation("dn_emit: a send of %" PRIu64 " bytes, reading %" PRIu64, len, read);
        struct conn *cn = &conns[k];
        if (cn->fd < 0 || cn->gen != gen) {
            /* not this connection's: its close is reported, or about to be */
            if (kind == DN_SESSION_SEND) dn_put_word(slot + DN_SESSION_ACTION_TAKEN, 0);
            continue;
        }
        if (kind == DN_SESSION_SEND) {
            ssize_t n = len ? send(cn->fd, slot + DN_SESSION_ACTION_HEAD, len, MSG_NOSIGNAL | MSG_DONTWAIT) : 0;
            uint64_t taken = n > 0 ? (uint64_t)n : 0;
            if (n < 0 && errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR) {
                close(cn->fd);
                cn->fd = -1;
                cn->lost = 1;
                carrying = 1;
            }
            dn_put_word(slot + DN_SESSION_ACTION_TAKEN, taken);
            cn->unsent = !cn->lost && taken < len;
            cn->reading = !cn->lost && read && taken == len;
        } else {
            int fd = cn->fd;
            cn->fd = -1;
            free_index(cn);
            if (kind == DN_SESSION_CLOSE_GRACEFULLY) linger(fd);
            else close(fd);
        }
    }
    dn_jobs_take(a);
    if (turn_actions != count)
        dn_violation("dn_emit: %" PRIu64 " actions counted, %" PRIu64 " in the slots", count, turn_actions);
    uint64_t listen_word = dn_word(a + DN_SESSION_EMIT_LISTEN);
    if (listen_word > 1 || (listening && !listen_word))
        dn_violation("dn_emit: listening %" PRIu64 ", having listened %d", listen_word, listening);
    if (listen_word && !listening) start_listening();
    if (report_fd >= 0) trace_actions(a);
    awaiting_emit = 0;
}

__attribute__((noreturn)) static void on_exit_run(int code) {
    if (code != 0) dn_violation("the run ended for want of stack or heap (code %d)", code);
    uint64_t stop = dn_word(dn_heap_at(DN_SESSION_OWN_OFF + DN_SESSION_OWN_STOP));
    if (stop == 0) dn_violation("the program ended its run without a cause");
    fprintf(stderr, "the program stopped the run: code %" PRIu64 "\n", stop);
    if (report_fd >= 0 && started) {
        traced(" | stopped %" PRIu64 "\n", stop);
        report_line();
    }
    exit(3);
}

/* How many descriptors are open, not counting the one that lists them. */
static int open_descriptors(void) {
    DIR *d = opendir("/proc/self/fd");
    if (!d) dn_harness("/proc/self/fd: %s", strerror(errno));
    int n = 0;
    for (struct dirent *e; (e = readdir(d));) n += e->d_name[0] != '.';
    closedir(d);
    return n - 1;
}

/* A descriptor the host was started with, open and not one of the standard three. */
static int descriptor(const char *text) {
    int fd = (int)dn_parse_u64(text, INT_MAX);
    if (fd < 3 || fcntl(fd, F_GETFD) < 0) dn_harness("not an open descriptor above 2: %s", text);
    return fd;
}

/* What the replies can name: 1 to `max` visible bytes, as the program requires. */
static void identity(const char *name, const char *value, size_t max) {
    size_t n = value ? strlen(value) : 0;
    if (n < 1 || n > max) dn_harness("%s needs 1 to %zu bytes", name, max);
    for (size_t i = 0; i < n; ++i)
        if (value[i] < 33 || value[i] > 126) dn_harness("%s may hold visible ASCII only", name);
}

int main(int argc, char **argv) {
    const char *address = "127.0.0.1";
    unsigned port = 0;
    for (int i = 1; i < argc; i += 2) {
        if (i + 1 == argc) dn_harness("%s needs a value", argv[i]);
        const char *name = argv[i], *value = argv[i + 1];
        if (!strcmp(name, "--port")) port = (unsigned)dn_parse_u64(value, 65535);
        else if (!strcmp(name, "--address")) address = value;
        else if (!strcmp(name, "--revision")) revision = value;
        else if (!strcmp(name, "--source")) source = value;
        else if (!strcmp(name, "--send-buffer")) send_buffer = (int)dn_parse_u64(value, 1 << 20);
        else if (!strcmp(name, "--clock-fd")) clock_fd = descriptor(value);
        else if (!strcmp(name, "--report-fd")) report_fd = descriptor(value);
        else if (!dn_store_option(name, value)) dn_harness("unknown option %s", name);
    }
    identity("--revision", revision, DN_SESSION_REV_MAX);
    identity("--source", source, DN_SESSION_SRC_MAX);
    dn_store_start();
    jobs_done = dn_jobs_start(dn_store_spool());
    if (clock_fd >= 0) now_virtual = 1;
    for (int i = 0; i < CONNS; ++i) conns[i].fd = -1;
    for (int i = 0; i < LINGERING; ++i) lingering[i].fd = -1;

    sigset_t mask;
    sigemptyset(&mask);
    sigaddset(&mask, SIGTERM);
    sigaddset(&mask, SIGINT);
    if (sigprocmask(SIG_BLOCK, &mask, NULL)) dn_harness("sigprocmask: %s", strerror(errno));
    signals = signalfd(-1, &mask, SFD_CLOEXEC | SFD_NONBLOCK);
    if (signals < 0) dn_harness("signalfd: %s", strerror(errno));
    if (signal(SIGPIPE, SIG_IGN) == SIG_ERR) dn_harness("signal: %s", strerror(errno));

    struct sockaddr_storage where = {0};
    socklen_t where_len;
    struct sockaddr_in *v4 = (struct sockaddr_in *)&where;
    struct sockaddr_in6 *v6 = (struct sockaddr_in6 *)&where;
    if (inet_pton(AF_INET, address, &v4->sin_addr) == 1) {
        v4->sin_family = AF_INET;
        v4->sin_port = htons((uint16_t)port);
        where_len = sizeof *v4;
    } else if (inet_pton(AF_INET6, address, &v6->sin6_addr) == 1) {
        v6->sin6_family = AF_INET6;
        v6->sin6_port = htons((uint16_t)port);
        where_len = sizeof *v6;
    } else {
        dn_harness("not an address: %s", address);
    }
    listener = socket(where.ss_family, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
    if (listener < 0) dn_harness("socket: %s", strerror(errno));
    int one = 1;
    if (setsockopt(listener, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one))
        dn_harness("setsockopt: %s", strerror(errno));
    if (where.ss_family == AF_INET6 && setsockopt(listener, IPPROTO_IPV6, IPV6_V6ONLY, &one, sizeof one))
        dn_harness("setsockopt: %s", strerror(errno));
    if (bind(listener, (struct sockaddr *)&where, where_len)) dn_harness("bind: %s", strerror(errno));
    if (getsockname(listener, (struct sockaddr *)&where, &where_len)) dn_harness("getsockname: %s", strerror(errno));
    listen_port = ntohs(where.ss_family == AF_INET ? v4->sin_port : v6->sin6_port);
    /* Descriptors are handed out lowest first: with those open now, the table and the lingering
     * sockets have to fit under the limit. */
    struct rlimit files;
    if (getrlimit(RLIMIT_NOFILE, &files)) dn_harness("getrlimit: %s", strerror(errno));
    int in_use = open_descriptors();
    if (files.rlim_cur < (rlim_t)in_use + CONNS + LINGERING)
        dn_harness("too few file descriptors: %llu, and %d open", (unsigned long long)files.rlim_cur, in_use);

    dn_runtime_setup_heap(DN_SESSION_HEAP_BYTES);
    dn_runtime_header();
    dn_runtime_on_exit = on_exit_run;
    cml_main();
    dn_violation("the program returned to its host, which a build without --main_return cannot do");
}
