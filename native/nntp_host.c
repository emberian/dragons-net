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
 * A run the program stops because the host broke the contract ends it with status 3; one it stops
 * because recovery refused the store, or a file job of recovery failed, with status 4. SIGTERM or
 * SIGINT closes every socket, drops the file jobs not begun, waits for those running, 30 s at most,
 * and ends the run inside a call, with status 0. `--spool` and the other
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
 * — or, when the program stops the run in that turn, `| stopped` and its code.
 *
 * Settings come as options or, with `--config FILE`, from a file: a setting a line, an option's name
 * without its dashes, white space, and its value; blank lines and those starting with `#` are
 * skipped, and a file may not give `config`, `check-config` or the test's descriptors. A setting
 * unknown, without a value, or given twice where it is taken once ends the host with status 2, the
 * file's line named. `--check-config FILE` takes them as `--config` does, checks them together and
 * that the store's directories open, writes them as JSON on standard output and ends with status 0,
 * starting nothing. Started by systemd with one socket (LISTEN_PID naming the process, LISTEN_FDS 1),
 * the host listens on descriptor 3 instead, so that it needs no privilege for port 119; `--address`
 * and `--port` are then refused. With `--tls-cert FILE` and `--tls-key FILE`, PEM files, every
 * connection speaks TLS from its first octet (RFC 8143, port 563) through libssl (tls.c), and the
 * program learns of one only once its handshake is done; a handshake not done in 10 s, or that
 * fails, closes the connection unreported. SIGUSR1 writes the counters to stderr, and so does a stop on a signal: the
 * connections taken, how they ended, the octets read and sent, the pauses in accepting, the file
 * jobs and those that failed for want of space, on an I/O error or otherwise; no address, name or
 * octet a client sent. */
#define _GNU_SOURCE
#include "accept_policy.h"
#include "faults.h"
#include "jobs.h"
#include "session_calls.h"
#include "store.h"
#include "tls.h"
#include <arpa/inet.h>
#include <dirent.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <poll.h>
#include <signal.h>
#include <malloc.h>
#include <sys/resource.h>
#include <sys/signalfd.h>
#include <sys/socket.h>
#include <time.h>

enum { CONNS = DN_SESSION_CONNS, LINGERING = 64, LINGER_TOTAL_MS = 30000, LINGER_QUIET_MS = 5000,
       LINGER_READS = 32, ACCEPT_PAUSE_MS = 100, MAX_LINE = 256, TRACE_BYTES = 1 << 18, DRAIN_MS = 30000,
       CONFIG_MAX = 1 << 16, LISTEN_FD = 3, HANDSHAKE_MS = 10000 };

struct conn {
    int fd;          /* -1 when the index is free */
    uint64_t gen;    /* the generation last given out at this index; at DN_SESSION_GEN_LIMIT the index
                        is used no more */
    int reading;     /* the last send asked to read and was taken whole; kept until the next send or
                        the end of input */
    int unsent;      /* the last send left bytes: poll for writing */
    int lost;        /* a send failed; the socket is closed, its close still to be reported */
    short ready;     /* what the last poll reported, not yet given out */
    unsigned port;   /* the client's, for the report */
    struct dn_tls *tls;          /* with a certificate set, the connection's TLS */
    int handshaking;             /* its handshake is not done: the program has not been told of it */
    int handshaken;              /* its handshake is done and the program is still to be told */
    short tls_wants;             /* what TLS waits for before the read, write or handshake can go on */
    uint64_t handshake_until;    /* when a handshake not done by then ends the connection */
    struct sockaddr_storage peer; /* the client, for the store once the handshake is done */
};

struct lingering { int fd; uint64_t until, quiet_until, since; };

static struct conn conns[CONNS];
static struct lingering lingering[LINGERING];
static int listener = -1, signals = -1, clock_fd = -1, report_fd = -1, jobs_done = -1;
static int accept_ready, started, awaiting_emit, carrying, listening;
static unsigned start, listen_port;
static uint64_t now_virtual, accept_paused_until, turn_events, turn_actions, lingered;
static int send_buffer, pausing, checking;
static const char *revision, *source, *address = "127.0.0.1", *tls_cert, *tls_key;
static unsigned port_wanted;
/* While a file's settings are taken, where the one taken is. */
static const char *setting_at = "";
/* What the counters count; a connection ended by neither action was ended by its client or the
 * network. */
static struct { uint64_t accepted, ended, graceful, abrupt, in, out, pauses, handshakes_failed; } counted;
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

/* The test build says how many octets the heap allocator has given out, and the most the process
 * has held resident since it began (VmHWM: getrusage's maximum takes in what its parent held before
 * exec): without TLS nothing is allocated once it serves; libssl allocates for each TLS connection. */
static void say_allocated(const char *when) {
#ifdef FIU_ENABLE
    long peak = -1;
    FILE *status = fopen("/proc/self/status", "re");
    if (!status) dn_harness("/proc/self/status: %s", strerror(errno));
    char line[256];
    while (fgets(line, sizeof line, status))
        if (sscanf(line, "VmHWM: %ld kB", &peak) == 1) break;
    fclose(status);
    fprintf(stderr, "%s: %zu octets allocated, %ld kB resident at most\n", when, mallinfo2().uordblks, peak);
#else
    (void)when;
#endif
}

static void say_counters(const char *when) {
    uint64_t jobs[4];
    dn_jobs_counted(jobs);
    fprintf(stderr,
            "%s: %" PRIu64 " connections, %" PRIu64 " closed gracefully, %" PRIu64 " at once, %" PRIu64
            " by the client or the network; %" PRIu64 " TLS handshakes failed; %" PRIu64 " octets in, %" PRIu64
            " out; %" PRIu64 " accept pauses; %" PRIu64 " file jobs, %" PRIu64 " failed for want of space, %" PRIu64
            " on I/O errors, %" PRIu64 " otherwise\n",
            when, counted.accepted, counted.graceful, counted.abrupt,
            counted.ended - counted.graceful - counted.abrupt - counted.handshakes_failed, counted.handshakes_failed,
            counted.in, counted.out, counted.pauses, jobs[0], jobs[1], jobs[2], jobs[3]);
}

/* Every socket closed, the file jobs drained, and the run ends inside the call. */
__attribute__((noreturn)) static void stop_serving(const char *why) {
    for (int i = 0; i < CONNS; ++i)
        if (conns[i].fd >= 0) close(conns[i].fd);
    for (int i = 0; i < LINGERING; ++i)
        if (lingering[i].fd >= 0) close(lingering[i].fd);
    close(listener);
    if (jobs_done >= 0) {
        int counts[3];
        dn_jobs_drain(DRAIN_MS, counts);
        fprintf(stderr, "at the stop: %d jobs run out, %d dropped before they began, %d still running\n", counts[0],
                counts[1], counts[2]);
    }
    say_allocated("at the stop");
    say_counters("at the stop");
    fprintf(stderr, "stopped: %s\n", why);
    exit(0);
}

/* The connection's TLS ended, saying so to the client if `gracefully`. */
static void end_tls(struct conn *c, int gracefully) {
    if (c->tls) dn_tls_end(c->tls, gracefully);
    c->tls = NULL;
    c->handshaking = 0;
    c->tls_wants = 0;
}

static int handshake(int i, short r);
static int take_handshakes(uint64_t now);

static void free_index(struct conn *c) {
    ++counted.ended;
    end_tls(c, 0);
    if (c->fd >= 0) close(c->fd);
    c->fd = -1;
    c->reading = c->unsent = c->lost = c->handshaken = 0;
    c->ready = 0;
}

/* A step of the handshake of connection `i`, which the poll found `r`. Done, the connection is the
 * program's to be told of; failed or past its time, it ends without the program having known of it,
 * so a handshake never takes a turn of the program. The first failure of a run says why, the others
 * are counted. Says whether the handshake is done. */
static int handshake(int i, short r) {
    struct conn *c = &conns[i];
    enum dn_tls_state state = r ? dn_tls_handshake(c->tls)
                                : c->tls_wants == POLLIN ? DN_TLS_WANT_READ : DN_TLS_WANT_WRITE;
    if (state == DN_TLS_DONE) {
        c->handshaking = 0;
        c->handshaken = 1;
        c->tls_wants = 0;
        return 1;
    }
    if ((state == DN_TLS_WANT_READ || state == DN_TLS_WANT_WRITE) && now_ms() < c->handshake_until) {
        c->tls_wants = state == DN_TLS_WANT_READ ? POLLIN : POLLOUT;
        return 0;
    }
    if (!counted.handshakes_failed++)
        fprintf(stderr, "TLS: a handshake %s; later ones are counted only\n",
                state == DN_TLS_WANT_READ || state == DN_TLS_WANT_WRITE ? "was not done in time" : dn_tls_reason());
    free_index(c);
    return 0;
}

static int usable(int i) {
    return conns[i].fd < 0 && !conns[i].lost && conns[i].gen < DN_SESSION_GEN_LIMIT;
}

static int free_indexes(void) {
    int n = 0;
    for (int i = 0; i < CONNS; ++i) n += usable(i);
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
        /* Octets TLS has taken off a socket and not yet given out no poll reports. */
        int held = 0;
        for (int i = 0; i < CONNS; ++i) {
            conn_at[i] = -1;
            struct conn *c = &conns[i];
            if (c->fd < 0) continue;
            if (c->handshaking) timeout = until(c->handshake_until, timeout);
            if (c->tls && !c->handshaking && c->reading && dn_tls_pending(c->tls)) {
                c->ready |= POLLIN;
                held = 1;
            }
            conn_at[i] = n;
            short wanted = c->handshaking ? c->tls_wants
                                          : (short)((c->reading ? POLLIN : 0) | (c->unsent ? POLLOUT : 0) | c->tls_wants);
            /* A send that waits for the peer to send waits for that alone, or it would spin. */
            if (c->unsent && c->tls_wants == POLLIN) wanted = POLLIN;
            fds[n++] = (struct pollfd){.fd = c->fd, .events = wanted};
        }
        if (held) return;
        for (int i = 0; i < LINGERING; ++i) {
            linger_at[i] = -1;
            if (lingering[i].fd < 0) continue;
            linger_at[i] = n;
            fds[n++] = (struct pollfd){.fd = lingering[i].fd, .events = POLLIN};
            uint64_t end = lingering[i].until < lingering[i].quiet_until ? lingering[i].until
                                                                          : lingering[i].quiet_until;
            timeout = until(end, timeout);
        }
        /* The test build's `dn/poll` fails the poll with the error number it was enabled with. */
        int got = DN_FAULT("dn/poll") ? -1 : poll(fds, (nfds_t)n, timeout);
        if (got < 0) {
            if (errno == EINTR) continue;
            dn_harness("poll: %s", strerror(errno));
        }
        if (fds[0].revents) {
            struct signalfd_siginfo si;
            ssize_t r = read(signals, &si, sizeof si);
            if (r == (ssize_t)sizeof si && si.ssi_signo == SIGUSR1) say_counters("counters");
            else if (r >= 0 || (errno != EAGAIN && errno != EINTR)) stop_serving("a signal");
        }
        if (fds[2].revents) read_clock();
        for (int i = 0; i < LINGERING; ++i)
            if (linger_at[i] >= 0) drain(&lingering[i], fds[linger_at[i]].revents);
        int news = 0;
        if (fds[1].revents && tls_cert) news |= take_handshakes(now_ms());
        else if (fds[1].revents) news = accept_ready = 1;
        news |= dn_jobs_ready();
        uint64_t now = now_ms();
        for (int i = 0; i < CONNS; ++i) {
            if (conn_at[i] < 0) continue;
            short revents = fds[conn_at[i]].revents;
            if (conns[i].handshaking) {
                if (revents || now >= conns[i].handshake_until) news |= handshake(i, revents);
                continue;
            }
            conns[i].ready = revents;
            news |= revents != 0;
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

/* The connection opened, as the program learns of it. */
static void opened(unsigned char *a, int i) {
    event(a, DN_SESSION_OPENED, i, conns[i].gen, 0);
    dn_store_log_opened(&conns[i].peer);
    dn_put_word(a + DN_SESSION_NEXT_EVENTS + (turn_events - 1) * DN_SESSION_EVENT_SLOT + DN_SESSION_EVENT_POST,
                (uint64_t)dn_store_may_post(&conns[i].peer));
}

/* What one connection has to report, if anything. */
static void give_out(unsigned char *a, int i) {
    struct conn *c = &conns[i];
    if (c->handshaken) {
        c->handshaken = 0;
        opened(a, i);
        return;
    }
    if (c->lost) {
        event(a, DN_SESSION_CLOSED, i, c->gen, 0);
        free_index(c);
        return;
    }
    short r = c->ready;
    c->ready = 0;
    if (c->fd < 0 || c->handshaking || !r) return;
    if (c->tls && c->reading && (r & (POLLIN | c->tls_wants | POLLERR | POLLHUP))) {
        unsigned char *slot = a + DN_SESSION_NEXT_EVENTS + turn_events * DN_SESSION_EVENT_SLOT;
        enum dn_tls_state state;
        size_t n = dn_tls_read(c->tls, slot + DN_SESSION_EVENT_HEAD, DN_SESSION_DATA, &state);
        c->tls_wants = state == DN_TLS_WANT_WRITE ? POLLOUT : 0;
        if (state == DN_TLS_DONE) {
            counted.in += n;
            event(a, DN_SESSION_RECEIVED, i, c->gen, n);
        } else if (state == DN_TLS_ENDED) {
            c->reading = 0;
            event(a, DN_SESSION_INPUT_ENDED, i, c->gen, 0);
        } else if (state == DN_TLS_FAILED) {
            event(a, DN_SESSION_CLOSED, i, c->gen, 0);
            free_index(c);
        }
        return;
    }
    if ((r & POLLIN) && c->reading) {
        unsigned char *slot = a + DN_SESSION_NEXT_EVENTS + turn_events * DN_SESSION_EVENT_SLOT;
        ssize_t n = recv(c->fd, slot + DN_SESSION_EVENT_HEAD, DN_SESSION_DATA, MSG_DONTWAIT);
        if (n > 0) {
            counted.in += (uint64_t)n;
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
    if ((r & (POLLOUT | c->tls_wants)) && c->unsent) {
        c->unsent = 0;
        c->tls_wants = 0;
        event(a, DN_SESSION_WRITABLE, i, c->gen, 0);
    }
}

/* One connection taken from the listener: its index, -1 when none was taken, or -2 when accepting
 * pauses, descriptors or memory having run out. `accept_ready` is cleared once the listener has none.
 * Over TLS the connection's handshake begins, and the program learns of it once it is done. */
static int accept_next(uint64_t now) {
    struct sockaddr_storage peer;
    socklen_t peer_len = sizeof peer;
    int fd = accept4(listener, (struct sockaddr *)&peer, &peer_len, SOCK_NONBLOCK | SOCK_CLOEXEC);
    if (fd < 0) {
        int code = errno;
        switch (dn_accept_action(code)) {
        case DN_ACCEPT_RETRY:
            if (code == EAGAIN || code == EWOULDBLOCK) accept_ready = 0;
            return -1;
        case DN_ACCEPT_PAUSE:
            ++counted.pauses;
            if (!pausing) fprintf(stderr, "accept: %s; pausing\n", strerror(code));
            pausing = 1;
            accept_ready = 0;
            accept_paused_until = now + ACCEPT_PAUSE_MS;
            return -2;
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
        return -1;
    }
    int i = 0;
    while (!usable(i)) ++i;
    /* The test build's `dn/generation` takes the index's count of generations up to its number. */
    uint64_t past;
    if (DN_FAULT_INFO("dn/generation", past) && conns[i].gen < past && past < DN_SESSION_GEN_LIMIT)
        conns[i].gen = past;
    in_port_t port = peer.ss_family == AF_INET ? ((struct sockaddr_in *)&peer)->sin_port
                                               : ((struct sockaddr_in6 *)&peer)->sin6_port;
    struct dn_tls *tls = NULL;
    if (tls_cert && !(tls = dn_tls_new(fd))) {
        close(fd);
        return -1;
    }
    conns[i] = (struct conn){.fd = fd, .gen = conns[i].gen + 1, .port = ntohs(port), .tls = tls, .peer = peer,
                             .handshaking = tls != NULL, .handshake_until = now + HANDSHAKE_MS};
    ++counted.accepted;
    if (conns[i].gen == DN_SESSION_GEN_LIMIT) fprintf(stderr, "index %d given out at its last generation\n", i);
    return i;
}

/* Over TCP, the connections the listener has, each reported open in the batch. */
static void take_connections(unsigned char *a, uint64_t now) {
    while (!tls_cert && accept_ready && turn_events < DN_SESSION_BATCH && free_indexes() > 0) {
        int i = accept_next(now);
        if (i == -2) return;
        if (i >= 0) opened(a, i);
    }
}

/* Over TLS, the connections the listener has, taken while the host waits, so that one whose handshake
 * is not done takes no turn of the program. Says whether a handshake is done. */
static int take_handshakes(uint64_t now) {
    int done = 0;
    accept_ready = 1;
    while (accept_ready && free_indexes() > 0) {
        int i = accept_next(now);
        if (i == -2) break;
        if (i >= 0) done |= handshake(i, POLLIN);
    }
    accept_ready = 0;
    return done;
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
    for (int i = 0; i < CONNS; ++i) carrying |= conns[i].ready != 0 || conns[i].lost || conns[i].handshaken;
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
    say_allocated("serving");
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
            int failed;
            uint64_t taken;
            if (cn->tls) {
                enum dn_tls_state state = DN_TLS_DONE;
                taken = len ? dn_tls_write(cn->tls, slot + DN_SESSION_ACTION_HEAD, len, &state) : 0;
                cn->tls_wants = state == DN_TLS_WANT_READ ? POLLIN : 0;
                failed = state == DN_TLS_ENDED || state == DN_TLS_FAILED;
            } else {
                ssize_t n = len ? send(cn->fd, slot + DN_SESSION_ACTION_HEAD, len, MSG_NOSIGNAL | MSG_DONTWAIT) : 0;
                taken = n > 0 ? (uint64_t)n : 0;
                failed = n < 0 && errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR;
            }
            counted.out += taken;
            if (failed) {
                end_tls(cn, 0);
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
            end_tls(cn, kind == DN_SESSION_CLOSE_GRACEFULLY);
            cn->fd = -1;
            free_index(cn);
            if (kind == DN_SESSION_CLOSE_GRACEFULLY) {
                ++counted.graceful;
                linger(fd);
            } else {
                ++counted.abrupt;
                close(fd);
            }
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
    if (stop == DN_SESSION_STORE_REFUSED || stop == DN_SESSION_RECOVERY_FAILED)
        dn_store_recovery_stopped(stop, dn_heap_at(DN_SESSION_REC_OFF),
                                  dn_word(dn_heap_at(DN_SESSION_DRV_OFF + DN_SESSION_D_CLASS)));
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

static void read_settings(const char *path);

/* Settings taken once at most; the file of settings, given either way, counts as one. */
enum { GIVEN_PORT, GIVEN_ADDRESS, GIVEN_SETTINGS, GIVEN_ONCE = 13 };
static const char *const taken_once[GIVEN_ONCE] = {
    [GIVEN_PORT] = "--port", [GIVEN_ADDRESS] = "--address", [GIVEN_SETTINGS] = "--config", "--revision", "--source",
    "--send-buffer", "--clock-fd", "--report-fd", "--spool", "--run-dir", "--path-identity", "--tls-cert",
    "--tls-key"};
static int given[sizeof taken_once / sizeof *taken_once];

/* A number of the setting `name`, the file's line named. */
static uint64_t number(const char *name, const char *value, uint64_t max) {
    char *end;
    errno = 0;
    unsigned long long n = strtoull(value, &end, 10);
    if (value[0] < '0' || value[0] > '9' || errno || *end || n > max)
        dn_harness("%s%s: not a number from 0 to %llu: %s", setting_at, name, (unsigned long long)max, value);
    return n;
}

static void set(const char *name, const char *value) {
    const char *counted_as = strcmp(name, "--check-config") ? name : taken_once[GIVEN_SETTINGS];
    for (size_t k = 0; k < sizeof taken_once / sizeof *taken_once; ++k)
        if (!strcmp(counted_as, taken_once[k]) && given[k]++) dn_harness("%s%s given twice", setting_at, name);
    if (!strcmp(name, "--port")) port_wanted = (unsigned)number(name, value, 65535);
    else if (!strcmp(name, "--address")) address = value;
    else if (!strcmp(name, "--revision")) revision = value;
    else if (!strcmp(name, "--source")) source = value;
    else if (!strcmp(name, "--send-buffer")) send_buffer = (int)number(name, value, 1 << 20);
    else if (!strcmp(name, "--clock-fd")) clock_fd = descriptor(value);
    else if (!strcmp(name, "--report-fd")) report_fd = descriptor(value);
    else if (!strcmp(name, "--tls-cert")) tls_cert = value;
    else if (!strcmp(name, "--tls-key")) tls_key = value;
    else if (!strcmp(counted_as, "--config")) {
        checking = !strcmp(name, "--check-config");
        read_settings(value);
    } else if (!dn_store_option(name, value)) dn_harness("%sunknown setting %s", setting_at, name);
}

/* The settings of the file at `path`, each taken as its option would be. */
static void read_settings(const char *path) {
    static char text[CONFIG_MAX + 1];
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) dn_harness("%s: %s", path, strerror(errno));
    size_t n = 0;
    for (ssize_t got; (got = read(fd, text + n, CONFIG_MAX + 1 - n)) != 0;) {
        if (got < 0) {
            if (errno == EINTR) continue;
            dn_harness("%s: %s", path, strerror(errno));
        }
        n += (size_t)got;
        if (n > CONFIG_MAX) dn_harness("%s: more than %d bytes", path, CONFIG_MAX);
    }
    close(fd);
    text[n] = 0;
    if (strlen(text) != n) dn_harness("%s: a NUL byte", path);
    static const char *const options_only[] = {"--config", "--check-config", "--clock-fd", "--report-fd"};
    char at[PATH_MAX + 32], option[64];
    unsigned line = 0;
    for (char *p = text, *next; *p; p = next) {
        ++line;
        char *end = strchr(p, '\n');
        next = end ? end + 1 : p + strlen(p);
        if (end) *end = 0;
        p += strspn(p, " \t");
        if (!*p || *p == '#') continue;
        char *name = p;
        p += strcspn(p, " \t");
        if (*p) *p++ = 0;
        p += strspn(p, " \t");
        size_t len = strlen(p);
        while (len && (p[len - 1] == ' ' || p[len - 1] == '\t' || p[len - 1] == '\r')) p[--len] = 0;
        snprintf(at, sizeof at, "%s:%u: ", path, line);
        setting_at = at;
        if (strlen(name) + 3 > sizeof option) dn_harness("%sunknown setting %s", at, name);
        snprintf(option, sizeof option, "--%s", name);
        for (size_t k = 0; k < sizeof options_only / sizeof *options_only; ++k)
            if (!strcmp(option, options_only[k])) dn_harness("%s%s is an option only", at, name);
        if (!len) dn_harness("%s%s needs a value", at, name);
        set(option, p);
        setting_at = "";
    }
}

/* The listening socket systemd hands over (sd_listen_fds(3)), or -1 when it hands none to this
 * process; as there, the variables are taken out of the environment either way. */
static int handed_listener(void) {
    const char *pid_text = getenv("LISTEN_PID"), *fds_text = getenv("LISTEN_FDS");
    uint64_t pid = pid_text ? dn_parse_u64(pid_text, UINT32_MAX) : 0, fds = fds_text ? dn_parse_u64(fds_text, 64) : 0;
    unsetenv("LISTEN_PID");
    unsetenv("LISTEN_FDS");
    unsetenv("LISTEN_FDNAMES");
    if (!pid_text || !fds_text || pid != (uint64_t)getpid() || !fds) return -1;
    if (fds != 1) dn_harness("LISTEN_FDS: %" PRIu64 " sockets, where the server takes one", fds);
    int type = 0, accepting = 0;
    socklen_t len = sizeof type;
    if (getsockopt(LISTEN_FD, SOL_SOCKET, SO_TYPE, &type, &len) || type != SOCK_STREAM)
        dn_harness("LISTEN_FDS: descriptor %d is not a stream socket", LISTEN_FD);
    struct sockaddr_storage at;
    socklen_t at_len = sizeof at;
    if (getsockname(LISTEN_FD, (struct sockaddr *)&at, &at_len) || (at.ss_family != AF_INET && at.ss_family != AF_INET6))
        dn_harness("LISTEN_FDS: descriptor %d is not an IPv4 or IPv6 socket", LISTEN_FD);
    len = sizeof accepting;
    if (getsockopt(LISTEN_FD, SOL_SOCKET, SO_ACCEPTCONN, &accepting, &len) || !accepting)
        dn_harness("LISTEN_FDS: descriptor %d does not listen", LISTEN_FD);
    int flags = fcntl(LISTEN_FD, F_GETFL);
    if (flags < 0 || fcntl(LISTEN_FD, F_SETFL, flags | O_NONBLOCK) || fcntl(LISTEN_FD, F_SETFD, FD_CLOEXEC))
        dn_harness("LISTEN_FDS: %s", strerror(errno));
    if (given[GIVEN_PORT] || given[GIVEN_ADDRESS])
        dn_harness("--address and --port are the socket's when systemd hands one over");
    return LISTEN_FD;
}

/* The address to listen at. */
static socklen_t where_of(struct sockaddr_storage *where) {
    *where = (struct sockaddr_storage){0};
    struct sockaddr_in *v4 = (struct sockaddr_in *)where;
    struct sockaddr_in6 *v6 = (struct sockaddr_in6 *)where;
    if (inet_pton(AF_INET, address, &v4->sin_addr) == 1) {
        v4->sin_family = AF_INET;
        v4->sin_port = htons((uint16_t)port_wanted);
        return sizeof *v4;
    }
    if (inet_pton(AF_INET6, address, &v6->sin6_addr) == 1) {
        v6->sin6_family = AF_INET6;
        v6->sin6_port = htons((uint16_t)port_wanted);
        return sizeof *v6;
    }
    dn_harness("not an address: %s", address);
}

/* What `--check-config` writes: the settings, as the host would take them. */
__attribute__((noreturn)) static void say_settings(void) {
    struct sockaddr_storage where;
    where_of(&where);
    dn_store_check();
    fputs("{\"address\":", stdout);
    dn_json_string(stdout, address);
    printf(",\"port\":%u,\"revision\":", port_wanted);
    dn_json_string(stdout, revision);
    fputs(",\"source\":", stdout);
    dn_json_string(stdout, source);
    printf(",\"send_buffer\":%d,\"tls_cert\":", send_buffer);
    if (tls_cert) dn_json_string(stdout, tls_cert);
    else fputs("null", stdout);
    fputs(",\"tls_key\":", stdout);
    if (tls_key) dn_json_string(stdout, tls_key);
    else fputs("null", stdout);
    dn_store_settings(stdout);
    puts("}");
    if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
    exit(0);
}

int main(int argc, char **argv) {
    for (int i = 1; i < argc; i += 2) {
        if (i + 1 == argc) dn_harness("%s needs a value", argv[i]);
        set(argv[i], argv[i + 1]);
    }
    identity("--revision", revision, DN_SESSION_REV_MAX);
    identity("--source", source, DN_SESSION_SRC_MAX);
    if (!tls_cert != !tls_key) dn_harness("--tls-cert and --tls-key are given together");
    if (tls_cert) {
        char why[512];
        if (dn_tls_setup(tls_cert, tls_key, why, sizeof why)) dn_harness("TLS: %s", why);
    }
    if (checking) say_settings();
    int handed = handed_listener();
    /* Blocked before anything starts, the workers too, so that a signal waits for the loop. */
    sigset_t mask;
    sigemptyset(&mask);
    sigaddset(&mask, SIGTERM);
    sigaddset(&mask, SIGINT);
    sigaddset(&mask, SIGUSR1);
    if (sigprocmask(SIG_BLOCK, &mask, NULL)) dn_harness("sigprocmask: %s", strerror(errno));
    signals = signalfd(-1, &mask, SFD_CLOEXEC | SFD_NONBLOCK);
    if (signals < 0) dn_harness("signalfd: %s", strerror(errno));
    if (signal(SIGPIPE, SIG_IGN) == SIG_ERR) dn_harness("signal: %s", strerror(errno));
    dn_store_start();
    jobs_done = dn_jobs_start(dn_store_spool());
    if (clock_fd >= 0) now_virtual = 1;
    for (int i = 0; i < CONNS; ++i) conns[i].fd = -1;
    for (int i = 0; i < LINGERING; ++i) lingering[i].fd = -1;

    struct sockaddr_storage where;
    socklen_t where_len = where_of(&where);
    if (handed >= 0) {
        listener = handed;
        where_len = sizeof where;
    } else {
        listener = socket(where.ss_family, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
        if (listener < 0) dn_harness("socket: %s", strerror(errno));
        int one = 1;
        if (setsockopt(listener, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one))
            dn_harness("setsockopt: %s", strerror(errno));
        if (where.ss_family == AF_INET6 && setsockopt(listener, IPPROTO_IPV6, IPV6_V6ONLY, &one, sizeof one))
            dn_harness("setsockopt: %s", strerror(errno));
        if (bind(listener, (struct sockaddr *)&where, where_len)) dn_harness("bind: %s", strerror(errno));
    }
    if (getsockname(listener, (struct sockaddr *)&where, &where_len)) dn_harness("getsockname: %s", strerror(errno));
    struct sockaddr_in *v4 = (struct sockaddr_in *)&where;
    struct sockaddr_in6 *v6 = (struct sockaddr_in6 *)&where;
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
