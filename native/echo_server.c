/* SPDX-License-Identifier: AGPL-3.0-or-later
 * Bounded reference host. Every payload byte goes through generated dn_echo.
 * Single thread: the Cake heap/stack cannot be entered concurrently.
 * poll is a bring-up adapter, not the planned io_uring dataplane. */
#define _POSIX_C_SOURCE 200809L
#include "cake_runtime.h"
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <poll.h>
#include <signal.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

enum { SLOTS = 32, CAPACITY = 4096 };
extern uint32_t dn_echo(uint64_t, uint64_t, uint64_t, uint64_t);
static volatile sig_atomic_t stopping;
static void stop(int signal_number) { (void)signal_number; stopping = 1; }
static uint64_t millis(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) abort();
    return (uint64_t)t.tv_sec * 1000 + (uint64_t)t.tv_nsec / 1000000;
}
static int nonblocking(int fd) {
    int flags = fcntl(fd, F_GETFL);
    return flags < 0 ? -1 : fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}
static unsigned number(const char *text, unsigned maximum) {
    char *end;
    errno = 0;
    unsigned long n = strtoul(text, &end, 10);
    if (errno || !*text || *end || n > maximum) {
        fputs("invalid numeric option\n", stderr); exit(2);
    }
    return (unsigned)n;
}
struct connection {
    int fd;
    unsigned char out[CAPACITY];
    size_t length, sent;
    uint64_t active;
};
static void close_connection(struct connection *c) {
    close(c->fd); c->fd = -1; c->length = c->sent = 0;
}

int main(int argc, char **argv) {
    unsigned port = 0, write_chunk = CAPACITY, idle_ms = 30000;
    for (int i = 1; i < argc; i += 2) {
        if (i + 1 == argc) { fputs("option needs a value\n", stderr); return 2; }
        if (!strcmp(argv[i], "--port")) port = number(argv[i+1], 65535);
        else if (!strcmp(argv[i], "--write-chunk")) write_chunk = number(argv[i+1], CAPACITY);
        else if (!strcmp(argv[i], "--idle-ms")) idle_ms = number(argv[i+1], 60000);
        else { fputs("unknown option\n", stderr); return 2; }
    }
    if (!write_chunk || idle_ms < 50) return 2;
    struct sigaction action = {0};
    action.sa_handler = stop;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGTERM, &action, NULL) || sigaction(SIGINT, &action, NULL)) return 1;
    action.sa_handler = SIG_IGN;
    if (sigaction(SIGPIPE, &action, NULL)) return 1;
    dn_runtime_init();
    int listener = socket(AF_INET, SOCK_STREAM, 0);
    if (listener < 0) { perror("socket"); return 1; }
    struct sockaddr_in address = { .sin_family = AF_INET, .sin_port = htons((uint16_t)port),
                                  .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
    if (nonblocking(listener) || bind(listener, (struct sockaddr *)&address, sizeof(address)) ||
        listen(listener, SLOTS)) { perror("listen"); close(listener); return 1; }
    socklen_t address_len = sizeof(address);
    if (getsockname(listener, (struct sockaddr *)&address, &address_len)) return 1;
    printf("{\"port\":%u,\"slots\":%u,\"buffer_bytes\":%u}\n",
           (unsigned)ntohs(address.sin_port), SLOTS, CAPACITY);
    fflush(stdout);
    struct connection clients[SLOTS];
    for (size_t i = 0; i < SLOTS; ++i) clients[i] = (struct connection){ .fd = -1 };
    uint64_t calls = 0, bytes = 0, sends = 0, partial = 0, accepted = 0, expired = 0;
    int result = 0;
    while (!stopping) {
        struct pollfd events[SLOTS + 1];
        int free_slot = -1;
        for (size_t i = 0; i < SLOTS; ++i) {
            struct connection *c = &clients[i];
            if (c->fd >= 0 && millis() - c->active >= idle_ms) {
                close_connection(c); ++expired;
            }
            if (c->fd < 0) free_slot = (int)i;
            events[i+1] = (struct pollfd){c->fd, c->length ? POLLOUT : POLLIN, 0};
        }
        events[0] = (struct pollfd){free_slot >= 0 ? listener : -1, POLLIN, 0};
        int count = poll(events, SLOTS + 1, 100);
        if (count < 0) {
            if (errno == EINTR) continue;
            perror("poll"); result = 1; break;
        }
        /* Process only connections represented in this poll result. A newly
         * accepted descriptor cannot inherit a recycled slot's readiness. */
        for (size_t i = 0; i < SLOTS; ++i) {
            struct connection *c = &clients[i];
            short ready = events[i+1].revents;
            if (c->fd < 0 || !ready) continue;
            if (ready & (POLLERR | POLLNVAL)) { close_connection(c); continue; }
            if (c->length) {
                size_t remaining = c->length - c->sent;
                size_t chunk = remaining < write_chunk ? remaining : write_chunk;
                ssize_t n = send(c->fd, c->out + c->sent, chunk, 0);
                if (n > 0) {
                    ++sends;
                    if ((size_t)n < remaining) ++partial;
                    c->sent += (size_t)n; c->active = millis();
                    if (c->sent == c->length) c->sent = c->length = 0;
                } else if (n == 0 || (errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR)) {
                    close_connection(c);
                }
            } else {
                unsigned char input[CAPACITY];
                ssize_t n = recv(c->fd, input, sizeof(input), 0);
                if (n > 0) {
                    uint64_t produced = dn_echo((uintptr_t)input, (uintptr_t)c->out, (uint64_t)n, CAPACITY);
                    if (produced != (uint64_t)n) {
                        fputs("generated echo contract failed\n", stderr); result = 1; stopping = 1; break;
                    }
                    ++calls; bytes += produced; c->length = (size_t)produced; c->active = millis();
                } else if (n == 0 || (errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR)) {
                    close_connection(c);
                }
            }
        }
        if (events[0].revents & POLLIN) {
            int fd = accept(listener, NULL, NULL);
            if (fd >= 0) {
                if (nonblocking(fd)) close(fd);
                else { clients[free_slot] = (struct connection){ .fd = fd, .active = millis() }; ++accepted; }
            } else if (errno != EINTR && errno != EAGAIN && errno != EWOULDBLOCK) {
                perror("accept"); result = 1; break;
            }
        }
    }
    for (size_t i = 0; i < SLOTS; ++i) if (clients[i].fd >= 0) close_connection(&clients[i]);
    close(listener);
    fprintf(stderr, "{\"kernel_calls\":%" PRIu64 ",\"kernel_bytes\":%" PRIu64
            ",\"send_calls\":%" PRIu64 ",\"partial_progress\":%" PRIu64
            ",\"accepted\":%" PRIu64 ",\"idle_expired\":%" PRIu64 "}\n",
            calls, bytes, sends, partial, accepted, expired);
    return result;
}
