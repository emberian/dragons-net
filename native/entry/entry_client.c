/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The load for the entry benchmark: M connections, each sending R commands one at a time and
 * checking every reply against the reference.
 *   entry-client PORT M R */
#include "entry.h"
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <poll.h>
#include <sys/socket.h>
#include <unistd.h>

enum { MAX_CONNECTIONS = 256, IDLE_MS = 10000 };

static void send_command(int fd, int command) {
    ssize_t sent = send(fd, dn_entry_commands[command], (size_t)dn_entry_command_lengths[command], MSG_NOSIGNAL);
    if (sent < 0) dn_fail_errno("send");
    /* A command is a few bytes into an empty socket buffer, so it goes out whole or not at all. */
    if (sent != dn_entry_command_lengths[command]) dn_fail("send: a command went out in part");
}

int main(int argc, char **argv) {
    if (argc != 4) dn_fail("usage: entry-client PORT M R");
    int port = (int)dn_number(argv[1], 1, 65535), m = (int)dn_number(argv[2], 1, MAX_CONNECTIONS);
    long r = dn_number(argv[3], 1, 100000000);
    static int fd[MAX_CONNECTIONS], command[MAX_CONNECTIONS], which[MAX_CONNECTIONS];
    static long done[MAX_CONNECTIONS], have[MAX_CONNECTIONS];
    static unsigned char buffer[MAX_CONNECTIONS][DN_ENTRY_DATA];
    struct pollfd p[MAX_CONNECTIONS];
    struct sockaddr_in addr = {.sin_family = AF_INET, .sin_port = htons((uint16_t)port),
                               .sin_addr.s_addr = htonl(INADDR_LOOPBACK)};
    for (int i = 0; i < m; ++i) {
        fd[i] = socket(AF_INET, SOCK_STREAM, 0);
        int one = 1;
        if (fd[i] < 0) dn_fail_errno("socket");
        if (setsockopt(fd[i], IPPROTO_TCP, TCP_NODELAY, &one, sizeof one)) dn_fail_errno("TCP_NODELAY");
        if (connect(fd[i], (struct sockaddr *)&addr, sizeof addr)) dn_fail_errno("connect");
    }
    double start = dn_now_ns();
    for (int i = 0; i < m; ++i) {
        command[i] = i % DN_ENTRY_COMMANDS;
        send_command(fd[i], command[i]);
    }
    int finished = 0;
    while (finished < m) {
        int n = 0;
        for (int i = 0; i < m; ++i)
            if (done[i] < r) { p[n] = (struct pollfd){.fd = fd[i], .events = POLLIN}; which[n++] = i; }
        int ready = poll(p, (nfds_t)n, IDLE_MS);
        if (ready < 0 && errno == EINTR) continue;
        if (ready < 0) dn_fail_errno("poll");
        if (ready == 0) dn_fail("no reply for ten seconds");
        for (int j = 0; j < n; ++j) {
            if (!p[j].revents) continue;
            int i = which[j];
            ssize_t got = recv(fd[i], buffer[i] + have[i], sizeof buffer[i] - (size_t)have[i], 0);
            if (got < 0 && errno == EINTR) continue;
            if (got <= 0) dn_fail("the server closed a connection");
            have[i] += got;
            long want = dn_entry_reply_lengths[command[i]];
            if (have[i] < want) continue;
            if (have[i] != want || memcmp(buffer[i], dn_entry_replies[command[i]], (size_t)want))
                dn_fail("a reply is not the one the reference gives");
            have[i] = 0;
            if (++done[i] == r) { ++finished; continue; }
            command[i] = (command[i] + 1) % DN_ENTRY_COMMANDS;
            send_command(fd[i], command[i]);
        }
    }
    double seconds = (dn_now_ns() - start) / 1e9;
    printf("{\"connections\":%d,\"requests\":%ld,\"seconds\":%.3f,\"requests_per_second\":%.0f}\n", m, (long)m * r, seconds, (double)m * (double)r / seconds);
    for (int i = 0; i < m; ++i) close(fd[i]);
    return 0;
}
