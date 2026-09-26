/* SPDX-License-Identifier: AGPL-3.0-or-later
 * Sockets for the two servers of the entry benchmark: a loopback listener and up to DN_NET_MAX
 * connections, one process, one thread. */
#ifndef DN_ENTRY_NET_H
#define DN_ENTRY_NET_H
#include "entry.h"
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <poll.h>
#include <sys/socket.h>
#include <unistd.h>

enum { DN_NET_MAX = 256, DN_NET_IDLE_MS = 10000 };
static int net_listener, net_conns[DN_NET_MAX];
static struct pollfd net_fds[DN_NET_MAX + 1];
static int net_fd_conn[DN_NET_MAX + 1];
static long net_served, net_total;

/* Listen on a free loopback port and print it, so the client can connect. */
static void net_listen(void) {
    net_listener = socket(AF_INET, SOCK_STREAM, 0);
    if (net_listener < 0) dn_fail_errno("socket");
    int one = 1;
    if (setsockopt(net_listener, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one)) dn_fail_errno("SO_REUSEADDR");
    struct sockaddr_in addr = {.sin_family = AF_INET, .sin_addr.s_addr = htonl(INADDR_LOOPBACK)};
    socklen_t len = sizeof addr;
    if (bind(net_listener, (struct sockaddr *)&addr, sizeof addr)) dn_fail_errno("bind");
    if (listen(net_listener, 512)) dn_fail_errno("listen");
    if (getsockname(net_listener, (struct sockaddr *)&addr, &len)) dn_fail_errno("getsockname");
    for (int i = 0; i < DN_NET_MAX; ++i) net_conns[i] = -1;
    printf("%d\n", ntohs(addr.sin_port));
    fflush(stdout);
}

static void net_accept(void) {
    int fd = accept(net_listener, NULL, NULL);
    if (fd < 0) {
        if (errno == EINTR || errno == EAGAIN || errno == ECONNABORTED) return;
        dn_fail_errno("accept");
    }
    int one = 1;
    /* Requests and replies are small and alternate, so Nagle's delay would be all there is. */
    if (setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one)) dn_fail_errno("TCP_NODELAY");
    for (int i = 0; i < DN_NET_MAX; ++i)
        if (net_conns[i] < 0) { net_conns[i] = fd; return; }
    dn_fail("more connections than the benchmark admits");
}

/* Wait until a connection is readable, accepting new ones meanwhile. Returns how many poll
   entries follow the listener's; net_fd_conn maps each to its connection. */
static int net_wait(void) {
    for (;;) {
        int n = 0;
        net_fds[n++] = (struct pollfd){.fd = net_listener, .events = POLLIN};
        for (int i = 0; i < DN_NET_MAX; ++i)
            if (net_conns[i] >= 0) {
                net_fd_conn[n] = i;
                net_fds[n++] = (struct pollfd){.fd = net_conns[i], .events = POLLIN};
            }
        int ready = poll(net_fds, (nfds_t)n, DN_NET_IDLE_MS);
        if (ready < 0 && errno == EINTR) continue;
        if (ready < 0) dn_fail_errno("poll");
        if (ready == 0) dn_fail("no activity for ten seconds");
        if (net_fds[0].revents & POLLIN) net_accept();
        if (ready > (net_fds[0].revents ? 1 : 0)) return n - 1;
    }
}

static void net_drop(int i) {
    close(net_conns[i]);
    net_conns[i] = -1;
}

/* Send the whole reply. The client reads every reply before it sends again and a reply is a few
   dozen bytes, so this does not wait on a client; a server for real clients may not block here. */
static void net_send(int i, const unsigned char *p, long len) {
    while (len > 0) {
        ssize_t sent = send(net_conns[i], p, (size_t)len, MSG_NOSIGNAL);
        if (sent < 0 && errno == EINTR) continue;
        if (sent <= 0) { net_drop(i); return; }
        p += sent;
        len -= sent;
    }
}
#endif
