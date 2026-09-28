/* SPDX-License-Identifier: AGPL-3.0-or-later */
#include "entry_net.h"
#include <arpa/inet.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <unistd.h>

int net_conns[DN_NET_MAX];
struct pollfd net_fds[DN_NET_MAX + 1];
int net_fd_conn[DN_NET_MAX + 1];
long net_served, net_total;
static int net_listener;

void net_listen(void) {
    net_listener = socket(AF_INET, SOCK_STREAM, 0);
    if (net_listener < 0) dn_broken_errno("socket");
    int one = 1;
    if (setsockopt(net_listener, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one)) dn_broken_errno("SO_REUSEADDR");
    struct sockaddr_in addr = {.sin_family = AF_INET, .sin_addr.s_addr = htonl(INADDR_LOOPBACK)};
    socklen_t len = sizeof addr;
    if (bind(net_listener, (struct sockaddr *)&addr, sizeof addr)) dn_broken_errno("bind");
    if (listen(net_listener, 512)) dn_broken_errno("listen");
    if (getsockname(net_listener, (struct sockaddr *)&addr, &len)) dn_broken_errno("getsockname");
    for (int i = 0; i < DN_NET_MAX; ++i) net_conns[i] = -1;
    printf("%d\n", ntohs(addr.sin_port));
    fflush(stdout);
}

static void net_accept(void) {
    int fd = accept(net_listener, NULL, NULL);
    if (fd < 0) {
        if (errno == EINTR || errno == EAGAIN || errno == ECONNABORTED) return;
        dn_broken_errno("accept");
    }
    int one = 1;
    /* Requests and replies are small and alternate, so Nagle's delay would be all there is. */
    if (setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one)) dn_broken_errno("TCP_NODELAY");
    for (int i = 0; i < DN_NET_MAX; ++i)
        if (net_conns[i] < 0) { net_conns[i] = fd; return; }
    dn_broken("more connections than the benchmark admits");
}

int net_wait(void) {
    for (;;) {
        int n = 0;
        net_fds[n++] = (struct pollfd){.fd = net_listener, .events = POLLIN};
        for (int i = 0; i < DN_NET_MAX; ++i)
            if (net_conns[i] >= 0) {
                net_fd_conn[n] = i;
                net_fds[n++] = (struct pollfd){.fd = net_conns[i], .events = POLLIN};
            }
        int events = poll(net_fds, (nfds_t)n, DN_NET_IDLE_MS);
        if (events < 0 && errno == EINTR) continue;
        if (events < 0) dn_broken_errno("poll");
        if (events == 0) dn_broken("no activity for ten seconds");
        if (net_fds[0].revents & POLLIN) net_accept();
        if (events > (net_fds[0].revents ? 1 : 0)) return n - 1;
    }
}

void net_drop(int i) {
    close(net_conns[i]);
    net_conns[i] = -1;
}

void net_send(int i, const unsigned char *p, long len) {
    while (len > 0) {
        ssize_t sent = send(net_conns[i], p, (size_t)len, MSG_NOSIGNAL);
        if (sent < 0 && errno == EINTR) continue;
        if (sent <= 0) { net_drop(i); return; }
        p += sent;
        len -= sent;
    }
}
