/* SPDX-License-Identifier: AGPL-3.0-or-later
 * Sockets for the two servers of the entry benchmark (entry_net.c): a loopback listener and up to
 * DN_NET_MAX connections, one process, one thread. */
#ifndef DN_ENTRY_NET_H
#define DN_ENTRY_NET_H
#include "entry.h"
#include <poll.h>
#include <sys/socket.h>

enum { DN_NET_MAX = 256, DN_NET_IDLE_MS = 10000 };
extern int net_conns[DN_NET_MAX];
extern struct pollfd net_fds[DN_NET_MAX + 1];
extern int net_fd_conn[DN_NET_MAX + 1];
extern long net_served, net_total;

/* Listen on a free loopback port and print it, so the client can connect. */
void net_listen(void);

/* Wait until a connection is readable, accepting new ones meanwhile. Returns how many poll
   entries follow the listener's; net_fd_conn maps each to its connection. */
int net_wait(void);

void net_drop(int i);

/* Send the whole reply. The client reads every reply before it sends again and a reply is a few
   dozen bytes, so this does not wait on a client; a server for real clients may not block here. */
void net_send(int i, const unsigned char *p, long len);
#endif
