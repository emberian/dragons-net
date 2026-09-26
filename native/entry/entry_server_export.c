/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The exported design on the network: this host runs the loop and calls the program's exported
 * dn_reply for each request, with its buffers in its own memory, as the native lanes do.
 *   entry-server-export TOTAL
 * One recv is taken for one request, as in entry_server_loop.c. */
#include "entry_net.h"
extern uint32_t dn_reply(uint64_t, uint64_t, uint64_t, uint64_t);

int main(int argc, char **argv) {
    if (argc != 2) dn_fail("usage: entry-server-export TOTAL");
    net_total = dn_number(argv[1], 1, 1000000000);
    net_listen();
    dn_runtime_setup();
    dn_runtime_header();
    cml_main();
    if (!dn_runtime_header_intact()) dn_fail("the heap header is not what the compiler theorem requires");
    static unsigned char in[DN_ENTRY_DATA], out[DN_ENTRY_DATA];
    while (net_served < net_total) {
        int n = net_wait();
        for (int j = 1; j <= n; ++j) {
            if (!(net_fds[j].revents & (POLLIN | POLLHUP | POLLERR))) continue;
            int i = net_fd_conn[j];
            ssize_t got = recv(net_conns[i], in, sizeof in, 0);
            if (got < 0 && errno == EINTR) continue;
            if (got <= 0) { net_drop(i); continue; }
            uint32_t len = dn_reply((uintptr_t)in, (uint64_t)got, (uintptr_t)out, DN_ENTRY_DATA);
            if (len > DN_ENTRY_DATA) dn_fail("dn_reply refused a request");
            net_send(i, out, len);
            ++net_served;
        }
    }
    return 0;
}
