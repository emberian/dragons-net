/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The loop design on the network: the program's main fetches requests from this host through
 * external calls, and the host receives them straight into the array the call names.
 *   entry-server-loop TOTAL K [--repoll]
 * serves TOTAL requests in batches of up to K, then ends the batch stream so main returns. The
 * host hands out what one poll reported before polling again; with --repoll it polls on every call
 * and drops the rest, which is what a naive host does and what the benchmark compares against.
 * One recv is taken for one request: the client sends a request only after the previous reply,
 * and every request fits a slot. */
#include "entry_net.h"

static long batch;
static int repoll, ready[DN_NET_MAX], nready, taken;

static void refill(void) {
    int n = net_wait();
    nready = taken = 0;
    for (int j = 1; j <= n; ++j)
        if (net_fds[j].revents & (POLLIN | POLLHUP | POLLERR)) ready[nready++] = net_fd_conn[j];
}

void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen) {
    dn_in_heap(c, clen, "next");
    dn_in_heap(a, alen, "next");
    dn_header_checked();
    if (alen != DN_ENTRY_AREA) dn_fail("next: the array is not a batch area");
    long k = 0;
    while (k == 0 && net_served < net_total) {
        if (repoll || taken == nready) refill();
        while (taken < nready && k < batch) {
            int i = ready[taken++];
            if (net_conns[i] < 0) continue;
            unsigned char *slot = a + 8 + k * DN_ENTRY_SLOT;
            ssize_t got = recv(net_conns[i], slot + 16, DN_ENTRY_DATA, 0);
            if (got < 0 && errno == EINTR) { --taken; continue; }
            if (got <= 0) { net_drop(i); continue; }
            dn_put_word(slot, (uint64_t)i);
            dn_put_word(slot + 8, (uint64_t)got);
            ++k;
        }
        if (repoll) nready = taken = 0;
    }
    dn_put_word(a, (uint64_t)k);
}

void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen) {
    dn_in_heap(c, clen, "emit");
    dn_in_heap(a, alen, "emit");
    if (alen != DN_ENTRY_AREA) dn_fail("emit: the array is not a batch area");
    uint64_t k = dn_word(a);
    if (k > DN_ENTRY_BATCH_MAX) dn_fail("emit: more replies than a batch holds");
    for (uint64_t j = 0; j < k; ++j) {
        const unsigned char *slot = a + 8 + j * DN_ENTRY_SLOT;
        uint64_t i = dn_word(slot), len = dn_word(slot + 8);
        if (i >= DN_NET_MAX || len > DN_ENTRY_DATA) dn_fail("emit: a reply names no connection or overruns its slot");
        if (net_conns[i] >= 0) net_send((int)i, slot + 16, (long)len);
        ++net_served;
    }
}

int main(int argc, char **argv) {
    repoll = argc == 4 && strcmp(argv[3], "--repoll") == 0;
    if (argc != 3 + repoll) dn_fail("usage: entry-server-loop TOTAL K [--repoll]");
    net_total = dn_number(argv[1], 1, 1000000000);
    batch = dn_number(argv[2], 1, DN_ENTRY_BATCH_MAX);
    net_listen();
    dn_runtime_setup();
    dn_runtime_header();
    cml_main();
    if (net_served != net_total) dn_fail("the program stopped before every request was served");
    return 0;
}
