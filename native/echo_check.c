// SPDX-License-Identifier: AGPL-3.0-or-later
#define _GNU_SOURCE
#include "accept_policy.h"
#include "cake_runtime.h"
#include <inttypes.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>
extern uint32_t dn_echo(uint64_t, uint64_t, uint64_t, uint64_t);

int main(void) {
    dn_runtime_init();
    unsigned char source[4112], destination[4112];
    for (size_t i = 0; i < sizeof(source); ++i) source[i] = (unsigned char)(i * 37);
    uint64_t cases = 0;
    for (size_t a = 0; a < 8; ++a) for (size_t b = 0; b < 8; ++b)
        for (size_t len = 0; len <= 4096; len += len < 80 ? 1 : 251) {
            /* The host always passes the whole buffer as capacity, so the frame has to
               hold for every capacity at or above the length, not only for cap == len. */
            const size_t caps[] = {len, len + 1, (len + 4096) / 2, 4096};
            for (size_t c = 0; c < sizeof(caps)/sizeof(caps[0]); ++c) {
                size_t cap = caps[c];
                if (cap < len || cap > 4096) continue;
                memset(destination, 0xa5, sizeof(destination));
                if (dn_echo((uintptr_t)(source+a), (uintptr_t)(destination+b), len, cap) != len)
                    return 1;
                for (size_t i = 0; i < sizeof(destination); ++i) {
                    unsigned char expected = i >= b && i - b < len ? source[a+i-b] : 0xa5;
                    if (destination[i] != expected) {
                        fputs("copy/frame mismatch\n", stderr);
                        return 1;
                    }
                }
                ++cases;
            }
        }
    /* A page with no access right after the destination: a kernel that writes past the
       length faults instead of quietly changing bytes a comparison might miss. */
    size_t page_size = (size_t)sysconf(_SC_PAGESIZE);
    unsigned char *pages = mmap(NULL, page_size * 2, PROT_READ | PROT_WRITE,
                                MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (pages == MAP_FAILED) return 1;
    if (mprotect(pages + page_size, page_size, PROT_NONE)) return 1;
    for (size_t len = 0; len <= 64; ++len) {
        unsigned char *tail = pages + page_size - len;
        memset(pages, 0xa5, page_size);
        if (dn_echo((uintptr_t)source, (uintptr_t)tail, len, 4096) != len) return 1;
        for (size_t i = 0; i < len; ++i)
            if (tail[i] != source[i]) { fputs("copy/frame mismatch\n", stderr); return 1; }
        ++cases;
    }
    munmap(pages, page_size * 2);

    /* Overlapping source and destination. The contract asks callers for disjoint buffers, and
       the copy theorem is stated for that case only — but a caller that ignores it does not get
       an undefined result: the kernel copies forward, one byte at a time, so a destination above
       the source reads back bytes it has already written. What that produces is simulated here on
       a separate array, byte by byte, and compared with what the compiled kernel did. */
    for (size_t len = 0; len <= 64; ++len) {
        for (size_t gap = 0; gap <= 8; ++gap) {
            for (int above = 0; above < 2; ++above) {
                unsigned char region[256], expected[256];
                for (size_t i = 0; i < sizeof(region); ++i) region[i] = (unsigned char)(i * 31 + 7);
                memcpy(expected, region, sizeof(region));
                size_t src = above ? 64 : 64 + gap;
                size_t dst = above ? 64 + gap : 64;
                for (size_t i = 0; i < len; ++i) expected[dst + i] = expected[src + i];
                if (dn_echo((uintptr_t)(region + src), (uintptr_t)(region + dst), len,
                            sizeof(region) - dst) != len)
                    return 1;
                if (memcmp(region, expected, sizeof(region))) {
                    fputs("overlap mismatch\n", stderr);
                    return 1;
                }
                ++cases;
            }
        }
    }

    /* Rejected lengths must not dereference either pointer. */
    void *guard = mmap(NULL, page_size, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (guard == MAP_FAILED) return 1;
    uint64_t bad[][2] = {{1,0}, {4097,4096}, {UINT64_MAX,4096}, {1ULL<<63,4096},
                         {0,UINT64_MAX}, {0,1ULL<<63},
                         {0,4097}, {1,4097}, {4096,4097}, {4097,4097}, {0,8192}};
    for (size_t i = 0; i < sizeof(bad)/sizeof(bad[0]); ++i) {
        if (dn_echo((uintptr_t)guard, (uintptr_t)guard, bad[i][0], bad[i][1]) != UINT32_MAX) return 1;
        ++cases;
    }
    if (dn_echo((uintptr_t)guard, (uintptr_t)guard, 0, 0) != 0) return 1;
    ++cases;
    munmap(guard, page_size);
    /* The expected classification, written from accept(2) rather than copied from the
       policy: the manual's "Error handling" section lists ENETDOWN, EPROTO, ENOPROTOOPT,
       EHOSTDOWN, ENONET, EHOSTUNREACH, EOPNOTSUPP and ENETUNREACH as errors to treat like
       EAGAIN by retrying, and ECONNABORTED as a connection aborted before it was taken.
       A listener that cannot work at all is the only reason to stop. */
    const int fatal[] = {EBADF, EINVAL, ENOTSOCK, EFAULT};
    const int retry[] = {EAGAIN, EINTR, ECONNABORTED, EPERM, EPROTO, ENETDOWN,
                         ENOPROTOOPT, EHOSTDOWN, ENONET, EHOSTUNREACH, ENETUNREACH,
                         EOPNOTSUPP, ETIMEDOUT, ECONNRESET};
    /* Running out of a resource is temporary, but retrying at once would spin. */
    const int pause[] = {EMFILE, ENFILE, ENOBUFS, ENOMEM, ENOSR, EPROTONOSUPPORT};
    for (size_t i = 0; i < sizeof(fatal)/sizeof(fatal[0]); ++i) {
        if (dn_accept_action(fatal[i]) != DN_ACCEPT_FATAL) {
            fputs("accept policy too forgiving\n", stderr);
            return 1;
        }
        ++cases;
    }
    for (size_t i = 0; i < sizeof(retry)/sizeof(retry[0]); ++i) {
        if (dn_accept_action(retry[i]) != DN_ACCEPT_RETRY) {
            fputs("accept policy too strict\n", stderr);
            return 1;
        }
        ++cases;
    }
    for (size_t i = 0; i < sizeof(pause)/sizeof(pause[0]); ++i) {
        if (dn_accept_action(pause[i]) != DN_ACCEPT_PAUSE) {
            fputs("accept policy mishandles resource exhaustion\n", stderr);
            return 1;
        }
        ++cases;
    }
    printf("{\"copy_cases\":%" PRIu64 "}\n", cases);
    return 0;
}
