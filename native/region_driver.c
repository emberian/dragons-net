/* SPDX-License-Identifier: AGPL-3.0-or-later
 * Trusted test adapter for the emitted kernel. No networking or fallback.
 * This executable tests the ABI and bytes; it is not a verified runtime. */
#define _GNU_SOURCE
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys/mman.h>
#include <unistd.h>

#include "cake_runtime.h"

extern uint32_t dn_region(uint64_t, uint64_t, uint64_t, uint64_t);

static uint64_t reference(const unsigned char *bytes, size_t off, size_t len) {
    uint64_t result = 0;
    for (size_t i = 0; i < len; ++i) result = (result * 31 + bytes[off + i]) & 0xffffff;
    return result;
}

static uint64_t invoke(const unsigned char *bytes, size_t size, size_t off, size_t len) {
    uint64_t ctrl[2] = {size, off};
    uint64_t out[3] = {0xcafebabefeedfaceULL, 0, 0x0123456789abcdefULL};
    uint64_t result = dn_region((uintptr_t)ctrl, (uintptr_t)bytes, len, (uintptr_t)&out[1]);
    if (out[0] != 0xcafebabefeedfaceULL || out[2] != 0x0123456789abcdefULL || out[1] != result) {
        fputs("output/return contract violated\n", stderr); exit(1);
    }
    return result;
}

static uint64_t now_ns(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t) != 0) abort();
    return (uint64_t)t.tv_sec * 1000000000 + (uint64_t)t.tv_nsec;
}

int main(void) {
    dn_runtime_init();

    unsigned char bytes[4096];
    uint64_t random = 0x12345678, vectors = 0;
    for (size_t i = 0; i < sizeof(bytes); ++i) {
        random = random * 6364136223846793005ULL + 1;
        bytes[i] = (unsigned char)(random >> 32);
    }
    for (size_t size = 0; size <= 64; ++size)
        for (size_t off = 0; off <= size + 1; ++off)
            for (size_t len = 0; len <= size + 1; ++len) {
                uint64_t expected = off + len > size ? 0xffffffff : reference(bytes, off, len);
                if (invoke(bytes, size, off, len) != expected) {
                    fprintf(stderr, "mismatch size=%zu off=%zu len=%zu\n", size, off, len); return 1;
                }
                ++vectors;
            }
    for (size_t i = 0; i < 1024; ++i) {
        random = random * 6364136223846793005ULL + 1;
        size_t off = (random >> 32) % sizeof(bytes);
        size_t len = sizeof(bytes) - off;
        if (invoke(bytes, sizeof(bytes), off, len) != reference(bytes, off, len)) return 1;
        ++vectors;
    }
    /* Sign-bit and wrapping-sum regressions. Rejected inputs get an unreadable
     * buffer: an accidental scan faults instead of reading benign test memory. */
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    void *guard = mmap(NULL, page, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (guard == MAP_FAILED) return 1;
    uint64_t sizes[] = {0, sizeof(bytes), 1ULL<<63, UINT64_MAX};
    uint64_t edges[] = {0, 1, 4096, 4097, (1ULL<<63)-1, 1ULL<<63, UINT64_MAX};
    for (size_t a = 0; a < sizeof(sizes)/sizeof(sizes[0]); ++a)
        for (size_t b = 0; b < sizeof(edges)/sizeof(edges[0]); ++b)
            for (size_t c = 0; c < sizeof(edges)/sizeof(edges[0]); ++c) {
                uint64_t size = sizes[a], off = edges[b], len = edges[c];
                int valid = size < (1ULL<<63) && off <= size && len <= size - off;
                uint64_t expected = valid ? reference(bytes, off, len) : 0xffffffff;
                if (invoke(valid ? bytes : guard, size, off, len) != expected) {
                    fputs("64-bit bounds mismatch\n", stderr); return 1;
                }
                ++vectors;
            }
    munmap(guard, page);
    const size_t iterations = 25000;
    uint64_t start = now_ns(), checksum = 0;
    for (size_t i = 0; i < iterations; ++i)
        checksum += invoke(bytes, sizeof(bytes), 0, sizeof(bytes));
    uint64_t elapsed = now_ns() - start;
    printf("{\"vectors\":%" PRIu64 ",\"bytes\":%zu,\"elapsed_ns\":%" PRIu64
           ",\"checksum\":%" PRIu64 ",\"heap_bytes\":%zu,\"stack_bytes\":%zu}\n",
           vectors, iterations * sizeof(bytes), elapsed, checksum,
           (size_t)DN_RUNTIME_SEGMENT_BYTES, (size_t)DN_RUNTIME_SEGMENT_BYTES);
    return 0;
}
