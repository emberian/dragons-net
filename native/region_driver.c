/* SPDX-License-Identifier: AGPL-3.0-or-later
 * Trusted test adapter for the emitted kernel. No networking or fallback.
 * This executable tests the ABI and bytes; it is not a verified runtime. */
#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

extern void *cml_heap, *cml_stack, *cml_stackend;
extern void cml_main(void);
extern uint64_t dn_region(uint64_t, uint64_t, uint64_t, uint64_t);

void cml_clear(void) {}
void cml_err(int code) { fprintf(stderr, "Cake runtime error %d\n", code); abort(); }
void cml_exit(int code) { fprintf(stderr, "unexpected Cake exit %d\n", code); abort(); }

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
    const size_t heap_size = 1024 * 1024, stack_size = 1024 * 1024;
    unsigned char *region = malloc(heap_size + stack_size);
    if (!region) return 1;
    cml_heap = region;
    cml_stack = region + heap_size;
    cml_stackend = region + heap_size + stack_size;
    cml_main();

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
    const size_t iterations = 25000;
    uint64_t start = now_ns(), checksum = 0;
    for (size_t i = 0; i < iterations; ++i)
        checksum += invoke(bytes, sizeof(bytes), 0, sizeof(bytes));
    uint64_t elapsed = now_ns() - start;
    printf("{\"vectors\":%" PRIu64 ",\"bytes\":%zu,\"elapsed_ns\":%" PRIu64
           ",\"checksum\":%" PRIu64 ",\"heap_bytes\":%zu,\"stack_bytes\":%zu}\n",
           vectors, iterations * sizeof(bytes), elapsed, checksum, heap_size, stack_size);
    free(region);
    return 0;
}
