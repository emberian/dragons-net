/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The emitted decimal render against the C library's own, on a fixed corpus. */
#define _GNU_SOURCE
#include "cake_runtime.h"
#include "host.h"
#include <inttypes.h>
extern uint32_t dn_render(uint64_t, uint64_t);

/* One number: the digits must equal the C library's own, and nothing outside them may
   change. */
static void check(uint64_t value, unsigned char *buffer) {
    memset(buffer, 0xa5, 64);
    unsigned char *end = buffer + 40;
    uint32_t written = dn_render(value, (uintptr_t)end);
    char expected[32];
    int expected_len = snprintf(expected, sizeof(expected), "%" PRIu64, value);
    if (expected_len < 0 || (uint32_t)expected_len != written ||
        memcmp(end - written, expected, (size_t)expected_len))
        dn_violation("render mismatch for %" PRIu64 ": wrote %" PRIu32 " bytes, expected %s", value,
                     written, expected);
    for (size_t i = 0; i < 64; ++i) {
        unsigned char *at = buffer + i;
        if (at >= end - written && at < end) continue;
        if (*at != 0xa5) dn_violation("render touched a byte outside its digits");
    }
}

int main(void) {
    dn_expect_faults();
    dn_runtime_init();
    /* A page with no access right where the digits end: a render that walks past its
       buffer faults instead of quietly overwriting the caller's frame. */
    unsigned char *page = dn_guarded(), *guarded_end = page + dn_page_size();
    unsigned char buffer[64];
    uint64_t cases = 0, random = 0x9e3779b97f4a7c15ULL;

    /* The quotient is built half by half, so the corpus has to move the high half as well
       as the low one: an error in the multiplier shows up only for some high halves. */
    static const uint64_t low_parts[] = {0, 1, 2, 9, 10, 11, 99, 2147483647ULL,
                                         2147483648ULL, 4294967294ULL, 4294967295ULL};
    static const uint64_t high_parts[] = {0, 1, 2, 3, 9, 10, 11, 19, 20, 99, 100, 101,
                                          999, 1000, 65535, 1000000, 2147483647ULL,
                                          4294967294ULL, 4294967295ULL};

    for (size_t h = 0; h < sizeof(high_parts)/sizeof(high_parts[0]); ++h)
        for (size_t l = 0; l < sizeof(low_parts)/sizeof(low_parts[0]); ++l) {
            uint64_t value = high_parts[h] * 4294967296ULL + low_parts[l];
            check(value, buffer);
            ++cases;
        }
    for (unsigned bit = 0; bit < 64; ++bit) {
        uint64_t power = 1ULL << bit;
        check(power, buffer);
        check(power - 1, buffer);
        cases += 2;
        if (bit < 63) {
            check(power + 1, buffer);
            ++cases;
        }
    }
    for (size_t round = 0; round < 512; ++round) {
        random = random * 6364136223846793005ULL + 1442695040888963407ULL;
        check(random >> (round % 64), buffer);
        ++cases;
    }
    /* Once more against the guard page, so a runaway loop faults instead of scribbling. */
    for (size_t round = 0; round < 64; ++round) {
        uint64_t value = round < 32 ? (1ULL << round) : random >> (round % 60);
        char expected[32];
        int expected_len = snprintf(expected, sizeof(expected), "%" PRIu64, value);
        uint32_t written = dn_render(value, (uintptr_t)guarded_end);
        if (expected_len < 0 || (uint32_t)expected_len != written ||
            memcmp(guarded_end - written, expected, (size_t)expected_len))
            dn_violation("render mismatch at the guard page for %" PRIu64, value);
        ++cases;
    }
    dn_unguard(page);
    printf("{\"render_cases\":%" PRIu64 "}\n", cases);
    return 0;
}
