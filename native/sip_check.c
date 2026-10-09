/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The emitted SipHash-2-4 against the authors' algorithm written out here, on the 64 vectors of
 * their `vectors.h` (`KEY MSG TAG` lines on standard input) and on keys and messages drawn up to
 * 65,536 octets, each ending at a page without access; nothing but the tag's word may change. */
#define _GNU_SOURCE
#include "cake_runtime.h"
#include "host.h"
#include <inttypes.h>
extern uint32_t dn_siphash(uint64_t k, uint64_t p, uint64_t n, uint64_t out);

#define ROTL(x, b) (((x) << (b)) | ((x) >> (64 - (b))))

static void sip_round(uint64_t v[4]) {
    v[0] += v[1], v[1] = ROTL(v[1], 13) ^ v[0], v[0] = ROTL(v[0], 32);
    v[2] += v[3], v[3] = ROTL(v[3], 16) ^ v[2];
    v[0] += v[3], v[3] = ROTL(v[3], 21) ^ v[0];
    v[2] += v[1], v[1] = ROTL(v[1], 17) ^ v[2], v[2] = ROTL(v[2], 32);
}

static uint64_t le64(const unsigned char *p) {
    uint64_t w = 0;
    for (int i = 7; i >= 0; --i) w = w << 8 | p[i];
    return w;
}

static uint64_t reference(const unsigned char *key, const unsigned char *m, size_t n) {
    uint64_t k0 = le64(key), k1 = le64(key + 8);
    uint64_t v[4] = {k0 ^ 0x736f6d6570736575ULL, k1 ^ 0x646f72616e646f6dULL, k0 ^ 0x6c7967656e657261ULL,
                     k1 ^ 0x7465646279746573ULL};
    size_t i = 0;
    for (; i + 8 <= n; i += 8) {
        uint64_t w = le64(m + i);
        v[3] ^= w, sip_round(v), sip_round(v), v[0] ^= w;
    }
    uint64_t b = (uint64_t)n << 56;
    for (size_t j = 0; i + j < n; ++j) b |= (uint64_t)m[i + j] << (8 * j);
    v[3] ^= b, sip_round(v), sip_round(v), v[0] ^= b;
    v[2] ^= 0xff, sip_round(v), sip_round(v), sip_round(v), sip_round(v);
    return v[0] ^ v[1] ^ v[2] ^ v[3];
}

static uint64_t splitmix(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

/* One message: the tag must be the reference's and `expected`, unless that is `UINT64_MAX`, and
   only the tag's word may change. */
static void check(unsigned char *out_page, const unsigned char *key, const unsigned char *msg, size_t n,
                  uint64_t expected) {
    struct dn_span k = dn_before_guard(16), m = dn_before_guard(n);
    memcpy(k.data, key, 16);
    memcpy(m.data, msg, n);
    memset(out_page, 0xa5, dn_page_size());
    dn_siphash((uintptr_t)k.data, (uintptr_t)m.data, n, (uintptr_t)(out_page + 64));
    uint64_t got, want = reference(key, msg, n);
    memcpy(&got, out_page + 64, 8);
    if (expected != UINT64_MAX && want != expected)
        dn_harness("the reference gives %016" PRIx64 " where the authors print %016" PRIx64, want, expected);
    if (got != want) dn_violation("SipHash of %zu bytes: %016" PRIx64 ", not %016" PRIx64, n, got, want);
    for (size_t i = 0; i < dn_page_size(); ++i)
        if ((i < 64 || i >= 72) && out_page[i] != 0xa5) dn_violation("a byte beside the tag changed");
    if (memcmp(k.data, key, 16) || memcmp(m.data, msg, n)) dn_violation("the key or the message changed");
    dn_unmap(k);
    dn_unmap(m);
}

static void unhex(const char *text, unsigned char *out, size_t room, size_t *n) {
    size_t len = strlen(text);
    if (len % 2 || len / 2 > room) dn_harness("odd or excessive hexadecimal");
    for (size_t i = 0; i < len / 2; ++i) {
        unsigned v;
        if (sscanf(text + 2 * i, "%2x", &v) != 1) dn_harness("not hexadecimal: %s", text);
        out[i] = (unsigned char)v;
    }
    *n = len / 2;
}

int main(void) {
    dn_expect_faults();
    dn_runtime_init();
    unsigned char *out_page = dn_guarded();
    static unsigned char key[16], msg[65536];
    uint64_t cases = 0, vectors = 0, state = 2;
    static char line[2 * sizeof msg + 128];
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\n")] = 0;
        char *first = strchr(line, ' '), *second = first ? strchr(first + 1, ' ') : NULL;
        if (!second) dn_harness("a vector not of three fields");
        *first = *second = 0;
        size_t klen, n;
        unhex(line, key, sizeof key, &klen);
        if (klen != 16) dn_harness("a key not of sixteen octets");
        unhex(first + 1, msg, sizeof msg, &n);
        check(out_page, key, msg, n, dn_parse_u64(second + 1, UINT64_MAX - 1));
        ++vectors;
    }
    static const size_t longer[] = {1390, 1400, 4096, 4097, 65536};
    for (size_t k = 0; k < 301 + sizeof longer / sizeof longer[0]; ++k) {
        size_t n = k < 301 ? k : longer[k - 301];
        for (size_t i = 0; i < 16; ++i) key[i] = (unsigned char)splitmix(&state);
        for (size_t i = 0; i < n; ++i) msg[i] = (unsigned char)splitmix(&state);
        check(out_page, key, msg, n, UINT64_MAX);
        ++cases;
    }
    printf("{\"sip_vectors\": %" PRIu64 ", \"sip_cases\": %" PRIu64 "}\n", vectors, cases + vectors);
    return 0;
}
