/* SPDX-License-Identifier: AGPL-3.0-or-later
 * The emitted CRC-32C against a bitwise one (RFC 7143 §13.1), on the examples of its appendix A.4
 * (`HEX CRC` lines on standard input) and on buffers of every length to 300 and some longer, each
 * ending at a page without access; the table the call builds must hold eight shifts of each octet,
 * and nothing past it or in the buffer may change. */
#define _GNU_SOURCE
#include "cake_runtime.h"
#include "host.h"
#include <inttypes.h>
extern uint32_t dn_crc32c(uint64_t t, uint64_t p, uint64_t n);

static uint32_t shifted(uint32_t c) {
    for (int k = 0; k < 8; ++k) c = (c & 1) ? (c >> 1) ^ 0x82F63B78u : c >> 1;
    return c;
}

static uint32_t reference(const unsigned char *p, size_t n) {
    uint32_t c = 0xFFFFFFFFu;
    for (size_t i = 0; i < n; ++i) c = shifted(c ^ p[i]);
    return c ^ 0xFFFFFFFFu;
}

/* `n` bytes that end where a page without access begins, in a mapping of `size` bytes. */
struct guarded {
    unsigned char *map, *data;
    size_t size;
};

static struct guarded before_guard(size_t n) {
    size_t page = dn_page_size(), pages = (n + page - 1) / page + 1;
    unsigned char *map = mmap(NULL, pages * page, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (map == MAP_FAILED) dn_harness("mmap: %s", strerror(errno));
    dn_protect(map + (pages - 1) * page, PROT_NONE);
    return (struct guarded){map, map + (pages - 1) * page - n, pages * page};
}

static uint64_t splitmix(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

/* One buffer: the CRC must be the reference's and `expected`, unless that is `UINT64_MAX`; the
   table must be built, and nothing else written. */
static void check(unsigned char *table_page, const unsigned char *data, size_t n, uint64_t expected) {
    struct guarded g = before_guard(n);
    unsigned char *buffer = g.data;
    memcpy(buffer, data, n);
    memset(table_page, 0xa5, dn_page_size());
    uint32_t got = dn_crc32c((uintptr_t)table_page, (uintptr_t)buffer, n);
    uint32_t want = reference(data, n);
    if (expected != UINT64_MAX && want != expected)
        dn_harness("the reference gives %08" PRIx32 " where RFC 7143 prints %08" PRIx64, want, expected);
    if (got != want) dn_violation("CRC-32C of %zu bytes: %08" PRIx32 ", not %08" PRIx32, n, got, want);
    for (uint32_t i = 0; i < 256; ++i) {
        uint64_t word;
        memcpy(&word, table_page + 8 * i, 8);
        if (word != shifted(i)) dn_violation("table word %" PRIu32 " is %016" PRIx64, i, word);
    }
    for (size_t i = 2048; i < dn_page_size(); ++i)
        if (table_page[i] != 0xa5) dn_violation("a byte past the table changed");
    if (memcmp(buffer, data, n)) dn_violation("the buffer changed");
    if (munmap(g.map, g.size)) dn_harness("munmap: %s", strerror(errno));
}

int main(void) {
    dn_expect_faults();
    dn_runtime_init();
    unsigned char *table_page = dn_guarded();
    static unsigned char data[1000000];
    uint64_t cases = 0, examples = 0, state = 1;
    char line[4096];
    while (fgets(line, sizeof line, stdin)) {
        line[strcspn(line, "\n")] = 0;
        char *space = strchr(line, ' ');
        if (!space) dn_harness("an example without its CRC");
        *space = 0;
        size_t n = strlen(line) / 2;
        if (strlen(line) % 2 || n > sizeof data) dn_harness("an example of odd or excessive length");
        for (size_t i = 0; i < n; ++i) {
            unsigned v;
            if (sscanf(line + 2 * i, "%2x", &v) != 1) dn_harness("an example not in hexadecimal");
            data[i] = (unsigned char)v;
        }
        check(table_page, data, n, dn_parse_u64(space + 1, UINT32_MAX));
        ++examples;
    }
    for (size_t n = 0; n <= 300; ++n) {
        for (size_t i = 0; i < n; ++i) data[i] = (unsigned char)splitmix(&state);
        check(table_page, data, n, UINT64_MAX);
        ++cases;
    }
    static const size_t longer[] = {4095, 4096, 4097, 16384, 1000000};
    for (size_t k = 0; k < sizeof longer / sizeof longer[0]; ++k) {
        for (size_t i = 0; i < longer[k]; ++i) data[i] = (unsigned char)splitmix(&state);
        check(table_page, data, longer[k], UINT64_MAX);
        ++cases;
    }
    printf("{\"crc_examples\": %" PRIu64 ", \"crc_cases\": %" PRIu64 "}\n", examples, cases + examples);
    return 0;
}
