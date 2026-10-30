// SPDX-License-Identifier: AGPL-3.0-or-later
/* The kernel that stamps a literal at its source and copies it to its destination, the source the
 * theorem DN.Compiler.Components.stampCopy_run runs in the model: at every pair of offsets in two
 * buffers, the literal at both and every other byte as it was; and with each buffer ending where a
 * page with no access begins, so that a byte written past either faults. The buffers are this
 * program's, outside CakeML's heap, where the theorem assumes them (docs/assurance.md, item 8). */
#define _GNU_SOURCE
#include "cake_runtime.h"
#include "host.h"
#include <inttypes.h>
extern uint32_t dn_stamp_copy(uint64_t, uint64_t);

/* The literal of DN.Compiler.Kernels.stampLiteral, written down again here. */
static const unsigned char literal[] = {'d', 'r', 'a', 'g', 'o', 'n', 's'};
enum { LEN = sizeof literal, ROOM = 64 };

static void held(const unsigned char *buffer, size_t size, size_t at, unsigned char fill, const char *what) {
    for (size_t i = 0; i < size; ++i) {
        unsigned char expected = i >= at && i - at < LEN ? literal[i - at] : fill;
        if (buffer[i] != expected) dn_violation("%s mismatch", what);
    }
}

int main(void) {
    dn_expect_faults();
    dn_runtime_init();
    unsigned char source[ROOM], destination[ROOM];
    uint64_t cases = 0;
    for (size_t a = 0; a + LEN <= ROOM; ++a)
        for (size_t b = 0; b + LEN <= ROOM; ++b) {
            memset(source, 0x5a, ROOM);
            memset(destination, 0xa5, ROOM);
            if (dn_stamp_copy((uintptr_t)(source + a), (uintptr_t)(destination + b)) != LEN)
                dn_violation("stamp length mismatch");
            held(source, ROOM, a, 0x5a, "stamp/frame");
            held(destination, ROOM, b, 0xa5, "copy/frame");
            ++cases;
        }
    size_t page_size = dn_page_size();
    unsigned char *first = dn_guarded(), *second = dn_guarded();
    memset(first, 0x5a, page_size);
    memset(second, 0xa5, page_size);
    if (dn_stamp_copy((uintptr_t)(first + page_size - LEN), (uintptr_t)(second + page_size - LEN)) != LEN)
        dn_violation("stamp length mismatch at the end of a page");
    held(first, page_size, page_size - LEN, 0x5a, "stamp/frame");
    held(second, page_size, page_size - LEN, 0xa5, "copy/frame");
    ++cases;
    dn_unguard(first);
    dn_unguard(second);
    printf("{\"stamp_cases\":%" PRIu64 "}\n", cases);
    return 0;
}
