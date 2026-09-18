#define _GNU_SOURCE
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
            memset(destination, 0xa5, sizeof(destination));
            if (dn_echo((uintptr_t)(source+a), (uintptr_t)(destination+b), len, len) != len) return 1;
            for (size_t i = 0; i < sizeof(destination); ++i) {
                unsigned char expected = i >= b && i - b < len ? source[a+i-b] : 0xa5;
                if (destination[i] != expected) { fputs("copy/frame mismatch\n", stderr); return 1; }
            }
            ++cases;
        }
    /* Rejected lengths must not dereference either pointer. */
    size_t page = (size_t)sysconf(_SC_PAGESIZE);
    void *guard = mmap(NULL, page, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (guard == MAP_FAILED) return 1;
    uint64_t bad[][2] = {{1,0}, {4097,4096}, {UINT64_MAX,4096}, {1ULL<<63,4096},
                         {0,UINT64_MAX}, {0,1ULL<<63}};
    for (size_t i = 0; i < sizeof(bad)/sizeof(bad[0]); ++i) {
        if (dn_echo((uintptr_t)guard, (uintptr_t)guard, bad[i][0], bad[i][1]) != UINT32_MAX) return 1;
        ++cases;
    }
    if (dn_echo((uintptr_t)guard, (uintptr_t)guard, 0, 0) != 0) return 1;
    ++cases;
    munmap(guard, page);
    printf("{\"copy_cases\":%" PRIu64 "}\n", cases);
    return 0;
}
