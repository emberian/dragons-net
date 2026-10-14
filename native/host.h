/* SPDX-License-Identifier: AGPL-3.0-or-later
 * What the native hosts share. A host ends with status 1 when the code it checks does something
 * it must not (`dn_violation`) and with status 2 when the host itself cannot go on: bad input, a
 * failed system call (`dn_harness`); either way with a message. Also: a page between two pages
 * without access, a strict number, words in memory, and a process whose expected faults leave no
 * core dump behind. */
#ifndef DN_HOST_H
#define DN_HOST_H
#include <errno.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <unistd.h>

__attribute__((noreturn)) static inline void dn_end(int status, const char *format, va_list args) {
    vfprintf(stderr, format, args);
    fputc('\n', stderr);
    exit(status);
}

/* The code under test did what it must not. */
__attribute__((noreturn, format(printf, 1, 2))) static inline void dn_violation(const char *format, ...) {
    va_list args;
    va_start(args, format);
    dn_end(1, format, args);
}

/* The host cannot go on: its input or the system failed it. */
__attribute__((noreturn, format(printf, 1, 2))) static inline void dn_harness(const char *format, ...) {
    va_list args;
    va_start(args, format);
    dn_end(2, format, args);
}

/* The same from a thread other than the main one, which may hold a lock of stdio: the message is
   written as it is and the process ends without flushing anything. */
__attribute__((noreturn, format(printf, 1, 2))) static inline void dn_harness_now(const char *format, ...) {
    char text[512];
    va_list args;
    va_start(args, format);
    int n = vsnprintf(text, sizeof text - 1, format, args);
    va_end(args);
    size_t len = n < 0 ? 0 : (size_t)n < sizeof text - 1 ? (size_t)n : sizeof text - 2;
    text[len++] = '\n';
    for (size_t done = 0; done < len;) {
        ssize_t w = write(STDERR_FILENO, text + done, len - done);
        if (w <= 0 && errno != EINTR) break;
        if (w > 0) done += (size_t)w;
    }
    _exit(2);
}

/* A call that faults is an outcome the host reports, not a crash to keep: without this, every
   expected fault is written out as a core dump. */
static inline void dn_expect_faults(void) {
    if (prctl(PR_SET_DUMPABLE, 0)) dn_harness("prctl: %s", strerror(errno));
}

static inline size_t dn_page_size(void) {
    long size = sysconf(_SC_PAGESIZE);
    if (size <= 0) dn_harness("sysconf: %s", strerror(errno));
    return (size_t)size;
}

static inline void dn_protect(unsigned char *page, int access) {
    if (mprotect(page, dn_page_size(), access)) dn_harness("mprotect: %s", strerror(errno));
}

/* The middle one of three pages; the outer two have no access. */
static inline unsigned char *dn_guarded(void) {
    size_t page = dn_page_size();
    unsigned char *pages = mmap(NULL, 3 * page, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (pages == MAP_FAILED) dn_harness("mmap: %s", strerror(errno));
    dn_protect(pages + page, PROT_READ | PROT_WRITE);
    return pages + page;
}

static inline void dn_unguard(unsigned char *page) {
    size_t size = dn_page_size();
    if (munmap(page - size, 3 * size)) dn_harness("munmap: %s", strerror(errno));
}

/* A page without access, for an argument no call may touch. */
static inline unsigned char *dn_inaccessible(void) {
    unsigned char *page = mmap(NULL, dn_page_size(), PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (page == MAP_FAILED) dn_harness("mmap: %s", strerror(errno));
    return page;
}

/* `n` bytes that end where a page without access begins, in a mapping of `size` bytes. */
struct dn_span {
    unsigned char *map, *data;
    size_t size;
};

static inline struct dn_span dn_before_guard(size_t n) {
    size_t page = dn_page_size(), pages = (n + page - 1) / page + 1;
    unsigned char *map = mmap(NULL, pages * page, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (map == MAP_FAILED) dn_harness("mmap: %s", strerror(errno));
    dn_protect(map + (pages - 1) * page, PROT_NONE);
    return (struct dn_span){map, map + (pages - 1) * page - n, pages * page};
}

static inline void dn_unmap(struct dn_span g) {
    if (munmap(g.map, g.size)) dn_harness("munmap: %s", strerror(errno));
}

/* A decimal number from 0 to `max`, or the host ends. */
static inline uint64_t dn_parse_u64(const char *text, uint64_t max) {
    char *end;
    errno = 0;
    unsigned long long value = strtoull(text, &end, 10);
    if (text[0] < '0' || text[0] > '9' || errno || *end || value > max)
        dn_harness("not a number from 0 to %llu: %s", (unsigned long long)max, text);
    return value;
}

static inline uint64_t dn_word(const unsigned char *p) {
    uint64_t value;
    memcpy(&value, p, sizeof value);
    return value;
}

static inline void dn_put_word(unsigned char *p, uint64_t value) { memcpy(p, &value, sizeof value); }

#endif
