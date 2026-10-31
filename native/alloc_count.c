// SPDX-License-Identifier: AGPL-3.0-or-later
/*
 * Loaded with LD_PRELOAD, counts a process's heap allocations into the file DN_ALLOC_FILE names,
 * which it maps shared, so that they can be read at any moment and whatever way the process ends:
 * three little-endian 64-bit counts, allocations (a realloc is one), octets asked, and frees. What
 * comes before the file is mapped is not counted, nor memory taken by mmap directly; how much is
 * live at most is the process's VmHWM.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

struct counts {
    uint64_t allocations, asked, frees;
};

static struct counts *counts;
static void *(*real_malloc)(size_t);
static void *(*real_calloc)(size_t, size_t);
static void *(*real_realloc)(void *, size_t);
static void (*real_free)(void *);
static int (*real_posix_memalign)(void **, size_t, size_t);
static void *(*real_aligned_alloc)(size_t, size_t);
static void *(*real_memalign)(size_t, size_t);
static void *(*real_valloc)(size_t);
static void *(*real_pvalloc)(size_t);

/* dlsym may allocate with calloc before calloc is found: from here, never freed. */
static _Alignas(16) unsigned char early[4096];
static size_t early_used;
static int resolving;

static int is_early(const void *p) {
    return (const unsigned char *)p >= early && (const unsigned char *)p < early + sizeof early;
}

static void resolve(void) {
    if (real_malloc || resolving) return;
    resolving = 1;
    real_calloc = (void *(*)(size_t, size_t))dlsym(RTLD_NEXT, "calloc");
    real_malloc = (void *(*)(size_t))dlsym(RTLD_NEXT, "malloc");
    real_realloc = (void *(*)(void *, size_t))dlsym(RTLD_NEXT, "realloc");
    real_free = (void (*)(void *))dlsym(RTLD_NEXT, "free");
    real_posix_memalign = (int (*)(void **, size_t, size_t))dlsym(RTLD_NEXT, "posix_memalign");
    real_aligned_alloc = (void *(*)(size_t, size_t))dlsym(RTLD_NEXT, "aligned_alloc");
    real_memalign = (void *(*)(size_t, size_t))dlsym(RTLD_NEXT, "memalign");
    real_valloc = (void *(*)(size_t))dlsym(RTLD_NEXT, "valloc");
    real_pvalloc = (void *(*)(size_t))dlsym(RTLD_NEXT, "pvalloc");
    resolving = 0;
}

__attribute__((constructor)) static void map_counts(void) {
    resolve();
    const char *path = getenv("DN_ALLOC_FILE");
    if (!path) return;
    int fd = open(path, O_RDWR | O_CREAT | O_CLOEXEC, 0600);
    if (fd < 0) return;
    if (ftruncate(fd, sizeof *counts) == 0) {
        void *m = mmap(NULL, sizeof *counts, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
        if (m != MAP_FAILED) counts = m;
    }
    close(fd);
}

static void taken(const void *p, size_t asked) {
    if (!p || !counts || is_early(p)) return;
    __atomic_add_fetch(&counts->allocations, 1, __ATOMIC_RELAXED);
    __atomic_add_fetch(&counts->asked, asked, __ATOMIC_RELAXED);
}

static void given_back(void) {
    if (counts) __atomic_add_fetch(&counts->frees, 1, __ATOMIC_RELAXED);
}

void *calloc(size_t n, size_t size) {
    if (!real_calloc) {
        resolve();
        if (!real_calloc) {
            size_t want = n && size > SIZE_MAX / n ? SIZE_MAX : (n * size + 15) & ~(size_t)15;
            if (want > sizeof early - early_used) return NULL;
            void *p = early + early_used;
            early_used += want;
            return p;
        }
    }
    void *p = real_calloc(n, size);
    taken(p, n * size);
    return p;
}

void *malloc(size_t size) {
    resolve();
    void *p = real_malloc(size);
    taken(p, size);
    return p;
}

void free(void *p) {
    if (!p || is_early(p)) return;
    resolve();
    given_back();
    real_free(p);
}

void *realloc(void *p, size_t size) {
    resolve();
    if (is_early(p)) {
        size_t room = (size_t)(early + sizeof early - (unsigned char *)p);
        void *q = malloc(size);
        if (q) memcpy(q, p, size < room ? size : room);
        return q;
    }
    void *q = real_realloc(p, size);
    if (p && (q || !size)) given_back();
    taken(q, size);
    return q;
}

int posix_memalign(void **out, size_t alignment, size_t size) {
    resolve();
    int done = real_posix_memalign(out, alignment, size);
    if (!done) taken(*out, size);
    return done;
}

void *aligned_alloc(size_t alignment, size_t size) {
    resolve();
    void *p = real_aligned_alloc(alignment, size);
    taken(p, size);
    return p;
}

void *memalign(size_t alignment, size_t size) {
    resolve();
    void *p = real_memalign(alignment, size);
    taken(p, size);
    return p;
}

void *valloc(size_t size) {
    resolve();
    void *p = real_valloc(size);
    taken(p, size);
    return p;
}

void *pvalloc(size_t size) {
    resolve();
    void *p = real_pvalloc(size);
    taken(p, size);
    return p;
}
