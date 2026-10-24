/* SPDX-License-Identifier: AGPL-3.0-or-later
 * File jobs; see jobs.h. A job is checked when it is taken, inside dn_emit, and copied out of the
 * heap with the bytes it writes; a worker takes it from a queue and runs it without the lock, on
 * files no other job in flight may name; the bytes it reads go back into the heap inside dn_next.
 * Names are made from a kind and a number as DN.News.Journal makes them, relative to the spool. The
 * directory's names are read when it is opened and listed from that reading, whatever jobs do to the
 * directory after: POSIX leaves a name added or removed during a reading unspecified. A signal's
 * interruption is retried and never reported; a short write is written on, and one that makes no
 * progress fails as no space; a short read is reported as it is. A failed sync, or close of a file
 * written through its place, leaves the mark of store.c before the program learns of it. The test
 * build fails each operation at a point of its name (faults.h); `dn/write-short` shortens a write to
 * the number given, `dn/sync-slow` delays a sync by that many milliseconds, and `dn/stop` holds the
 * workers before the operation it numbers, counted from one over the run, and each after it: once
 * every operation before has ended, the loop stops the process at the end of its turn, for a test to
 * kill it with those operations and everything the program did in place. `dn/fail`, given the number
 * of an operation, so counted, times 256 and an error number, fails that operation at its first point
 * with the error, once, and names the point on stderr. */
#define _GNU_SOURCE
#include "jobs.h"
#include "dn_session_layout.h"
#include "faults.h"
#include "host.h"
#include "store.h"
#include <dirent.h>
#include <fcntl.h>
#include <inttypes.h>
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdlib.h>
#include <sys/eventfd.h>
#include <sys/stat.h>
#include <time.h>
#ifdef FIU_ENABLE
#include <fiu-control.h>
#endif

enum { JOBS = DN_SESSION_JOBS, OPS = DN_SESSION_JOB_OPS, DATA = DN_SESSION_JOB_DATA, PLACES = DN_SESSION_HANDLES,
       WORKERS = 2, NAME = 32 };
enum { FREE, QUEUED, DONE };

struct op { uint64_t code, place, gen, name, number, to_name, to_number, offset, length, at; };

struct job {
    int state, dir_sync;
    uint64_t gen, count, done, class, results[OPS][2];
    struct op ops[OPS];
    int place[OPS];   /* the place an operation that opens a file takes, reserved when the job is */
    int wrote[OPS];   /* whether the file a close closes was written through its place */
    unsigned char data[DATA];
};

struct file {
    int fd, open, busy, reserved, listing, written;
    unsigned char *names;   /* a listing's names, each a length octet and its bytes */
    uint64_t size, count, gen;
};

static struct job jobs[JOBS];
static struct file files[PLACES];
static int spool = -1, wake = -1, queue[JOBS], queued, dir_syncs;
static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t work = PTHREAD_COND_INITIALIZER;
static atomic_uint_fast64_t begun, ended, held;
#ifdef FIU_ENABLE
static uint64_t failing;
static _Thread_local uint64_t running;
static const char *const POINTS[] = {"dn/create", "dn/open", "dn/open-dir", "dn/read-dir", "dn/list", "dn/write",
                                     "dn/read", "dn/size", "dn/data-sync", "dn/sync", "dn/sync-dir", "dn/truncate",
                                     "dn/rename", "dn/remove", "dn/close"};

/* Whether a point fails now: in the worker running the operation `dn/fail` numbers, once, said. */
static int fails_now(const char *name, int *failnum, void **failinfo, unsigned *flags) {
    (void)failnum, (void)failinfo, (void)flags;
    if (!running || running != failing / 256) return 0;
    running = 0;
    dprintf(STDERR_FILENO, "dn/fail %s\n", name);
    return 1;
}
#endif

/* The operation a worker runs, by its number, for `dn/fail`. */
static void numbered(uint64_t number) {
#ifdef FIU_ENABLE
    running = number;
#else
    (void)number;
#endif
}

/* Whether a failure of the operation is a failed sync: a close is, as decision 0005 has it. */
static int syncs(uint64_t code) {
    return code == DN_SESSION_OP_DATA_SYNC || code == DN_SESSION_OP_SYNC || code == DN_SESSION_OP_SYNC_DIR ||
           code == DN_SESSION_OP_CLOSE;
}

static int names_file(uint64_t code) { return code == DN_SESSION_OP_CREATE || code == DN_SESSION_OP_OPEN; }

static int opens(uint64_t code) { return names_file(code) || code == DN_SESSION_OP_OPEN_DIR; }

static int on_file(uint64_t code) {
    return code == DN_SESSION_OP_WRITE || code == DN_SESSION_OP_READ || code == DN_SESSION_OP_SIZE ||
           code == DN_SESSION_OP_DATA_SYNC || code == DN_SESSION_OP_SYNC || code == DN_SESSION_OP_TRUNCATE ||
           code == DN_SESSION_OP_LIST || code == DN_SESSION_OP_CLOSE;
}

/* The name a kind and a number make. */
static void name_of(uint64_t kind, uint64_t number, char name[NAME]) {
    static const char letters[] = {[DN_SESSION_NAME_FINAL] = 'a', [DN_SESSION_NAME_TEMP] = 't',
                                   [DN_SESSION_NAME_QUARANTINE] = 'q', [DN_SESSION_NAME_TAIL] = 'j'};
    if (kind == DN_SESSION_NAME_JOURNAL) snprintf(name, NAME, "journal");
    else snprintf(name, NAME, "%c%016" PRIx64, letters[kind], number);
}

static void check_name(int k, uint64_t kind, uint64_t number) {
    if (kind < DN_SESSION_NAME_JOURNAL || kind > DN_SESSION_NAME_TAIL || (kind == DN_SESSION_NAME_JOURNAL && number))
        dn_violation("dn_emit: job %d names kind %" PRIu64 " number %" PRIu64, k, kind, number);
}

/* Inside dn_emit, under the lock: the job in slot `k`, checked, copied and queued. */
static void take(int k, const unsigned char *slot) {
    struct job *j = &jobs[k];
    if (j->state != FREE) dn_violation("dn_emit: job %d is still in flight", k);
    j->gen = dn_word(slot + DN_SESSION_JOB_GEN);
    j->count = dn_word(slot + DN_SESSION_JOB_COUNT);
    if (j->count < 1 || j->count > OPS) dn_violation("dn_emit: job %d of %" PRIu64 " operations", k, j->count);
    int closed[PLACES] = {0};
    j->dir_sync = 0;
    for (uint64_t i = 0; i < j->count; ++i) {
        const unsigned char *o = slot + DN_SESSION_JOB_OPS_AT + i * DN_SESSION_OP_SLOT;
        struct op *op = &j->ops[i];
        *op = (struct op){dn_word(o + DN_SESSION_OP_CODE), dn_word(o + DN_SESSION_OP_HANDLE),
                          dn_word(o + DN_SESSION_OP_HANDLE_GEN), dn_word(o + DN_SESSION_OP_NAME),
                          dn_word(o + DN_SESSION_OP_NUMBER), dn_word(o + DN_SESSION_OP_TO_NAME),
                          dn_word(o + DN_SESSION_OP_TO_NUMBER), dn_word(o + DN_SESSION_OP_OFFSET),
                          dn_word(o + DN_SESSION_OP_LENGTH), dn_word(o + DN_SESSION_OP_DATA)};
        j->place[i] = -1;
        if (op->code < DN_SESSION_OP_CREATE || op->code > DN_SESSION_OP_CLOSE)
            dn_violation("dn_emit: job %d, operation %" PRIu64 " of code %" PRIu64, k, i, op->code);
        if (names_file(op->code) || op->code == DN_SESSION_OP_REMOVE || op->code == DN_SESSION_OP_RENAME)
            check_name(k, op->name, op->number);
        if (op->code == DN_SESSION_OP_RENAME) check_name(k, op->to_name, op->to_number);
        /* The store never removes its journal or renames it, or onto it. */
        if ((op->code == DN_SESSION_OP_REMOVE || op->code == DN_SESSION_OP_RENAME) &&
            (op->name == DN_SESSION_NAME_JOURNAL ||
             (op->code == DN_SESSION_OP_RENAME && op->to_name == DN_SESSION_NAME_JOURNAL)))
            dn_violation("dn_emit: job %d removes or renames the journal", k);
        if ((op->code == DN_SESSION_OP_WRITE || op->code == DN_SESSION_OP_READ || op->code == DN_SESSION_OP_LIST) &&
            (op->at > DATA || op->length > DATA - op->at || op->offset > INT64_MAX - op->length ||
             (op->code == DN_SESSION_OP_LIST && !op->length)))
            dn_violation("dn_emit: job %d, operation %" PRIu64 ": %" PRIu64 " bytes at %" PRIu64 " of its data",
                         k, i, op->length, op->at);
        if (op->code == DN_SESSION_OP_TRUNCATE && op->length > INT64_MAX)
            dn_violation("dn_emit: job %d truncates to %" PRIu64, k, op->length);
        if (op->code == DN_SESSION_OP_SYNC_DIR) j->dir_sync = 1;
        if (opens(op->code)) {
            /* A place closed by a job in flight is the program's until it learns of the close. */
            int p = 0;
            while (p < PLACES && (files[p].open || files[p].reserved || files[p].busy)) ++p;
            if (p == PLACES) dn_violation("dn_emit: job %d opens a file with all %d places taken", k, PLACES);
            files[p].reserved = 1;
            j->place[i] = p;
        }
        if (on_file(op->code)) {
            if (op->place >= PLACES) dn_violation("dn_emit: job %d names place %" PRIu64, k, op->place);
            struct file *f = &files[op->place];
            if (!f->open || f->gen != op->gen || closed[op->place])
                dn_violation("dn_emit: job %d names place %" PRIu64 " of generation %" PRIu64 ", not open", k,
                             op->place, op->gen);
            if (f->busy && f->busy != k + 1)
                dn_violation("dn_emit: job %d names place %" PRIu64 ", which a job in flight names", k, op->place);
            if ((op->code == DN_SESSION_OP_LIST) != f->listing && op->code != DN_SESSION_OP_CLOSE)
                dn_violation("dn_emit: job %d, operation %" PRIu64 " on place %" PRIu64 " of the other kind", k, i,
                             op->place);
            if (op->code == DN_SESSION_OP_LIST && op->offset > f->count)
                dn_violation("dn_emit: job %d lists from name %" PRIu64 " of %" PRIu64, k, op->offset, f->count);
            f->busy = k + 1;
            if (op->code == DN_SESSION_OP_CLOSE) closed[op->place] = 1;
        }
    }
    if (j->dir_sync && dir_syncs) dn_violation("dn_emit: job %d syncs the directory while another does", k);
    dir_syncs += j->dir_sync;
    memcpy(j->data, slot + DN_SESSION_JOB_HEAD, DATA);
    j->state = QUEUED;
    queue[queued++] = k;
    pthread_cond_signal(&work);
}

static uint64_t class_of(int error) {
    switch (error) {
    case EIO: return DN_SESSION_CLASS_IO;
    case ENOSPC:
    case EDQUOT: return DN_SESSION_CLASS_NO_SPACE;
    case EEXIST: return DN_SESSION_CLASS_EXISTS;
    case ENOENT: return DN_SESSION_CLASS_NOT_FOUND;
    default: return DN_SESSION_CLASS_OTHER;
    }
}

/* `call` until a signal does not interrupt it. */
#define RETRIED(call)                                                                                        \
    ({                                                                                                       \
        __typeof__(call) result_;                                                                            \
        do result_ = (call);                                                                                 \
        while (result_ < 0 && errno == EINTR);                                                               \
        result_;                                                                                             \
    })

/* Write all of `n` bytes at `offset`: a short write is written on, one of no byte fails as no space. */
static int write_all(int fd, const unsigned char *p, uint64_t n, uint64_t offset) {
    while (n) {
        uint64_t now = n;
        if (DN_FAULT_INFO("dn/write-short", now) && now > n) now = n;
        ssize_t w = RETRIED(DN_FAULT("dn/write") ? -1 : pwrite(fd, p, now, (off_t)offset));
        if (w < 0) return -1;
        if (w == 0) {
            errno = ENOSPC;
            return -1;
        }
        p += w;
        n -= (uint64_t)w;
        offset += (uint64_t)w;
    }
    return 0;
}

/* The names of the directory `fd` opens, without `.` and `..`, into `f`; the descriptor is closed. */
static int read_names(int fd, struct file *f) {
    DIR *dir = fdopendir(fd);
    if (!dir) {
        int error = errno;
        close(fd);
        errno = error;
        return -1;
    }
    uint64_t room = 0;
    for (;;) {
        errno = 0;
        struct dirent *e = DN_FAULT("dn/read-dir") ? NULL : readdir(dir);
        if (!e) break;
        if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
        size_t len = strlen(e->d_name);
        if (len > 255) {
            errno = ENAMETOOLONG;
            break;
        }
        if (f->size + 1 + len > room) {
            room = 2 * room + 4096;
            unsigned char *more = realloc(f->names, room);
            if (!more) break;
            f->names = more;
        }
        f->names[f->size] = (unsigned char)len;
        memcpy(f->names + f->size + 1, e->d_name, len);
        f->size += 1 + len;
        ++f->count;
    }
    int error = errno;
    closedir(dir);   /* read only: nothing to lose */
    if (!error) return 0;
    free(f->names);
    errno = error;
    return -1;
}

/* A page of the names of listing `f` from the `from`-th on, each a length octet and its bytes. */
static int list(const struct file *f, uint64_t from, unsigned char *page, uint64_t room, uint64_t result[2]) {
    uint64_t at = 0, used = 0, count = 0;
    if (DN_FAULT("dn/list")) return -1;
    for (uint64_t k = 0; k < from; ++k) at += 1 + (uint64_t)f->names[at];
    while (at < f->size && 1 + (uint64_t)f->names[at] <= room - used) {
        uint64_t n = 1 + (uint64_t)f->names[at];
        memcpy(page + used, f->names + at, n);
        used += n;
        at += n;
        ++count;
    }
    if (at < f->size && !count) {
        errno = ENAMETOOLONG;
        return -1;
    }
    result[0] = count;
    result[1] = used;
    return 0;
}

/* A sync, made slower in the test build. */
static int synced(const char *point, int fd, int (*sync)(int)) {
    uint64_t ms;
    if (DN_FAULT_INFO("dn/sync-slow", ms)) {
        struct timespec t = {(time_t)(ms / 1000), (long)(ms % 1000) * 1000000};
        while (nanosleep(&t, &t) && errno == EINTR) {}
    }
    return RETRIED(DN_FAULT(point) ? -1 : sync(fd));
}

/* Operation `i` of `j`, without the lock but where a place is given or taken back. */
static int run(struct job *j, uint64_t i) {
    struct op *op = &j->ops[i];
    struct file *f = op->place < PLACES ? &files[op->place] : NULL;
    uint64_t *result = j->results[i];
    char name[NAME], to[NAME];
    int fd = -1;
    switch (op->code) {
    case DN_SESSION_OP_CREATE:
    case DN_SESSION_OP_OPEN:
    case DN_SESSION_OP_OPEN_DIR: {
        struct file listing = {.fd = -1};
        if (op->code == DN_SESSION_OP_OPEN_DIR) {
            fd = RETRIED(DN_FAULT("dn/open-dir") ? -1 : openat(spool, ".", O_RDONLY | O_DIRECTORY | O_CLOEXEC));
            if (fd < 0 || read_names(fd, &listing)) return -1;
            listing.listing = 1;
        } else {
            name_of(op->name, op->number, name);
            int flags = op->code == DN_SESSION_OP_CREATE ? O_RDWR | O_CREAT | O_EXCL : O_RDWR;
            fd = RETRIED(DN_FAULT(op->code == DN_SESSION_OP_CREATE ? "dn/create" : "dn/open")
                             ? -1 : openat(spool, name, flags | O_CLOEXEC | O_NOFOLLOW, 0644));
        }
        if (fd < 0 && !listing.listing) return -1;
        int p = j->place[i];
        pthread_mutex_lock(&lock);
        files[p] = (struct file){.fd = listing.listing ? -1 : fd, .open = 1, .busy = (int)(j - jobs) + 1,
                                 .listing = listing.listing, .names = listing.names, .size = listing.size,
                                 .count = listing.count, .gen = files[p].gen};
        result[0] = (uint64_t)p;
        result[1] = files[p].gen;
        pthread_mutex_unlock(&lock);
        j->place[i] = -1;
        return 0;
    }
    case DN_SESSION_OP_WRITE:
        f->written = 1;
        return write_all(f->fd, j->data + op->at, op->length, op->offset);
    case DN_SESSION_OP_READ: {
        ssize_t n = RETRIED(DN_FAULT("dn/read") ? -1 : pread(f->fd, j->data + op->at, op->length, (off_t)op->offset));
        if (n < 0) return -1;
        result[0] = (uint64_t)n;
        return 0;
    }
    case DN_SESSION_OP_SIZE: {
        struct stat s;
        if (DN_FAULT("dn/size") || fstat(f->fd, &s)) return -1;
        result[0] = (uint64_t)s.st_size;
        return 0;
    }
    case DN_SESSION_OP_DATA_SYNC: return synced("dn/data-sync", f->fd, fdatasync);
    case DN_SESSION_OP_SYNC: return synced("dn/sync", f->fd, fsync);
    case DN_SESSION_OP_TRUNCATE:
        f->written = 1;
        return RETRIED(DN_FAULT("dn/truncate") ? -1 : ftruncate(f->fd, (off_t)op->length));
    case DN_SESSION_OP_SYNC_DIR: return synced("dn/sync-dir", spool, fsync);
    case DN_SESSION_OP_LIST: return list(f, op->offset, j->data + op->at, op->length, result);
    case DN_SESSION_OP_RENAME:
        name_of(op->name, op->number, name);
        name_of(op->to_name, op->to_number, to);
        return RETRIED(DN_FAULT("dn/rename") ? -1 : renameat(spool, name, spool, to));
    case DN_SESSION_OP_REMOVE:
        name_of(op->name, op->number, name);
        return RETRIED(DN_FAULT("dn/remove") ? -1 : unlinkat(spool, name, 0));
    case DN_SESSION_OP_CLOSE: {
        /* Never retried: the descriptor is gone whatever close says. A listing holds none. */
        j->wrote[i] = f->written;
        int r = f->listing ? 0 : close(f->fd);
        free(f->names);
        if (!f->listing && DN_FAULT("dn/close")) r = -1;
        pthread_mutex_lock(&lock);
        *f = (struct file){.fd = -1, .busy = f->busy, .gen = f->gen + 1};
        pthread_mutex_unlock(&lock);
        return r;
    }
    default: return -1;
    }
}

/* The test build's stop from operation `at` on: the worker holds, and once the operations before
 * have ended wakes the loop to stop. */
static void hold(uint64_t at) {
    struct timespec t = {0, 100000};
    while (atomic_load(&ended) + 1 < at) nanosleep(&t, NULL);
    atomic_store(&held, at);
    uint64_t one = 1;
    if (write(wake, &one, sizeof one) != sizeof one) dn_harness_now("eventfd: %s", strerror(errno));
    for (;;) pause();
}

static void *worker(void *unused) {
    (void)unused;
    for (;;) {
        pthread_mutex_lock(&lock);
        while (!queued) pthread_cond_wait(&work, &lock);
        int k = queue[0];
        memmove(queue, queue + 1, (size_t)--queued * sizeof queue[0]);
        pthread_mutex_unlock(&lock);
        struct job *j = &jobs[k];
        memset(j->results, 0, sizeof j->results);
        j->done = j->count;
        j->class = 0;
        for (uint64_t i = 0; i < j->count; ++i) {
            uint64_t stop, number = 0;
            int stopping = DN_FAULT_INFO("dn/stop", stop);
            if (stopping || fiu_fail("dn/fail")) number = atomic_fetch_add(&begun, 1) + 1;
            if (stopping && number >= stop) hold(stop);
            numbered(number);
            int failed = run(j, i);
            if (stopping) atomic_fetch_add(&ended, 1);
            if (failed) {
                j->done = i;
                j->class = class_of(errno);
                /* A file only read has nothing a failed close may lose. */
                if (syncs(j->ops[i].code) && (j->ops[i].code != DN_SESSION_OP_CLOSE || j->wrote[i]))
                    dn_store_mark_failed();
                break;
            }
        }
        pthread_mutex_lock(&lock);
        j->state = DONE;
        pthread_mutex_unlock(&lock);
        uint64_t one = 1;
        if (write(wake, &one, sizeof one) != sizeof one) dn_harness_now("eventfd: %s", strerror(errno));
    }
    return NULL;
}

int dn_jobs_start(int dir) {
    spool = dir;
    if (spool < 0) return -1;
    for (int p = 0; p < PLACES; ++p) files[p].fd = -1;
    wake = eventfd(0, EFD_CLOEXEC | EFD_NONBLOCK);
    if (wake < 0) dn_harness("eventfd: %s", strerror(errno));
#ifdef FIU_ENABLE
    if (DN_FAULT_INFO("dn/fail", failing))
        for (size_t k = 0; k < sizeof POINTS / sizeof *POINTS; ++k)
            if (fiu_enable_external(POINTS[k], 1, (void *)(uintptr_t)(failing % 256), 0, fails_now))
                dn_harness("fiu_enable_external %s", POINTS[k]);
#endif
    /* Workers take no signal: the loop takes SIGTERM and SIGINT through its signalfd, which a worker
       taking one would bypass, ending the process at once. */
    sigset_t all, old;
    sigfillset(&all);
    if (pthread_sigmask(SIG_SETMASK, &all, &old)) dn_harness("pthread_sigmask");
    for (int w = 0; w < WORKERS; ++w) {
        pthread_t thread;
        if (pthread_create(&thread, NULL, worker, NULL) || pthread_detach(thread)) dn_harness("a worker thread");
    }
    if (pthread_sigmask(SIG_SETMASK, &old, NULL)) dn_harness("pthread_sigmask");
    return wake;
}

void dn_jobs_take(const unsigned char *a) {
    pthread_mutex_lock(&lock);
    for (int k = 0; k < JOBS; ++k) {
        const unsigned char *slot = a + DN_SESSION_EMIT_JOBS + (size_t)k * DN_SESSION_JOB_SLOT;
        uint64_t kind = dn_word(slot + DN_SESSION_JOB_KIND);
        if (!kind) continue;
        if (kind != DN_SESSION_JOB) dn_violation("dn_emit: job %d of kind %" PRIu64, k, kind);
        if (spool < 0) dn_violation("dn_emit: a file job without a store");
        take(k, slot);
    }
    pthread_mutex_unlock(&lock);
}

int dn_jobs_ready(void) {
    /* Emptied first: a worker marks its job done before it writes, so a completion after the check
     * below wakes the loop again, and one before it leaves at most one wake for nothing. */
    uint64_t drained, at;
    if (wake >= 0 && read(wake, &drained, sizeof drained) < 0 && errno != EAGAIN)
        dn_harness("eventfd: %s", strerror(errno));
    if (DN_FAULT_INFO("dn/stop", at) && atomic_load(&held) == at) raise(SIGSTOP);
    pthread_mutex_lock(&lock);
    int ready = 0;
    for (int k = 0; k < JOBS; ++k) ready |= jobs[k].state == DONE;
    pthread_mutex_unlock(&lock);
    return ready;
}

void dn_jobs_give(unsigned char *a) {
    uint64_t count = 0;
    pthread_mutex_lock(&lock);
    for (int k = 0; k < JOBS; ++k) {
        unsigned char *slot = a + DN_SESSION_NEXT_DONE + (size_t)k * DN_SESSION_DONE_SLOT;
        struct job *j = &jobs[k];
        if (j->state != DONE) {
            dn_put_word(slot + DN_SESSION_DONE_KIND, 0);
            continue;
        }
        dn_put_word(slot + DN_SESSION_DONE_KIND, DN_SESSION_DONE);
        dn_put_word(slot + DN_SESSION_DONE_GEN, j->gen);
        dn_put_word(slot + DN_SESSION_DONE_OPS, j->done);
        dn_put_word(slot + DN_SESSION_DONE_CLASS, j->class);
        for (int i = 0; i < OPS; ++i) {
            dn_put_word(slot + DN_SESSION_DONE_RESULTS + 16 * (size_t)i, j->results[i][0]);
            dn_put_word(slot + DN_SESSION_DONE_RESULTS + 16 * (size_t)i + 8, j->results[i][1]);
        }
        memcpy(slot + DN_SESSION_DONE_HEAD, j->data, DATA);
        /* Until the program learns of it, the job keeps the files it names, the places it reserved
         * and its sync of the directory. */
        for (uint64_t i = 0; i < j->count; ++i)
            if (j->place[i] >= 0) files[j->place[i]].reserved = 0;
        for (int p = 0; p < PLACES; ++p)
            if (files[p].busy == k + 1) files[p].busy = 0;
        dir_syncs -= j->dir_sync;
        j->state = FREE;
        ++count;
    }
    pthread_mutex_unlock(&lock);
    dn_put_word(a + DN_SESSION_NEXT_DONE_COUNT, count);
}
