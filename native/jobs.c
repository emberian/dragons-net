/* SPDX-License-Identifier: AGPL-3.0-or-later
 * File jobs; see jobs.h. A job is checked when it is taken, inside dn_emit, and copied out of the
 * heap with the bytes it writes; a worker takes it from a queue and runs it without the lock, on
 * files no other job in flight may name; the bytes it reads go back into the heap inside dn_next.
 * Names are made from a kind and a number as DN.News.Journal makes them, relative to the spool. A
 * signal's interruption is retried and never reported; a short write is written on, and one that
 * makes no progress fails as no space; a short read is reported as it is. */
#define _GNU_SOURCE
#include "jobs.h"
#include "dn_session_layout.h"
#include "host.h"
#include <dirent.h>
#include <fcntl.h>
#include <inttypes.h>
#include <pthread.h>
#include <sys/eventfd.h>
#include <sys/stat.h>

enum { JOBS = DN_SESSION_JOBS, OPS = DN_SESSION_JOB_OPS, DATA = DN_SESSION_JOB_DATA, PLACES = DN_SESSION_HANDLES,
       WORKERS = 2, NAME = 32 };
enum { FREE, QUEUED, DONE };

struct op { uint64_t code, place, gen, name, number, to_name, to_number, offset, length, at; };

struct job {
    int state, dir_sync;
    uint64_t gen, count, done, class, results[OPS][2];
    struct op ops[OPS];
    int place[OPS];   /* the place an operation that opens a file takes, reserved when the job is */
    unsigned char data[DATA];
};

struct file {
    int fd, open, busy, reserved;
    DIR *dir;         /* a directory opened to list it */
    uint64_t gen;
};

static struct job jobs[JOBS];
static struct file files[PLACES];
static int spool = -1, wake = -1, queue[JOBS], queued, dir_syncs;
static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t work = PTHREAD_COND_INITIALIZER;

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
            int p = 0;
            while (p < PLACES && (files[p].open || files[p].reserved)) ++p;
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
            if ((op->code == DN_SESSION_OP_LIST) != (f->dir != NULL) && op->code != DN_SESSION_OP_CLOSE)
                dn_violation("dn_emit: job %d, operation %" PRIu64 " on place %" PRIu64 " of the other kind", k, i,
                             op->place);
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
        ssize_t w = RETRIED(pwrite(fd, p, n, (off_t)offset));
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

/* A page of the directory's names, each a length octet and its bytes, without `.` and `..`. */
static int list(DIR *dir, unsigned char *page, uint64_t room, uint64_t result[2]) {
    uint64_t used = 0, count = 0;
    for (;;) {
        long at = telldir(dir);
        errno = 0;
        struct dirent *e = readdir(dir);
        if (!e) {
            if (errno) return -1;
            break;
        }
        if (!strcmp(e->d_name, ".") || !strcmp(e->d_name, "..")) continue;
        size_t len = strlen(e->d_name);
        if (len > 255 || 1 + len > room - used) {
            seekdir(dir, at);
            if (!count) {
                errno = ENAMETOOLONG;
                return -1;
            }
            break;
        }
        page[used] = (unsigned char)len;
        memcpy(page + used + 1, e->d_name, len);
        used += 1 + len;
        ++count;
    }
    result[0] = count;
    result[1] = used;
    return 0;
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
        DIR *dir = NULL;
        if (op->code == DN_SESSION_OP_OPEN_DIR) {
            fd = RETRIED(openat(spool, ".", O_RDONLY | O_DIRECTORY | O_CLOEXEC));
            if (fd >= 0 && !(dir = fdopendir(fd))) {
                int error = errno;
                close(fd);
                errno = error;
                fd = -1;
            }
        } else {
            name_of(op->name, op->number, name);
            int flags = op->code == DN_SESSION_OP_CREATE ? O_RDWR | O_CREAT | O_EXCL : O_RDWR;
            fd = RETRIED(openat(spool, name, flags | O_CLOEXEC | O_NOFOLLOW, 0644));
        }
        if (fd < 0) return -1;
        int p = j->place[i];
        pthread_mutex_lock(&lock);
        files[p] = (struct file){.fd = fd, .open = 1, .busy = (int)(j - jobs) + 1, .dir = dir, .gen = files[p].gen};
        result[0] = (uint64_t)p;
        result[1] = files[p].gen;
        pthread_mutex_unlock(&lock);
        j->place[i] = -1;
        return 0;
    }
    case DN_SESSION_OP_WRITE: return write_all(f->fd, j->data + op->at, op->length, op->offset);
    case DN_SESSION_OP_READ: {
        ssize_t n = RETRIED(pread(f->fd, j->data + op->at, op->length, (off_t)op->offset));
        if (n < 0) return -1;
        result[0] = (uint64_t)n;
        return 0;
    }
    case DN_SESSION_OP_SIZE: {
        struct stat s;
        if (fstat(f->fd, &s)) return -1;
        result[0] = (uint64_t)s.st_size;
        return 0;
    }
    case DN_SESSION_OP_DATA_SYNC: return RETRIED(fdatasync(f->fd));
    case DN_SESSION_OP_SYNC: return RETRIED(fsync(f->fd));
    case DN_SESSION_OP_TRUNCATE: return RETRIED(ftruncate(f->fd, (off_t)op->length));
    case DN_SESSION_OP_SYNC_DIR: return RETRIED(fsync(spool));
    case DN_SESSION_OP_LIST: return list(f->dir, j->data + op->at, op->length, result);
    case DN_SESSION_OP_RENAME:
        name_of(op->name, op->number, name);
        name_of(op->to_name, op->to_number, to);
        return RETRIED(renameat(spool, name, spool, to));
    case DN_SESSION_OP_REMOVE:
        name_of(op->name, op->number, name);
        return RETRIED(unlinkat(spool, name, 0));
    case DN_SESSION_OP_CLOSE: {
        /* Never retried: the descriptor is gone whatever close says. */
        int r = f->dir ? closedir(f->dir) : close(f->fd);
        pthread_mutex_lock(&lock);
        *f = (struct file){.fd = -1, .gen = f->gen + 1};
        pthread_mutex_unlock(&lock);
        return r;
    }
    default: return -1;
    }
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
        for (uint64_t i = 0; i < j->count; ++i)
            if (run(j, i)) {
                j->done = i;
                j->class = class_of(errno);
                break;
            }
        pthread_mutex_lock(&lock);
        j->state = DONE;
        pthread_mutex_unlock(&lock);
        uint64_t one = 1;
        if (write(wake, &one, sizeof one) != sizeof one) dn_harness("eventfd: %s", strerror(errno));
    }
    return NULL;
}

int dn_jobs_start(int dir) {
    spool = dir;
    if (spool < 0) return -1;
    for (int p = 0; p < PLACES; ++p) files[p].fd = -1;
    wake = eventfd(0, EFD_CLOEXEC | EFD_NONBLOCK);
    if (wake < 0) dn_harness("eventfd: %s", strerror(errno));
    for (int w = 0; w < WORKERS; ++w) {
        pthread_t thread;
        if (pthread_create(&thread, NULL, worker, NULL) || pthread_detach(thread)) dn_harness("a worker thread");
    }
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
    uint64_t drained;
    if (wake >= 0 && read(wake, &drained, sizeof drained) < 0 && errno != EAGAIN)
        dn_harness("eventfd: %s", strerror(errno));
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
