/* SPDX-License-Identifier: AGPL-3.0-or-later
 * Runs the NNTP session (DN.Server.Session) as `dn-compiler session-model` runs its model: it reads
 * the same lines from stdin and answers with the same lines, so that one driver can hold the
 * compiled code against the model turn by turn (scripts/session_native.py).
 *
 *   identity REVISION SOURCE        once, first; both in hex
 *   store GROUPS PATH RUN PLACE GEN JOB IMAGE
 *                                   a store, once, next, as the model reads it
 *   turn NOW [WALL], then events and completions, then go
 *                                   a batch; the answer is the actions and the jobs, then `done`
 *   took N ...                      what the kernel took of each send; the answer, `deadline D`,
 *                                   comes when the program asks for its next batch
 *
 * With a store the program first recovers it from the spool the image gives, which has to end
 * where the model's begins, before its start record: the host answers its jobs from that spool in
 * memory, opening the journal at the line's place and generation, and tells the generations of
 * the program's later jobs shifted so that the first is the line's JOB + 1.
 *
 * Besides the events the model knows, a batch can hold `raw KIND IDX GEN`, an event of any kind,
 * and `poke OFFSET VALUE`, a word the host writes into the program's own area, and an identity can
 * be longer than the layout holds, its length written in full: all are there to break the contract
 * in ways only the program is asked to see.
 *
 * A breach ends the run with the code the program leaves in its area, answered `stop CODE`. A
 * `took` with another number of counts than sends cannot be written in the layout, where each
 * count lies in its send's slot; the host answers it itself, as the model does. Completions the
 * layout cannot hold — more than its slots, two of one slot, out of the slots' order, or results
 * for operations not done — are bad input. The end of stdin ends the run inside a call, as a
 * serving host would.
 *
 * Before the run the whole heap past its header is filled, so the program cannot lean on what it
 * did not write; on every call and when the run ends, the heap header, the heap before the first
 * area and the heap past the program's layout have to be as they were, and each array the program
 * hands over has to be its area of the layout; the word to listen has to be 0 or 1, and stay 1. */
#include "session_calls.h"

static const uint64_t FILL = UINT64_C(0x5A5A5A5A5A5A5A5A);
/* More than any spool of the lane holds: a write or truncation past it is the program's fault. */
static const uint64_t FILE_MAX = UINT64_C(1) << 30;

static unsigned char revision[DN_SESSION_REV_MAX], source[DN_SESSION_SRC_MAX];
static size_t revision_len, source_len;
static int started, awaiting_emit, listening;
static long sends;
static char *line;
static size_t line_cap;
static uint64_t wall;

/* The store: its configuration, and while the program recovers it, the spool in memory, the
 * places open in it and the completion of the job in flight. */
static int stored, recovering;
static unsigned char groups[DN_SESSION_GROUPS_MAX][DN_SESSION_GROUP_MAX], path[DN_SESSION_IDENTITY_MAX];
static size_t group_len[DN_SESSION_GROUPS_MAX], groups_n, path_len;
static unsigned char run_value[DN_SESSION_RUN_VALUE_LEN];
static uint64_t journal_place, journal_gen, job_line, shift, last_gen;

struct file {
    char name[24];
    unsigned char *data;
    size_t len;
    int live;
};
static struct file *files;
static size_t files_n, files_cap;

struct place {
    int open, listing;
    size_t file;
    uint64_t gen;
    unsigned char *names;
    size_t names_len;
    uint64_t count;
};
static struct place places[DN_SESSION_HANDLES];

static int pending;
/* Whether the job handed in each slot reads, so that its completion carries the octets read. */
static int reads_in[DN_SESSION_JOBS];
static uint64_t pending_gen, pending_ops, pending_class, pending_results[DN_SESSION_JOB_OPS][2];
static unsigned char pending_data[DN_SESSION_JOB_DATA];

/* The heap outside the program's areas: the header, the bytes before the first area, and all past
 * the layout. */
static void heap_intact(const char *call) {
    dn_header_checked(call);
    for (size_t off = DN_HEADER_BYTES; off < DN_SESSION_ART_OFF; off += 8)
        if (dn_word(dn_heap_at(off)) != FILL)
            dn_violation("%s: the program wrote before its layout, at heap offset %zu", call, off);
    for (size_t off = DN_SESSION_SIZE; off < DN_SESSION_HEAP_BYTES; off += 8)
        if (dn_word(dn_heap_at(off)) != FILL)
            dn_violation("%s: the program wrote past its layout, at heap offset %zu", call, off);
}

static void checked(const unsigned char *c, long clen, const unsigned char *a, long alen, size_t offset, long len,
                    const char *call) {
    heap_intact(call);
    dn_session_call(c, clen, a, alen, offset, len, call);
}

static char *next_line(void) {
    ssize_t n = getline(&line, &line_cap, stdin);
    if (n < 0) {
        if (ferror(stdin)) dn_harness("stdin: %s", strerror(errno));
        return NULL;
    }
    if (n && line[n - 1] == '\n') line[--n] = 0;
    return line;
}

static uint64_t number(const char *text) { return dn_parse_u64(text, UINT64_MAX); }

static int nibble(char h) {
    if (h >= '0' && h <= '9') return h - '0';
    if (h >= 'a' && h <= 'f') return h - 'a' + 10;
    dn_harness("bad input: not hex: %c", h);
}

/* Hex bytes into `out`, at most `room` of them; the count in full, `-` being none. */
static size_t unhex(const char *text, unsigned char *out, size_t room) {
    if (strcmp(text, "-") == 0) return 0;
    size_t digits = strlen(text);
    if (digits % 2) dn_harness("bad input: an odd number of hex digits");
    for (size_t k = 0; k < digits / 2 && k < room; ++k)
        out[k] = (unsigned char)(nibble(text[2 * k]) * 16 + nibble(text[2 * k + 1]));
    return digits / 2;
}

static void print_hex(const unsigned char *bytes, uint64_t count) {
    if (count == 0) putchar('-');
    for (uint64_t k = 0; k < count; ++k) printf("%02x", bytes[k]);
}

static void answer(void) {
    if (fflush(stdout)) dn_harness("stdout: %s", strerror(errno));
}

static const char *const kinds[] = {"open", "recv", "writable", "end", "closed", "verdict"};

static size_t smaller(size_t a, size_t b) { return a < b ? a : b; }

/* A name the store gives a file: the journal's, or a letter and sixteen hexadecimal digits. */
static void name_of(uint64_t kind, uint64_t seq, char name[24]) {
    static const char letters[] = {[DN_SESSION_NAME_FINAL] = 'a', [DN_SESSION_NAME_TEMP] = 't',
                                   [DN_SESSION_NAME_QUARANTINE] = 'q', [DN_SESSION_NAME_TAIL] = 'j'};
    if (kind == DN_SESSION_NAME_JOURNAL) snprintf(name, 24, "journal");
    else if (kind >= DN_SESSION_NAME_FINAL && kind <= DN_SESSION_NAME_TAIL)
        snprintf(name, 24, "%c%016" PRIx64, letters[kind], seq);
    else dn_violation("dn_emit: a job names a file of kind %" PRIu64, kind);
}

/* What the store line says, the program's configuration and the spool it recovers. */
static void store_line(char *text) {
    char *g = strtok(text, " "), *p = strtok(NULL, " "), *r = strtok(NULL, " "), *place = strtok(NULL, " "),
         *gen = strtok(NULL, " "), *job = strtok(NULL, " "), *image = strtok(NULL, " ");
    if (!image || strtok(NULL, " ")) dn_harness("bad input: not a store");
    for (char *name = strcmp(g, "-") ? strtok(g, ",") : NULL; name; name = strtok(NULL, ",")) {
        if (groups_n == DN_SESSION_GROUPS_MAX) dn_harness("bad input: more groups than the layout holds");
        group_len[groups_n] = unhex(name, groups[groups_n], DN_SESSION_GROUP_MAX);
        if (group_len[groups_n] > DN_SESSION_GROUP_MAX) dn_harness("bad input: a group the layout cannot hold");
        ++groups_n;
    }
    path_len = unhex(p, path, sizeof path);
    if (path_len > sizeof path || unhex(r, run_value, sizeof run_value) != sizeof run_value)
        dn_harness("bad input: a path identity or a run's value the layout cannot hold");
    journal_place = number(place);
    journal_gen = number(gen);
    job_line = number(job);
    if (journal_place >= DN_SESSION_HANDLES) dn_harness("bad input: the journal at place %" PRIu64, journal_place);
    for (char *item = strcmp(image, "-") ? strtok(image, ";") : NULL; item; item = strtok(NULL, ";")) {
        char *eq = strchr(item, '=');
        if (!eq) dn_harness("bad input: not an image");
        *eq = 0;
        if (files_n == files_cap) {
            files_cap = files_cap ? 2 * files_cap : 64;
            files = realloc(files, files_cap * sizeof *files);
            if (!files) dn_harness("out of memory");
        }
        struct file *f = &files[files_n++];
        *f = (struct file){.live = 1};
        size_t nl = unhex(item, (unsigned char *)f->name, sizeof f->name - 1);
        if (nl >= sizeof f->name) dn_harness("bad input: a name of %zu octets", nl);
        f->name[nl] = 0;
        f->len = strlen(eq + 1) / 2;
        f->data = malloc(f->len + 1);
        if (!f->data) dn_harness("out of memory");
        unhex(eq + 1, f->data, f->len);
        if (strcmp(eq + 1, "-") == 0) f->len = 0;
    }
    stored = recovering = 1;
}

static struct file *named(const char *name) {
    for (size_t k = 0; k < files_n; ++k)
        if (files[k].live && strcmp(files[k].name, name) == 0) return &files[k];
    return NULL;
}

static struct file *made(const char *name) {
    if (files_n == files_cap) {
        files_cap = files_cap ? 2 * files_cap : 64;
        files = realloc(files, files_cap * sizeof *files);
        if (!files) dn_harness("out of memory");
    }
    struct file *f = &files[files_n++];
    *f = (struct file){.live = 1};
    snprintf(f->name, sizeof f->name, "%s", name);
    return f;
}

/* A place for a file being opened: the journal's own, else the lowest free one. */
static uint64_t free_place(int journal) {
    if (journal) return journal_place;
    for (uint64_t p = 0; p < DN_SESSION_HANDLES; ++p)
        if (p != journal_place && !places[p].open) return p;
    dn_violation("dn_emit: recovery opens a file with every place taken");
}

static struct place *open_place(const unsigned char *o, uint64_t i) {
    uint64_t p = dn_word(o + DN_SESSION_OP_HANDLE), g = dn_word(o + DN_SESSION_OP_HANDLE_GEN);
    if (p >= DN_SESSION_HANDLES || !places[p].open || places[p].gen != g)
        dn_violation("dn_emit: operation %" PRIu64 " of recovery's job names place %" PRIu64 "/%" PRIu64 ", not open",
                     i, p, g);
    return &places[p];
}

/* Recovery's job in the first slot, done on the spool in memory: its completion, for the next
 * batch. */
static void recovery_job(const unsigned char *slot) {
    uint64_t count = dn_word(slot + DN_SESSION_JOB_COUNT);
    if (count < 1 || count > DN_SESSION_JOB_OPS) dn_violation("dn_emit: a job of %" PRIu64 " operations", count);
    pending = 1;
    pending_gen = last_gen = dn_word(slot + DN_SESSION_JOB_GEN);
    pending_class = 0;
    memset(pending_results, 0, sizeof pending_results);
    for (pending_ops = 0; pending_ops < count; ++pending_ops) {
        uint64_t i = pending_ops;
        const unsigned char *o = slot + DN_SESSION_JOB_OPS_AT + i * DN_SESSION_OP_SLOT;
        uint64_t code = dn_word(o + DN_SESSION_OP_CODE), offset = dn_word(o + DN_SESSION_OP_OFFSET),
                 length = dn_word(o + DN_SESSION_OP_LENGTH), at = dn_word(o + DN_SESSION_OP_DATA);
        uint64_t *result = pending_results[i];
        char name[24], to[24];
        if ((code == DN_SESSION_OP_WRITE || code == DN_SESSION_OP_READ || code == DN_SESSION_OP_LIST) &&
            (at > DN_SESSION_JOB_DATA || length > DN_SESSION_JOB_DATA - at))
            dn_violation("dn_emit: %" PRIu64 " bytes at %" PRIu64 " of a job's data", length, at);
        if ((code == DN_SESSION_OP_WRITE && offset > FILE_MAX - length) ||
            (code == DN_SESSION_OP_TRUNCATE && length > FILE_MAX))
            dn_violation("dn_emit: recovery makes a file of more than %llu octets", (unsigned long long)FILE_MAX);
        if (code == DN_SESSION_OP_SYNC_DIR) continue;
        if (code == DN_SESSION_OP_OPEN_DIR) {
            uint64_t p = free_place(0);
            struct place *pl = &places[p];
            *pl = (struct place){.open = 1, .listing = 1, .gen = pl->gen};
            for (size_t k = 0; k < files_n; ++k) {
                if (!files[k].live) continue;
                size_t nl = strlen(files[k].name);
                pl->names = realloc(pl->names, pl->names_len + 1 + nl);
                if (!pl->names) dn_harness("out of memory");
                pl->names[pl->names_len] = (unsigned char)nl;
                memcpy(pl->names + pl->names_len + 1, files[k].name, nl);
                pl->names_len += 1 + nl;
                ++pl->count;
            }
            result[0] = p;
            result[1] = pl->gen;
            continue;
        }
        if (code == DN_SESSION_OP_OPEN || code == DN_SESSION_OP_CREATE) {
            name_of(dn_word(o + DN_SESSION_OP_NAME), dn_word(o + DN_SESSION_OP_NUMBER), name);
            struct file *f = named(name);
            if (code == DN_SESSION_OP_OPEN && !f) { pending_class = DN_SESSION_CLASS_NOT_FOUND; break; }
            if (code == DN_SESSION_OP_CREATE && f) { pending_class = DN_SESSION_CLASS_EXISTS; break; }
            if (!f) f = made(name);
            int journal = strcmp(name, "journal") == 0;
            uint64_t p = free_place(journal);
            if (places[p].open) dn_violation("dn_emit: recovery opens the journal twice");
            places[p] = (struct place){.open = 1, .file = (size_t)(f - files),
                                       .gen = journal ? journal_gen : places[p].gen};
            result[0] = p;
            result[1] = places[p].gen;
            continue;
        }
        if (code == DN_SESSION_OP_RENAME || code == DN_SESSION_OP_REMOVE) {
            name_of(dn_word(o + DN_SESSION_OP_NAME), dn_word(o + DN_SESSION_OP_NUMBER), name);
            struct file *f = named(name);
            if (!f) { pending_class = DN_SESSION_CLASS_NOT_FOUND; break; }
            if (code == DN_SESSION_OP_REMOVE) {
                f->live = 0;
                continue;
            }
            name_of(dn_word(o + DN_SESSION_OP_TO_NAME), dn_word(o + DN_SESSION_OP_TO_NUMBER), to);
            struct file *old = named(to);
            if (old) old->live = 0;
            snprintf(f->name, sizeof f->name, "%s", to);
            continue;
        }
        struct place *pl = open_place(o, i);
        struct file *f = &files[pl->file];
        switch (code) {
        case DN_SESSION_OP_LIST: {
            if (!pl->listing) dn_violation("dn_emit: a listing of a file");
            size_t from = 0, used = 0;
            uint64_t listed = 0;
            for (uint64_t k = 0; k < offset && from < pl->names_len; ++k) from += 1 + pl->names[from];
            while (from < pl->names_len && 1 + (size_t)pl->names[from] <= length - used) {
                size_t nl = 1 + (size_t)pl->names[from];
                memcpy(pending_data + at + used, pl->names + from, nl);
                used += nl;
                from += nl;
                ++listed;
            }
            result[0] = listed;
            result[1] = used;
            break;
        }
        case DN_SESSION_OP_READ: {
            size_t n = offset < f->len ? smaller(length, f->len - offset) : 0;
            memcpy(pending_data + at, f->data + offset, n);
            result[0] = n;
            break;
        }
        case DN_SESSION_OP_SIZE: result[0] = f->len; break;
        case DN_SESSION_OP_WRITE:
        case DN_SESSION_OP_TRUNCATE: {
            size_t end = code == DN_SESSION_OP_WRITE ? offset + length : length;
            if (end > f->len) {
                f->data = realloc(f->data, end + 1);
                if (!f->data) dn_harness("out of memory");
                memset(f->data + f->len, 0, end - f->len);
            }
            if (code == DN_SESSION_OP_WRITE) memcpy(f->data + offset, slot + DN_SESSION_JOB_HEAD + at, length);
            f->len = code == DN_SESSION_OP_WRITE && end < f->len ? f->len : end;
            break;
        }
        case DN_SESSION_OP_SYNC:
        case DN_SESSION_OP_DATA_SYNC: break;
        case DN_SESSION_OP_CLOSE:
            free(pl->names);
            *pl = (struct place){.gen = pl->gen + 1};
            break;
        default: dn_violation("dn_emit: recovery's job holds an operation of code %" PRIu64, code);
        }
    }
}

/* What a recovery's batch carries: the completion of its job, if it has one. */
static void recovery_batch(unsigned char *a) {
    dn_put_word(a + DN_SESSION_NEXT_COUNT, 0);
    for (uint64_t k = 0; k < DN_SESSION_JOBS; ++k)
        dn_put_word(a + DN_SESSION_NEXT_DONE + k * DN_SESSION_DONE_SLOT + DN_SESSION_DONE_KIND, 0);
    if (!pending) return;
    unsigned char *slot = a + DN_SESSION_NEXT_DONE;
    dn_put_word(slot + DN_SESSION_DONE_KIND, DN_SESSION_DONE);
    dn_put_word(slot + DN_SESSION_DONE_GEN, pending_gen);
    dn_put_word(slot + DN_SESSION_DONE_OPS, pending_ops);
    dn_put_word(slot + DN_SESSION_DONE_CLASS, pending_class);
    for (uint64_t i = 0; i < DN_SESSION_JOB_OPS; ++i) {
        dn_put_word(slot + DN_SESSION_DONE_RESULTS + 16 * i, pending_results[i][0]);
        dn_put_word(slot + DN_SESSION_DONE_RESULTS + 16 * i + 8, pending_results[i][1]);
    }
    memcpy(slot + DN_SESSION_DONE_HEAD, pending_data, DN_SESSION_JOB_DATA);
    pending = 0;
}

/* The words every batch carries: the clocks, the identity and, with a store, its configuration. */
static void configuration(unsigned char *a, uint64_t now) {
    dn_put_word(a + DN_SESSION_NEXT_CLOCK, now);
    dn_put_word(a + DN_SESSION_NEXT_WALL, wall);
    dn_put_word(a + DN_SESSION_NEXT_STORE, (uint64_t)stored);
    dn_put_word(a + DN_SESSION_NEXT_REV_LEN, revision_len);
    memcpy(a + DN_SESSION_NEXT_REV, revision, smaller(revision_len, sizeof revision));
    dn_put_word(a + DN_SESSION_NEXT_SRC_LEN, source_len);
    memcpy(a + DN_SESSION_NEXT_SRC, source, smaller(source_len, sizeof source));
    if (!stored) return;
    memcpy(a + DN_SESSION_NEXT_RANDOM, run_value, sizeof run_value);
    /* The journal's key, as the lane's spools have it, then the index's. */
    for (size_t k = sizeof run_value; k < DN_SESSION_RANDOM_LEN; ++k)
        a[DN_SESSION_NEXT_RANDOM + k] = (unsigned char)(k - sizeof run_value);
    dn_put_word(a + DN_SESSION_NEXT_IDENTITY_LEN, path_len);
    memcpy(a + DN_SESSION_NEXT_IDENTITY, path, path_len);
    dn_put_word(a + DN_SESSION_NEXT_GROUP_COUNT, groups_n);
    for (size_t k = 0; k < groups_n; ++k) {
        dn_put_word(a + DN_SESSION_NEXT_GROUPS + k * DN_SESSION_GROUP_SLOT, group_len[k]);
        memcpy(a + DN_SESSION_NEXT_GROUPS + k * DN_SESSION_GROUP_SLOT + 8, groups[k], group_len[k]);
    }
}

/* `complete SLOT GEN OK RESULTS [DATA]` into its slot, which has to come after the last one's; the
octets a read gave into its data. */
static void completion(unsigned char *a, int *last) {
    char *slot = strtok(NULL, " "), *gen = strtok(NULL, " "), *ok = strtok(NULL, " "), *rs = strtok(NULL, " "),
         *data = strtok(NULL, " ");
    if (!rs || (data && strtok(NULL, " "))) dn_harness("bad input: not a completion");
    uint64_t k = number(slot), done = number(ok);
    if (k >= DN_SESSION_JOBS || (int)k <= *last) dn_harness("bad input: a completion the layout cannot hold");
    *last = (int)k;
    unsigned char *d = a + DN_SESSION_NEXT_DONE + k * DN_SESSION_DONE_SLOT;
    dn_put_word(d + DN_SESSION_DONE_KIND, DN_SESSION_DONE);
    dn_put_word(d + DN_SESSION_DONE_GEN, number(gen) + shift);
    dn_put_word(d + DN_SESSION_DONE_OPS, done);
    dn_put_word(d + DN_SESSION_DONE_CLASS, 0);
    uint64_t given = 0;
    for (char *r = strcmp(rs, "-") ? strtok(rs, ",") : NULL; r; r = strtok(NULL, ",")) {
        char *colon = strchr(r, ':');
        if (!colon || given >= DN_SESSION_JOB_OPS) dn_harness("bad input: not results");
        *colon = 0;
        dn_put_word(d + DN_SESSION_DONE_RESULTS + 16 * given, number(r));
        dn_put_word(d + DN_SESSION_DONE_RESULTS + 16 * given + 8, number(colon + 1));
        ++given;
    }
    if (given != done) dn_harness("bad input: results for operations not done");
    /* A read's completion carries its octets, those of no other job any. */
    uint64_t count = done && reads_in[k] ? dn_word(d + DN_SESSION_DONE_RESULTS) : 0;
    if ((data ? unhex(data, d + DN_SESSION_DONE_HEAD, DN_SESSION_JOB_DATA) : 0) != count || (data && !count))
        dn_harness("bad input: octets a read does not count");
}

/* One batch from stdin into the `dn_next` array; the end of stdin ends the run. */
static void batch(unsigned char *a) {
    char *text = next_line();
    if (!text) exit(0);
    char *word = strtok(text, " "), *now = strtok(NULL, " "), *at = strtok(NULL, " ");
    if (!word || strcmp(word, "turn") || !now || (at && strtok(NULL, " "))) dn_harness("bad input: not a turn");
    if (at) wall = number(at);
    configuration(a, number(now));
    for (uint64_t k = 0; k < DN_SESSION_JOBS; ++k)
        dn_put_word(a + DN_SESSION_NEXT_DONE + k * DN_SESSION_DONE_SLOT + DN_SESSION_DONE_KIND, 0);
    uint64_t count = 0;
    int last = -1;
    while ((text = next_line()) && strcmp(text, "go")) {
        if (strncmp(text, "poke ", 5) == 0) {
            char *off = strtok(text + 5, " "), *value = strtok(NULL, " ");
            if (!off || !value || strtok(NULL, " ")) dn_harness("bad input: not a poke");
            uint64_t place = number(off);
            if (place < DN_SESSION_OWN_OFF || place >= DN_SESSION_SIZE || place % 8)
                dn_harness("bad input: a poke outside the program's own area");
            dn_put_word(dn_heap_at(place), number(value));
            continue;
        }
        char *kind = strtok(text, " ");
        if (kind && strcmp(kind, "complete") == 0) {
            completion(a, &last);
            continue;
        }
        char *raw = kind && strcmp(kind, "raw") == 0 ? strtok(NULL, " ") : NULL;
        char *idx = strtok(NULL, " "), *gen = strtok(NULL, " "), *data = strtok(NULL, " ");
        if (!kind || !idx || !gen || (strcmp(kind, "raw") == 0 && !raw))
            dn_harness("bad input: an event without its connection");
        uint64_t code = raw ? number(raw) : 0;
        for (uint64_t k = 0; !raw && k < sizeof kinds / sizeof *kinds; ++k)
            if (strcmp(kind, kinds[k]) == 0) code = k + 1;
        /* An open's flags add 1 when it may post, 2 when it may log in, 4 over TLS; a verdict's are 1
         * when it takes the name and password. */
        int flagged = (code == DN_SESSION_OPENED || code == DN_SESSION_VERIFIED) && data;
        uint64_t flags = flagged ? number(data) : 0;
        if (raw ? data != NULL
                : (!code || (code == DN_SESSION_RECEIVED) != (data != NULL && !flagged) ||
                   (code == DN_SESSION_VERIFIED && !data) || flags > (code == DN_SESSION_OPENED ? 7u : 1u) ||
                   (data && strtok(NULL, " "))))
            dn_harness("bad input: no event %s", kind);
        if (count < DN_SESSION_BATCH) {
            unsigned char *slot = a + DN_SESSION_NEXT_EVENTS + count * DN_SESSION_EVENT_SLOT;
            dn_put_word(slot + DN_SESSION_EVENT_KIND, code);
            dn_put_word(slot + DN_SESSION_EVENT_IDX, number(idx));
            dn_put_word(slot + DN_SESSION_EVENT_GEN, number(gen));
            dn_put_word(slot + DN_SESSION_EVENT_POST, flags & 1);
            dn_put_word(slot + DN_SESSION_EVENT_LOGINS, flags >> 1 & 1);
            dn_put_word(slot + DN_SESSION_EVENT_TLS, flags >> 2 & 1);
            dn_put_word(slot + DN_SESSION_EVENT_LEN,
                        data && !flagged ? unhex(data, slot + DN_SESSION_EVENT_HEAD, DN_SESSION_DATA) : 0);
        }
        ++count;
    }
    if (!text) dn_harness("bad input: the input ended inside a turn");
    dn_put_word(a + DN_SESSION_NEXT_COUNT, count);
}

void ffidn_next(unsigned char *c, long clen, unsigned char *a, long alen) {
    checked(c, clen, a, alen, DN_SESSION_NEXT_OFF, DN_SESSION_NEXT_LEN, "dn_next");
    if (awaiting_emit) dn_violation("dn_next: the program fetched again without handing over its answers");
    awaiting_emit = 1;
    if (recovering) {
        configuration(a, 0);
        recovery_batch(a);
        return;
    }
    if (started) {
        printf("deadline %" PRIu64 "\n", dn_word(a + DN_SESSION_NEXT_WAKE));
        answer();
    }
    started = 1;
    batch(a);
}

/* An operation of a job the store makes, as the model writes it. */
static void print_op(const unsigned char *slot, uint64_t i) {
    const unsigned char *o = slot + DN_SESSION_JOB_OPS_AT + i * DN_SESSION_OP_SLOT;
    uint64_t code = dn_word(o + DN_SESSION_OP_CODE), p = dn_word(o + DN_SESSION_OP_HANDLE),
             g = dn_word(o + DN_SESSION_OP_HANDLE_GEN);
    char name[24], to[24];
    switch (code) {
    case DN_SESSION_OP_CREATE:
    case DN_SESSION_OP_REMOVE:
    case DN_SESSION_OP_OPEN:
        name_of(dn_word(o + DN_SESSION_OP_NAME), dn_word(o + DN_SESSION_OP_NUMBER), name);
        printf(" %s:%s", code == DN_SESSION_OP_CREATE ? "create" : code == DN_SESSION_OP_OPEN ? "open" : "remove", name);
        break;
    case DN_SESSION_OP_READ: {
        uint64_t len = dn_word(o + DN_SESSION_OP_LENGTH);
        if (dn_word(o + DN_SESSION_OP_DATA) || len > DN_SESSION_JOB_DATA)
            dn_violation("dn_emit: a read of %" PRIu64 " bytes at %" PRIu64 " of a job's data", len,
                         dn_word(o + DN_SESSION_OP_DATA));
        printf(" read:%" PRIu64 ":%" PRIu64 ":%" PRIu64 ":%" PRIu64, p, g, dn_word(o + DN_SESSION_OP_OFFSET), len);
        break;
    }
    case DN_SESSION_OP_WRITE: {
        uint64_t at = dn_word(o + DN_SESSION_OP_DATA), len = dn_word(o + DN_SESSION_OP_LENGTH);
        if (at > DN_SESSION_JOB_DATA || len > DN_SESSION_JOB_DATA - at)
            dn_violation("dn_emit: a write of %" PRIu64 " bytes at %" PRIu64 " of a job's data", len, at);
        printf(" write:%" PRIu64 ":%" PRIu64 ":%" PRIu64 ":", p, g, dn_word(o + DN_SESSION_OP_OFFSET));
        if (len) print_hex(slot + DN_SESSION_JOB_HEAD + at, len);
        break;
    }
    case DN_SESSION_OP_DATA_SYNC: printf(" datasync:%" PRIu64 ":%" PRIu64, p, g); break;
    case DN_SESSION_OP_CLOSE: printf(" close:%" PRIu64 ":%" PRIu64, p, g); break;
    case DN_SESSION_OP_RENAME:
        name_of(dn_word(o + DN_SESSION_OP_NAME), dn_word(o + DN_SESSION_OP_NUMBER), name);
        name_of(dn_word(o + DN_SESSION_OP_TO_NAME), dn_word(o + DN_SESSION_OP_TO_NUMBER), to);
        printf(" rename:%s:%s", name, to);
        break;
    case DN_SESSION_OP_SYNC_DIR: printf(" syncdir"); break;
    default: dn_violation("dn_emit: a job of the store holds an operation of code %" PRIu64, code);
    }
}

void ffidn_emit(unsigned char *c, long clen, unsigned char *a, long alen) {
    checked(c, clen, a, alen, DN_SESSION_EMIT_OFF, DN_SESSION_EMIT_LEN, "dn_emit");
    if (!awaiting_emit) dn_violation("dn_emit: the program answered without fetching");
    awaiting_emit = 0;
    uint64_t listen_word = dn_word(a + DN_SESSION_EMIT_LISTEN);
    if (listen_word > 1 || (listening && !listen_word))
        dn_violation("dn_emit: listening %" PRIu64 ", having listened %d", listen_word, listening);
    listening = (int)listen_word;
    if (recovering) {
        if (dn_word(a + DN_SESSION_EMIT_COUNT)) dn_violation("dn_emit: actions before the store is recovered");
        for (uint64_t k = 1; k < DN_SESSION_JOBS; ++k)
            if (dn_word(a + DN_SESSION_EMIT_JOBS + k * DN_SESSION_JOB_SLOT + DN_SESSION_JOB_KIND))
                dn_violation("dn_emit: recovery hands a job in slot %" PRIu64, k);
        const unsigned char *slot = a + DN_SESSION_EMIT_JOBS;
        uint64_t kind = dn_word(slot + DN_SESSION_JOB_KIND);
        if (kind == DN_SESSION_JOB) recovery_job(slot);
        else if (kind) dn_violation("dn_emit: a job of kind %" PRIu64, kind);
        if (listening) {
            if (kind) dn_violation("dn_emit: a job handed as the host is told to listen");
            recovering = 0;
            shift = last_gen - job_line;
        }
        return;
    }
    uint64_t count = dn_word(a + DN_SESSION_EMIT_COUNT), actions = 0;
    sends = 0;
    for (uint64_t k = 0; k < DN_SESSION_CONNS; ++k) {
        unsigned char *slot = a + DN_SESSION_EMIT_ACTIONS + k * DN_SESSION_ACTION_SLOT;
        uint64_t kind = dn_word(slot + DN_SESSION_ACTION_KIND), idx = dn_word(slot + DN_SESSION_ACTION_IDX),
                 gen = dn_word(slot + DN_SESSION_ACTION_GEN), len = dn_word(slot + DN_SESSION_ACTION_LEN);
        if (kind == 0) continue;
        ++actions;
        if (idx != k) dn_violation("dn_emit: the slot of connection %" PRIu64 " holds an action for %" PRIu64, k, idx);
        if (kind == DN_SESSION_SEND) {
            uint64_t read = dn_word(slot + DN_SESSION_ACTION_READ);
            if (len > DN_SESSION_DATA) dn_violation("dn_emit: a send of %" PRIu64 " bytes", len);
            if (read > 1) dn_violation("dn_emit: a send whose word to read is %" PRIu64, read);
            printf("send %" PRIu64 " %" PRIu64 " ", idx, gen);
            print_hex(slot + DN_SESSION_ACTION_HEAD, len);
            printf(" %" PRIu64 "\n", read);
            ++sends;
        } else if (kind == DN_SESSION_CLOSE_GRACEFULLY) {
            printf("graceful %" PRIu64 " %" PRIu64 "\n", idx, gen);
        } else if (kind == DN_SESSION_CLOSE_NOW) {
            printf("close %" PRIu64 " %" PRIu64 "\n", idx, gen);
        } else if (kind == DN_SESSION_VERIFY) {
            uint64_t name = dn_word(slot + DN_SESSION_ACTION_READ);
            if (name > DN_SESSION_NAME_MAX || len < name || len - name > DN_SESSION_PASSWORD_MAX)
                dn_violation("dn_emit: a check of %" PRIu64 " octets, %" PRIu64 " of them the name", len, name);
            printf("verify %" PRIu64 " %" PRIu64 " ", idx, gen);
            print_hex(slot + DN_SESSION_ACTION_HEAD, name);
            putchar(' ');
            print_hex(slot + DN_SESSION_ACTION_HEAD + name, len - name);
            putchar('\n');
        } else {
            dn_violation("dn_emit: an action of kind %" PRIu64, kind);
        }
    }
    if (actions != count)
        dn_violation("dn_emit: %" PRIu64 " actions counted, %" PRIu64 " in the slots", count, actions);
    for (uint64_t k = 0; k < DN_SESSION_JOBS; ++k) {
        const unsigned char *slot = a + DN_SESSION_EMIT_JOBS + k * DN_SESSION_JOB_SLOT;
        uint64_t kind = dn_word(slot + DN_SESSION_JOB_KIND), ops = dn_word(slot + DN_SESSION_JOB_COUNT);
        if (kind == 0) continue;
        if (kind != DN_SESSION_JOB || !stored) dn_violation("dn_emit: a job of kind %" PRIu64, kind);
        if (ops < 1 || ops > DN_SESSION_JOB_OPS) dn_violation("dn_emit: a job of %" PRIu64 " operations", ops);
        reads_in[k] = dn_word(slot + DN_SESSION_JOB_OPS_AT + DN_SESSION_OP_CODE) == DN_SESSION_OP_READ;
        printf("job %" PRIu64 " %" PRIu64, k, dn_word(slot + DN_SESSION_JOB_GEN) - shift);
        for (uint64_t i = 0; i < ops; ++i) print_op(slot, i);
        printf("\n");
    }
    printf("done\n");
    answer();
    char *text = next_line();
    char *word = text ? strtok(text, " ") : NULL;
    if (!word || strcmp(word, "took")) dn_harness("bad input: no took after the actions");
    long found = 0;
    for (uint64_t k = 0; k < DN_SESSION_CONNS; ++k) {
        unsigned char *slot = a + DN_SESSION_EMIT_ACTIONS + k * DN_SESSION_ACTION_SLOT;
        if (dn_word(slot + DN_SESSION_ACTION_KIND) != DN_SESSION_SEND) continue;
        char *taken = strtok(NULL, " ");
        if (!taken) break;
        dn_put_word(slot + DN_SESSION_ACTION_TAKEN, number(taken));
        ++found;
    }
    if (found != sends || strtok(NULL, " ")) {
        printf("stop %d\n", DN_SESSION_OVER_TAKEN);
        answer();
        exit(0);
    }
}

__attribute__((noreturn)) static void on_exit_run(int code) {
    if (code != 0) dn_violation("the run ended for want of stack or heap (code %d)", code);
    heap_intact("the end of the run");
    uint64_t stop = dn_word(dn_heap_at(DN_SESSION_OWN_OFF + DN_SESSION_OWN_STOP));
    if (stop == 0) dn_violation("the program ended its run without a cause");
    printf("stop %" PRIu64 "\n", stop);
    answer();
    exit(0);
}

int main(void) {
    char *text = next_line();
    if (!text) dn_harness("bad input: no identity first");
    char *word = strtok(text, " "), *rev = strtok(NULL, " "), *src = strtok(NULL, " ");
    if (!word || strcmp(word, "identity") || !rev || !src || strtok(NULL, " "))
        dn_harness("bad input: no identity first");
    revision_len = unhex(rev, revision, sizeof revision);
    source_len = unhex(src, source, sizeof source);
    int first = getc(stdin);
    if (first == 's') {
        ungetc(first, stdin);
        text = next_line();
        if (!text || strncmp(text, "store ", 6)) dn_harness("bad input: not a store");
        store_line(text + 6);
    } else if (first != EOF) {
        ungetc(first, stdin);
    }
    dn_expect_faults();
    dn_runtime_setup_heap(DN_SESSION_HEAP_BYTES);
    dn_runtime_header();
    for (size_t off = DN_HEADER_BYTES; off < DN_SESSION_HEAP_BYTES; off += 8) dn_put_word(dn_heap_at(off), FILL);
    dn_runtime_on_exit = on_exit_run;
    cml_main();
    dn_violation("the program returned to its host, which a build without --main_return cannot do");
}
