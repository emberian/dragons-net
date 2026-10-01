# 0005. The article store: durable acceptance, file operations through the host, and what is proved

Status: accepted, 2026-09-29.

## Question

[#17](https://github.com/emberian/dragons-net/issues/17) asks for a bounded local spool with one
ingestion path for posting, feeds and import: articles accepted durably, deduplicated by
Message-ID, indexed by group with crossposts, with an exact point before which no acceptance is
reported, recovery after a crash with bounded work, and rejected or partial articles never
visible. The session of [0003](0003-nntp-slice.md) answers from an empty store. Before any of the
store is written this has to fix: where its logic runs; how the host reaches the disk without
stalling every connection; the files on disk, the durability point, what an operation's failure
means, and the recovery; how an article's bytes flow and what the heap holds; which articles are
accepted and what the server adds to them; what the slice answers from the store; and what is a
theorem and what is a test.

## What the standards fix

- A proto-article may omit Message-ID, Date and Path, must not carry Injection-Info or Xref, and
  is otherwise a valid article ([RFC 5537](../../rfcs/rfc5537.txt) §3.4.1); an article has From,
  Newsgroups, Subject, Message-ID, Date and Path, each at most once
  ([RFC 5536](../../rfcs/rfc5536.txt) §3, §3.1). Header fields are US-ASCII (§2.2); a msg-id is at
  most 250 octets, and comparing octets is enough to compare two (§3.1.3). Newsgroup names
  reserved by §3.1.4 must not be used for ordinary groups.
- An injecting agent should accept only from a trusted source; must reject a proto-article without
  its mandatory fields, with Injection-Info or Xref, with `POSTED` in Path, or not valid by RFC
  5536, and should reject fields deprecated for Netnews; should reject an Injection-Date or Date
  more than 24 hours ahead or too far past, the cutoff no shorter than 72 hours; should reject one
  with no valid group, crossposts to unknown groups being allowed; must add Message-ID and Date
  when absent; must not alter the body or an existing Message-ID or Injection-Date; must add a
  Path tail entry and update Path; should add an Injection-Info that identifies the source; adds
  Injection-Date unless both Message-ID and Date were present; and must have a list, possibly
  empty, of moderated groups (RFC 5537 §3.5). A serving agent rejects an article it has already
  accepted and may add Xref (§3.3, §3.7).
- Article numbers are issued in order of arrival, a later article always getting a higher number
  ([RFC 3977](../../rfcs/rfc3977.txt) §6). POST answers 340 to send the article, 440 if posting is
  not permitted, and after the article 240 or 441 (§6.3.1); an internal fault that keeps the
  server from carrying out a command is 403 (§3.2.1). The greeting is 200 when the client may post
  and 201 otherwise (§5.1). A command is either not implemented (500) or implemented fully, and a
  form that needs a command the server lacks answers with that case's code, as ARTICLE answers
  412 without GROUP; without the READER label a server may implement some of its commands, though
  it is discouraged from implementing part of a bundle (§3.4). By message-id with no group
  selected, ARTICLE answers with the number 0 (§6.2.1.2).

## What others do

The ACL2 server `fn` keeps an immutable body, an append-only journal whose records carry a checksum,
and an index derived from the journal; it commits in four phases — reserve, durable object, durable
commit record, publish — acknowledges only after the commit record is durable, never reuses an
identifier it has handed out, and tells a known failure from an indeterminate one: an unacknowledged
commit may survive a crash, an acknowledged one may not vanish. Kafka frames its log with a length
and a CRC-32C, etcd its write-ahead log likewise, SQLite checksums its own; INN's tradspool writes
article files without syncing them. A file is made durable by writing it, syncing it, renaming it
into place and syncing the directory; no Linux file system makes the directory sync unnecessary by
contract. After a failed `fsync` the state of the page cache is unknown, and a retry can report
success for lost data (PostgreSQL, 2018). Event-loop servers keep blocking file calls off the loop
with a few threads that report back through a descriptor the loop polls (nginx, Redis); `io_uring`
runs `fsync`, and buffered writes on ext4, on kernel worker threads all the same, and Docker's
default seccomp profile refuses it. The closest verified system is Mailboat (Perennial, SOSP 2019),
a mail server that spools a message and links it into place, proved crash-safe against a file system
whose writes are durable at once; none has been verified against one that defers durability. INN
accepts UTF-8 in header fields, beyond RFC 5536, and sets no limit on crossposts.

## Decision

### Where the logic runs

In the program, as the session does. The program decides what is accepted, writes the article and
its journal records, allocates article numbers, answers from its index and recovers from the
journal. The host carries out file operations it is told to, on one directory, and reports what
happened; it knows nothing of articles.

### File operations through the host

- A new kind of action, a file job: up to eight primitive operations, carried out in order by one
  of the host's worker threads and stopped at the first that fails. Its completion comes back in a
  later batch as an event naming the job, how many operations succeeded and, for one that failed,
  its class: an I/O error, no space, a name that exists or does not, or any other error. The
  program orders what must be ordered by the operations inside a job and by starting a job only
  after the one it depends on completed.
- The operations: create a file under a new name, failing if the name exists; open a named file;
  write bytes at an offset, a short write being a failure; read bytes at an offset; report a
  file's size; sync a file's data (`fdatasync`) or all of it (`fsync`); rename a file; remove a
  name; truncate; sync the directory; list the directory's names, a page at a time, without `.`
  and `..`; close. Names have one fixed shape the host checks, and everything is relative to the
  directory the host opened at start (`openat`, `renameat`, `unlinkat`).
- Jobs are identified by a slot and a generation, like connections, and at most eight are in
  flight. The bytes to write are copied out of the heap inside `dn_emit`, and what is read is
  copied in inside `dn_next`, so the host still touches the heap only inside a call; a job moves at
  most 16,384 octets.
- The workers are a few threads with a queue, and a completed job wakes the loop through an
  `eventfd` in the same `poll`. They are the host's own code: a pool is the norm for this, a library
  for it would outweigh the host, and `io_uring` would gain nothing here.
- At start the host takes an exclusive lock on the spool directory and refuses a spool another
  process holds.

### On disk

- The spool directory holds the journal and one file per article; it is not the root of a file
  system, whose `lost+found` would be a name of another shape. An article is named by a sequence
  number of the store, one more than the highest that a journal record or a name in the directory —
  `a`, `t`, `q` or `j` — showed at start (none: 0) and than any handed out since, so a number is
  never handed out while a file may hold it. A file is first written under a temporary name derived
  from its number and then renamed to its final one, which by that rule no file holds. The final
  name is `a` and the number in sixteen lowercase hexadecimal digits, the temporary name `t` and the
  same digits, and the journal is `journal`.
- The file holds the article as a reader receives it, without Xref: lines ending in CRLF,
  dot-stuffed, without the final dot line, the header fields the server added in place.
- An article is accepted in four phases:
  1. reserve: the program checks the header section, reserves the Message-ID in the index and a
     sequence number, and counts the article against the bounds;
  2. body: it creates the temporary file, writes the article, syncs it, renames it to its final
     name and syncs the directory;
  3. commit: it appends one journal record — the sequence number, the Message-ID, each group by
     name with the number it allocates to the article there, the size of the header section and of
     the file, and the file's CRC-32C — and syncs the journal;
  4. publish: it adds the article to the index and answers 240.

  Numbers are allocated when the record is appended, and records are appended one at a time, so
  articles are numbered in the order they are committed, and a crosspost is one record. ARTICLE
  and HEAD insert the Xref field, built from the record, after the stored header fields.
- A failure is known only while the commit record has not been written: the article is refused
  with 441, and the temporary or final file is removed. Once the record has been written, a failed
  write or sync of the journal leaves the outcome unknown: the connection is closed without an
  answer (RFC 3977 §6.3.1 asks the client to check before posting again), and the next start
  decides from what the journal holds. A failed sync of any kind is never retried, and it stops the
  store accepting articles for the rest of the run (POST then answers 403); what it has, it keeps
  serving.
- A journal record is framed as Kafka's record batches are, with a length, a type and a check over
  the type and the payload, and an end mark: the payload's length, four octets, least significant
  first as every number here; the tag, eight octets; the type, one octet; the payload; and the end
  mark, the octet 0xA5. The tag is SipHash-2-4 (Aumasson and Bernstein, 2012) under the journal's
  key, sixteen random octets the host gives when the journal is created, of the frame's offset in
  the journal, eight octets, the type and the payload: a keyed MAC, not a CRC, since part of a
  commit is an article's author's to choose, and a CRC is linear enough to aim at. The journal
  begins with the record naming its format, type 1: `dragons-net journal`, the version in one octet,
  1, and the key, so that its tag is made under the key it carries. A commit is type 2: the sequence
  number, eight octets, from 1; the Message-ID, a length octet and 1 to 250 octets; a count octet
  and 1 to 16 groups, no two alike, each a name in a length octet and 1 to 64 octets and the article
  number, four octets, 1 to 2,147,483,647 (RFC 3977 §6); then the size of the header section, no
  more than the file's, the size of the file and the file's CRC-32C (RFC 7143 §13.1), four octets
  each. Each start of the store, once recovery is done, appends a start record, type 3 with no
  payload, and syncs it before it takes an article. The largest record is 1,390 octets, the format's
  50 and a start's 14, less than any other's: appended where a torn tail was truncated, a start
  cannot leave whole a frame cut away there, and every other append lands where no frame has been.
  Recovery reads the journal from the start and stops at the first frame that does not check: one
  short of its header or of its length, with a length past the largest payload's, without its end
  mark, or whose tag is not the one its key makes — before the format, a frame that does not carry a
  key the way the format does cannot be checked at all. If what follows fits the one append that can
  have been cut — the format's while no record has been read, one of the largest size after — and no
  frame that checks starts in it after its first octet, as none does after the last thing written,
  it is a torn tail, which is truncated away and the truncation synced; otherwise the store is
  corrupt. A crash may leave any octets of an append it cut short, up to its length: a prefix,
  zeros, junk, parts of it out of order (Zheng et al., FAST 2013, found failures under power loss,
  shorn and unserializable writes among them, on thirteen of fifteen SSDs). Filled with zeros or
  with octets not ending in the end mark, it loses its end mark whatever the article it commits;
  that no crash leaves a frame whose tag checks where it was not written is assumed — it takes the
  key, which neither a crash's junk nor an article's author has. A frame that checks but is no
  record a correct store writes — a format of another version among them — is corruption wherever it
  is, and so is a second format. At most one append is in flight, and the next starts only after its
  sync completed. The journal is bounded by the number of articles the store holds, and the
  directory by those, the files set aside below and two names for each POST in flight, so recovery
  is bounded work without a checkpoint.
  Expiry, when it comes, brings compaction and checkpoints, and has to keep the Message-IDs of what
  it removes, or a cutoff by date, since an article accepted once is rejected ever after.
- After reading the journal, recovery lists the directory. A temporary name is removed. A final name
  without a record is removed too when the journal ended cleanly: an article answered 240 has its
  record synced, and when no tail was cut every synced record reads back. When recovery truncated a
  torn tail after a record, the last record may have been one answered 240 and damaged since, which
  no reading can tell from an append cut short, so a final name without a record is set aside under
  the quarantine name `q` and the same digits, never read and never removed, and the truncated
  octets are kept, after their offset in eight octets, in a file named `j` and a sequence number of
  its own. Then the directory is synced. Each start reports what is set aside; taking it back, or
  removing it, is repair (#21). A name of any other shape makes the store corrupt.
- A store that is corrupt is refused, and the server does not start and says why: a frame that does
  not check where what follows is no torn append's; a sequence number in two records; an article
  number in a group not above the one an earlier record gave it there (RFC 3977 §6); a record naming
  a file that is missing or of another size; a group the configuration lacks; files in the directory
  and no journal. A journal is created only in an empty directory, and created again the same way
  when nothing is left of it but a format cut short and no other name is there. The store is never
  repaired silently; repair, when it comes, is a separate operation (#21).
- A file is checked as it is read: the program re-checks its lines — CRLF only, dot-stuffed — and
  its CRC-32C at the end. One that fails before anything was sent is answered 403; found while
  sending, it closes the connection without the final dot.
- Recovery runs before the first connection is taken: the host listens only once the program
  reports the store ready.

### How an article's bytes flow

- At most four connections are in a POST at once; another POST waits, unanswered and not read,
  until one ends. Each POST holds a header buffer of 65,536 octets and a write buffer of 16,384.
- The article is framed as it arrives by a block framer that streams: it checks each line —
  CRLF only, no NUL or bare CR or LF — and finds the end of the block, keeping only its state, not
  the block. The header section is gathered in the header buffer and checked when it ends; the file
  is then created, and the checked header section with the added fields written. The body is
  gathered in the write buffer and written a buffer at a time, and the connection is not read again
  until that write completes. A line the block may not hold, or an article past its size, refuses
  the article; the rest of the block is read and discarded, and the file is removed.
- ARTICLE, HEAD and BODY read a file 16,384 octets at a time into a buffer of the connection's,
  at most eight such reads in flight, and send it a slot at a time before reading more.
- An article must arrive within 1,800 seconds of its 340, a deadline bytes do not renew; waiting
  for a POST slot or for the store is not inactivity. A connection that ends before the terminator
  abandons its article once its job in flight completes: the file is removed and the reservation
  released. One that ends after the terminator does not stop the commit.
- The heap holds the index, the group table, the POST and read buffers and the session's layout:
  4 MiB in all, which the host provisions.

### Bounds

Set at build time, each with its reason: 4,096 articles in the store, files set aside, `q` and `j`,
counting against it; 64 groups, names at most 64 octets (ours); 16 groups in an article's Newsgroups
field (ours: INN sets no limit); 1,000,000 octets per article in the form it arrives in, with its
terminator, as INN counts `maxartsize`, whose default it is; 65,536 octets for the header section
and 998 for a header line (ours, the line limit of RFC 5322). A full store refuses new articles
(441); it never drops old ones to make room.

### Configuration

The host is given the spool directory, the groups, the server's path identity and the networks
allowed to post (by default loopback, until authentication, RFC 4643, is added), and hands the
groups and the path identity to the program, which checks them: group names as RFC 5536 §3.1.4
allows, none of them reserved, and the path identity as a domain name. Each opened connection
carries whether it may post. The host also hands the program its wall clock, in UTC and not checked
to move forward, and random octets: the run's value, which Message-IDs carry, and sixteen more that
key a journal the program creates, written only to that journal and used for nothing else; and it
logs each connection's address with the run and its index.

### Which articles are accepted, and what the server adds

- Refused: a missing From, Newsgroups or Subject; a field that may appear once present twice
  (RFC 5536 §3, §3.1 and §3.2, RFC 5322 §3.6, RFC 8315 §2), and, by policy as INN, a second
  MIME-Version, Content-Type or Content-Transfer-Encoding, since RFC 2045 describes an entity by
  one of each; any header field not valid by RFC 5536, in particular not US-ASCII, as RFC 5536
  §2.2 and RFC 5537 §3.5 require (INN accepts UTF-8), with a line of a field body of white space
  alone, a message identifier longer than 250 octets in any field that holds one, a From of
  several mailboxes without a Sender, the distribution "All", or a date, a Received's included,
  that is no date;
  Injection-Info, Xref, or `POSTED` in Path; the trace fields of injecting agents older than RFC
  5536 (NNTP-Posting-Host, NNTP-Posting-Date, X-Trace, X-Complaints-To), as RFC 5537 §3.5 allows
  and INN does; a Message-ID, compared by octets, that the store has or has reserved; no known
  group among Newsgroups, or a reserved one, names compared as written as the server compares
  them with its own; a Date or Injection-Date more than 24 hours ahead or
  more than 72 hours past, compared in UTC; a Control or Supersedes field, since this slice
  carries no control messages and Supersedes is a cancel; an Approved field, by policy, so that
  no approval passes before moderation exists; the fields RFC 5536 §3.3 makes obsolete and RFC
  3798 deprecates for Netnews; anything past the bounds. The order RFC 5322 §3.6 gives blocks of
  trace and resent fields is mail transport's and is not checked.
- Added, in RFC 5537 §3.5's order, Path first and the proto-article's fields after it as they
  were: Message-ID, `<seq.random@path-identity>`, and Date from the
  wall clock, when absent; the Path tail entry and the `POSTED` entry for the path identity;
  Injection-Info with the path identity and a `logging-data` parameter naming the run and the
  connection; Injection-Date, unless the proto-article has one or had both Message-ID and Date. A
  present Injection-Date is kept. The body is not changed.
- An article to known and unknown groups is stored in the known ones.
- The four phases, the journal and the index take an article with the role it arrives in; POST
  checks it as an injecting agent, and feeds and import, in later issues, as their roles require.

### What the slice answers from the store

- POST, and the capability `POST`, while the store accepts, has at least one group and the client
  may post; the greeting is then 200, and 201 otherwise. Once the store stops accepting, new
  connections are greeted with 201 and are not offered POST; those greeted before get 403.
- HEAD and STAT by message-id answer from the store (221, 223). ARTICLE and BODY are implemented
  in full: by message-id from the store, with the number 0, and 412 to a number or to no argument,
  since GROUP is not implemented. READER is not advertised until the reader commands are (#18).
  HELP lists ARTICLE, BODY and POST.
- A server started without a spool answers as 0003 fixes.

### What is proved and what is tested

- Proved in Lean, of specifications:
  - which articles are accepted and what is added, each rule shown to matter by a version with it
    broken, as `DN.News.CommandSpec` does for command lines;
  - the streaming block framer gives the specification's verdict however the article is cut;
  - a journal of records reads back as those records; an append cut short — a prefix of its frame,
    that prefix and zeros, or its length and octets not ending in the end mark, to its length —
    reads as a torn tail, whatever the tag, when no frame that checks starts in it; a frame that
    does not check with a record after it is corruption; and a start's frame is shorter than any
    other record's;
  - under a model of crashes in the vocabulary of Pillai and Bornholt — anything not yet synced may
    or may not survive, independently for each file and name; a synced file's data and a name whose
    directory was synced survive; an unsynced append may leave any octets up to its length, which
    are assumed never to make a frame whose tag checks where it was not written — recovery after a
    crash at any point of any run yields every article answered 240, possibly some whose commit
    record was written but not answered, and never one refused before its record was written or a
    partial one; recovery is idempotent. The model has no failing sync; what happens after one is
    tested.
- Proved of the program: the CRC-32C and SipHash-2-4 functions it prints compute what
  `DN.News.Journal` and `DN.News.SipHash` define, as `DN.News.FramerCode` proves the framers; no run
  of the program fails, by the analysis of [0004](0004-safety-analysis.md). The analysis now costs
  about 40 s and 7.4 GB; if the store's code takes it past 12 GB, the program is split into
  functions and the analysis extended to calls.
- Tested:
  - that the program is the specification, as for the session: the model, an independent reference
    in Python and the compiled program against each other;
  - acceptance against the article corpus of INN's tests (`tests/data/articles`, ISC licence),
    with our own expected outcomes for an injecting agent, and the header fields RFC 5322, RFC
    5537 and RFC 8315 print;
  - the host's worker pool, with failed and slow syncs, no space and short writes injected
    (`libfiu`);
  - process crashes: the server killed at each operation of a job, then restarted;
  - power loss: the spool on LazyFS, a FUSE file system that keeps unsynced data in its own cache
    and drops it on command, cleared at each operation of a job, then restarted; LazyFS makes
    creations, renames and removals durable at once, so a missing directory sync is caught by the
    model, not by this test; and appends torn by LazyFS's `torn-op` — a prefix kept, the end kept,
    the ends kept and the middle lost;
  - a corrupt store at every entry point — start, POST, HEAD, STAT, ARTICLE, BODY — after the
    table `fn` keeps for its own store;
  - two connections posting the same Message-ID, and overlapping crossposts, at once;
  - POST and reading back with `nntplib` and raw sockets, across restarts.
- Not claimed: that the kernel and the file system keep the guarantees of the model; anything about
  the host's workers beyond the tests; that the program is its specification on every run.

## Consequences

- The layout gains file jobs and their completions, the wall clock, the run's random value and a
  journal's key, the configuration, and whether a connection may post; the heap grows to 4 MiB, and
  the theorem that the layout fits the heap moves with it.
- `native/nntp_host.c` gains the worker pool, the lock, and `--spool`, `--group`,
  `--path-identity` and `--post-from`.
- 0003's answers change as above: the greeting, CAPABILITIES, HELP, and HEAD and STAT by message-id.
- New lanes: the store's model against its reference and the corruption table; the crash lane on
  LazyFS, which needs `/dev/fuse` and the right to mount — in CI on the runner, locally in a
  container of its own; the `nntp` lane gains POST and restarts.
- LazyFS, its two dependencies and libfiu are pinned by digest in `tools.lock.json` and built
  offline, as the other tools built from source are; LazyFS also needs the system's libfuse 3.
- `docs/nntp.md`, `docs/assurance.md` and `docs/baseline.md` move with the code.

## References

1. RFC 3977 §3.2.1, §3.4, §5.1, §6, §6.2.1.2, §6.3.1; RFC 5536 §2.2, §3, §3.1, §3.1.3, §3.1.4,
   §3.2.8, §3.2.12, §3.2.14; RFC 5537 §3.2.1, §3.3, §3.4.1, §3.5, §3.7 (all in
   [`rfcs/`](../../rfcs)); RFC 3798; RFC 5322 §2.1.1.
2. `fn`, `specs/storage.md`, `specs/failures.md`, `specs/store-corruption-matrix.md`,
   <https://github.com/emberian/fn>.
3. T. S. Pillai et al., All File Systems Are Not Created Equal, OSDI 2014; J. Bornholt et al.,
   Specifying and Checking File System Crash-Consistency Models, ASPLOS 2016.
4. T. Chajed et al., Verifying Concurrent, Crash-Safe Systems with Perennial, SOSP 2019;
   T. Chajed et al., Argosy, PLDI 2019; H. LeBlanc et al., PoWER Never Corrupts, OSDI 2025.
5. LazyFS, <https://github.com/dsrhaslab/lazyfs> (MIT); M. Ramos et al., When Amnesia Strikes:
   Understanding and Reproducing Data Loss Bugs with Fault Injection, PVLDB 17(11), 2024.
6. PostgreSQL's fsync errors, <https://wiki.postgresql.org/wiki/Fsync_Errors>; Docker's default
   seccomp profile and `io_uring`, <https://github.com/moby/moby/issues/47532>.
7. INN, `nnrpd/post.c`, `lib/headers.c`, `tests/data/articles`, `doc/pod/inn.conf.pod`,
   <https://github.com/InterNetNews/inn>.
8. J.-P. Aumasson and D. J. Bernstein, SipHash: a Fast Short-Input PRF, INDOCRYPT 2012,
   <https://github.com/veorq/SipHash>; M. Zheng et al., Understanding the Robustness of SSDs under
   Power Fault, FAST 2013.
