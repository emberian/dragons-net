# 0005. The article store: durable acceptance, file operations through the host, and what is proved

Status: accepted, 2026-09-29.

## Question

[#17](https://github.com/emberian/dragons-net/issues/17) asks for a bounded local spool with one
ingestion path for posting, feeds and import: durable acceptance, deduplication by Message-ID, a
group index with crossposts, an exact point before which no acceptance is reported, crash recovery
with bounded work, and rejected or partial articles never visible. The session of
[0003](0003-nntp-slice.md) answers from an empty store. To fix before the store is written: where
its logic runs; how the host reaches the disk without stalling connections; the files on disk, the
durability point, failures and recovery; how an article's bytes flow and what the heap holds; which
articles are accepted and what the server adds; what the slice answers from the store; and what is
a theorem and what is a test.

## What the standards fix

- A proto-article may omit Message-ID, Date and Path, must not carry Injection-Info or Xref, and is
  otherwise a valid article ([RFC 5537](../../rfcs/rfc5537.txt) §3.4.1); an article has From,
  Newsgroups, Subject, Message-ID, Date and Path, each at most once
  ([RFC 5536](../../rfcs/rfc5536.txt) §3, §3.1). Header fields are US-ASCII (§2.2); a msg-id is at
  most 250 octets and compared by octets (§3.1.3). Newsgroup names reserved by §3.1.4 must not be
  used for ordinary groups.
- An injecting agent should accept only from a trusted source; must reject a proto-article without
  its mandatory fields, with Injection-Info or Xref, with `POSTED` in Path, or not valid by RFC
  5536, and should reject fields deprecated for Netnews; should reject an Injection-Date or Date
  more than 24 hours ahead or too far past, the cutoff no shorter than 72 hours; should reject one
  with no valid group, crossposts to unknown groups being allowed; must add Message-ID and Date
  when absent; must not alter the body or an existing Message-ID or Injection-Date; must add a
  Path tail entry and update Path; should add an Injection-Info identifying the source; adds
  Injection-Date unless both Message-ID and Date were present; and must have a list, possibly
  empty, of moderated groups (RFC 5537 §3.5). A serving agent rejects an article it has already
  accepted and may add Xref (§3.3, §3.7).
- Article numbers rise in order of arrival ([RFC 3977](../../rfcs/rfc3977.txt) §6). POST answers
  340 to send the article, 440 if posting is not permitted, then 240 or 441 (§6.3.1); an internal
  fault that keeps the server from carrying out a command is 403 (§3.2.1). The greeting is 200 when
  the client may post, 201 otherwise (§5.1). A command is either not implemented (500) or
  implemented fully, and a form needing a command the server lacks answers with that case's code,
  as ARTICLE answers 412 without GROUP; without the READER label a server may implement some of its
  commands, though implementing part of a bundle is discouraged (§3.4). By message-id with no group
  selected, ARTICLE answers with the number 0 (§6.2.1.2).

## What others do

The ACL2 server `fn` keeps an immutable body, an append-only journal of checksummed records and an
index derived from it; it commits in four phases — reserve, durable object, durable commit record,
publish — acknowledges only once the commit record is durable, never reuses an identifier it has
handed out, and tells a known failure from an indeterminate one: an unacknowledged commit may
survive a crash, an acknowledged one may not vanish. Kafka and etcd frame their logs with a length
and a CRC-32C, SQLite checksums its own; INN's tradspool does not sync article files. A file is made
durable by writing it, syncing it, renaming it into place and syncing the directory; no Linux file
system makes the directory sync unnecessary by contract. After a failed `fsync` the page cache's
state is unknown, and a retry can report success for lost data (PostgreSQL, 2018). Event-loop
servers keep blocking file calls off the loop on a few threads that report through a descriptor the
loop polls (nginx, Redis); `io_uring` runs `fsync`, and buffered writes on ext4, on kernel worker
threads anyway, and Docker's default seccomp profile refuses it. The closest verified system is
Mailboat (Perennial, SOSP 2019), a mail server that spools a message and links it into place,
proved crash-safe against a file system whose writes are durable at once; none is verified against
one that defers durability. INN accepts UTF-8 in header fields, beyond RFC 5536, and sets no limit
on crossposts.

## Decision

### Where the logic runs

In the program, as for the session: it decides what is accepted, writes the article and its journal
records, allocates article numbers, answers from its index and recovers from the journal. The host
carries out the file operations it is told to, on one directory, and reports what happened; it
knows nothing of articles.

### File operations through the host

- A new action, a file job: up to eight primitive operations, done in order by a worker thread and
  stopped at the first that fails. Its completion, in a later batch, names the job, how many
  operations succeeded, the failed one's class — an I/O error, no space, a name that exists or does
  not, another — and two result words per operation: a file's place and generation, octets read, a
  size, names listed. The program orders operations within a job, and jobs by starting one only
  after those it depends on completed.
- The operations: create a file under a new name, failing if it exists; open a file; write bytes at
  an offset, all of them; read at an offset; report a size; `fdatasync`, `fsync`; rename; remove;
  truncate; sync the directory; open the directory and list its names a page at a time; close. A
  name is a kind and a number, made by the host into the name `DN.News.Journal` gives, relative to
  the directory opened at start (`openat`, `renameat`, `unlinkat`).
- A created or opened file stays open across jobs, in the host's table of sixteen places (four
  POSTs, the journal, eight reads, spare), named by place and generation; the program closes it, the
  host only what is left at the end. A file is synced through the descriptor it was written through:
  Linux reports a failed write-back only to descriptors open at the time.
- The host retries a call a signal interrupted; writes on after a short write, one without progress
  failing as no space; reports a short read as it is. A failed close is a failed sync. Classes:
  `EIO` an I/O error; `ENOSPC`, `EDQUOT` no space; `EEXIST`, `ENOENT` the name's; any other,
  another.
- Jobs are identified by a slot and a generation, like connections; at most eight are in flight.
  Bytes to write are copied out of the heap inside `dn_emit` and bytes read are copied in inside
  `dn_next`, so the host still touches the heap only inside a call; a job moves at most 16,384
  octets.
- At most one sync of the directory is in flight: the next starts only once the program has learned
  how the last ended, so a failed one stops the store before any later one is trusted.
- The workers are a few threads with a queue; a completed job wakes the loop through an `eventfd`
  in the same `poll`. They are the host's own code: a pool is the norm for this, a library would
  outweigh the host, and `io_uring` would gain nothing here.
- At start the host takes an exclusive lock on the spool directory and refuses a spool another
  process holds.
- The host's test build carries a named point of failure before each file operation (libfiu's
  `fiu_return_on`), enabled from outside as the host starts or while it runs, as PostgreSQL's
  injection points and SQLite's test build do; built without `FIU_ENABLE`, the server has no point
  and does not load libfiu. libfiu's preload that fails POSIX calls does not know `openat`,
  `renameat` or `unlinkat`, which the host uses.

### On disk

- The spool directory holds the journal and one file per article; it is not the root of a file
  system, whose `lost+found` would be a name of another shape. An article is named by a sequence
  number of the store, one more than the highest that a journal record or a name in the directory —
  `a`, `t`, `q` or `j` — showed at start (none: 0) and than any handed out since, so a number is
  never handed out while a file may hold it. A file is first written under a temporary name derived
  from its number and then renamed to its final one, which by that rule no file holds. The final
  name is `a` and the number in sixteen lowercase hexadecimal digits, the temporary name `t` and the
  same digits; the journal is `journal`.
- The file holds the article as a reader receives it, without Xref: lines ending in CRLF,
  dot-stuffed, without the final dot line, the fields the server added in place.
- An article is accepted in four phases:
  1. reserve: the program checks the header section, reserves the Message-ID in the index and a
     sequence number, and counts the article against the bounds;
  2. body: it creates the temporary file, writes the article, syncs it, renames it to its final
     name and syncs the directory;
  3. commit: it appends one journal record — the sequence number, the Message-ID, each group by
     name with the number it allocates there, the sizes of the header section and of the file, and
     the file's CRC-32C — and syncs the journal;
  4. publish: it adds the article to the index and answers 240.

  Numbers are allocated when the record is appended, one record at a time, so articles are numbered
  in commit order, and a crosspost is one record. ARTICLE and HEAD insert the Xref field, built from
  the record, after the stored header fields.
- A failure is known only until the commit record is written: the article is refused with 441 and
  its temporary or final file removed. After that, a failed write or sync of the journal leaves the
  outcome unknown: the connection is closed without an answer (RFC 3977 §6.3.1 asks the client to
  check before posting again), and the next start decides from the journal. No failed write,
  truncation or sync of the journal, and no failed sync of any kind, is retried; each stops the
  store accepting for the rest of the run (POST then answers 403): after a failed write the journal
  may end in part of a frame, which only the next start truncates, and after a failed sync Linux may
  have dropped what it could not write, so no later sync is trusted. Articles in flight when the
  store stops are refused once their jobs in flight have completed; one whose record is appended and
  not yet synced is not answered, and its connection is closed. What the store has, it keeps
  serving. A process started again after a failed sync, without a loss of power, would read what
  Linux kept in memory and may never write, which what is proved does not cover: so the host marks
  a failed sync with the boot it happened in (`sync-failed`, in the spool and in a run directory a
  boot clears) before the program learns of it, refuses to start on a mark of this boot, or one it
  cannot read whole, until the machine restarts or the store is repaired (#21), and removes a whole
  mark of another boot. Not covered: a process killed between the failure and its mark.
- A journal record is framed as Kafka's record batches are, with a length, a type and a check over
  the type and the payload, and an end mark: the payload's length, four octets, least significant
  first as every number here; the tag, eight octets; the type, one octet; the payload; and the end
  mark, the octet 0xA5. The tag is SipHash-2-4 (Aumasson and Bernstein, 2012) under the journal's
  key, sixteen random octets the host gives when the journal is created, of the frame's offset,
  eight octets, the type and the payload: a keyed MAC, not a CRC, since part of a commit is an
  article's author's to choose, and a CRC is linear enough to aim at. The journal begins with the
  record naming its format, type 1: `dragons-net journal`, the version in one octet, 1, and the key,
  so its tag is made under the key it carries. A commit is type 2: the sequence number, eight
  octets, from 1; the Message-ID, a length octet and 1 to 250 octets; a count octet and 1 to 16
  groups, no two alike, each a name in a length octet and 1 to 64 octets and the article number,
  four octets, 1 to 2,147,483,647 (RFC 3977 §6); then the size of the header section, no more than
  the file's, the size of the file and the file's CRC-32C (RFC 7143 §13.1), four octets each. Each
  start, once recovery is done, appends a start record, type 3 with no payload, and syncs it before
  taking an article. The largest record is 1,390 octets, the format's 50; a start's is 14, less than
  any other's: appended where a torn tail was truncated, a start cannot leave whole a frame cut away
  there, and every other append lands where no frame has been. Recovery reads the journal from the
  start and stops at the first frame that does not check: short of its header or its length, with a
  length past the largest payload's, without its end mark, or with a tag its key does not make —
  before the format, a frame that does not carry a key the way the format does cannot be checked at
  all. If what follows fits the one append that can have been cut — the format's while no record has
  been read, one of the largest size after — and no frame that checks starts in it after its first
  octet, as none does after the last thing written, it is a torn tail, truncated away and the
  truncation synced; otherwise the store is corrupt. A crash may leave any octets of an append it
  cut short, up to its length: a prefix, zeros, junk, parts out of order (Zheng et al., FAST 2013,
  found failures under power loss, shorn and unserializable writes among them, on thirteen of
  fifteen SSDs). Filled with zeros, or cut after its length and filled with octets not ending in the
  end mark, it loses its end mark whatever the article it commits. That no crash leaves a frame
  whose tag checks where it was not written is assumed: past the format it takes the key, which
  neither a crash's junk nor an article's author has; at the start, where a format carries its own
  key, it takes a file system and a device that show a file no octets of another after a crash —
  ext4 writes data before the metadata pointing to it with `data=ordered` and `data=journal` and
  warns that `data=writeback` may show incorrect data; Zheng et al. saw no write land elsewhere —
  and junk making such a frame only by chance. A frame that checks but is no record a correct store
  writes — a format of another version among them — is corruption wherever it is, and so is a second
  format. At most one append is in flight; the next starts only after its sync completed. An append
  writes again the device block that holds the end of the record before it; the model assumes that a
  loss of power never garbles that block, rather than pad each frame to a block: a device that did
  would take that record with the append, which would read as a torn tail and be kept in a `j` file.
  The journal holds a record for each article the store holds and a start record of 14 octets for
  each start, never removed, and the directory those articles' files, the files set aside below and
  two names per POST in flight; recovery reads each once, so its work grows with the articles held
  and the starts made, without a checkpoint. Expiry, when it comes, brings compaction and
  checkpoints, and must keep the Message-IDs of what it removes, or a cutoff by date, since an
  article accepted once is rejected ever after.
- Recovery first syncs the journal and the directory, so that what it reads is what a loss of power
  keeps — a process killed before its syncs leaves its writes in the page cache, where the next
  would read them as done (PostgreSQL syncs its data directory at start for the same reason) — then
  reads the journal, lists the directory and acts in this order. When the journal ends in a torn
  tail after a record, the last record may have been answered 240 and damaged since, which no
  reading can tell from an append cut short: the tail's octets, after their offset in eight octets,
  are kept in a file named `j` and a sequence number of its own, synced with the directory, and then
  the tail is truncated and the truncation synced. Then names are tidied: a temporary name is
  removed, and a final name without a record is set aside under the quarantine name `q` and the same
  digits, never read and never removed — or removed, when that quarantine name exists already, or
  when the journal ended cleanly and no `j` file is numbered above it: sequence numbers are given in
  order, so a file numbered above every kept tail was made after them, and an article answered 240
  since has its record synced, which then reads back. Then the directory is synced, if a name
  changed. No file is taken before the truncation is synced, so a record a crash brings back from a
  tail whose truncation is not yet durable still has its file, and reads as written but not
  answered. An action of recovery that fails stops it: the server does not start, and the next
  start recovers again. Each start reports what is set aside, in the directory's order and the tail
  it kept last; taking it back, or removing it, is repair (#21). A name of any other shape makes the
  store corrupt.
- A corrupt store is refused: the server does not start and says why. Corrupt: a frame that does not
  check where what follows is no torn append's; a sequence number in two records; an article number
  in a group not above the one an earlier record gave it there (RFC 3977 §6); a record naming a file
  that is missing or of another size; a group the configuration lacks; files and no journal, a
  format cut short beside another name among them; no sequence number left to give. It says the
  first it finds, once the key is checked (see Configuration): a name of another shape, in the
  directory's order; files and no journal; where reading the journal stops in corruption; then each
  of these over the records in the journal's order, before the next — a sequence number a later
  record repeats, an article number not above, a group the configuration lacks, a file missing or of
  another size; last, no number left. A journal is created only in an empty directory, the
  directory then synced, and made again — cut to nothing, its format written and synced — when
  nothing is left of it but a format cut short and no other name is there. The store is never
  repaired silently; repair, when it comes, is a separate operation (#21). A Message-ID in two
  records is to be corruption too, which recovery does not check yet: the program refuses one the
  store has or has reserved (Which articles are accepted), and the specification takes up both
  with the index that reserves it.
- A file is checked as it is read: the program re-checks its lines — CRLF only, dot-stuffed — and
  its CRC-32C at the end. One that fails before anything was sent is answered 403; found while
  sending, it closes the connection without the final dot.
- Recovery runs before the first connection: the host listens only once the program reports the
  store ready.

### How an article's bytes flow

- At most four connections are in a POST at once; another POST waits, unanswered and not read,
  until one ends. Each POST holds a header buffer of 65,536 octets and a write buffer of 16,384.
- The article is framed as it arrives by a streaming block framer: it checks each line — CRLF only,
  no NUL or bare CR or LF — and finds the end of the block, keeping only its state. The header
  section is gathered in the header buffer and checked when it ends; the file is then created and
  the checked header section written with the added fields. The body is gathered in the write
  buffer and written a buffer at a time, and the connection is not read again until that write
  completes. A line the block may not hold, or an article past its size, refuses the article; the
  rest of the block is read and discarded, and the file removed.
- ARTICLE, HEAD and BODY read a file 16,384 octets at a time into a buffer of the connection's, at
  most eight reads in flight, and send it a slot at a time before reading more.
- An article must arrive within 1,800 seconds of its 340, a deadline bytes do not renew; waiting
  for a POST slot or for the store is not inactivity. A connection that ends before the terminator
  abandons its article once its job in flight completes: the file is removed and the reservation
  released. One that ends after the terminator does not stop the commit.
- The heap holds the index, the group table, the POST and read buffers and the session's layout:
  4 MiB in all, which the host provisions.

### Bounds

Set at build time, each with its reason: 4,096 articles in the store, files set aside (`q`, `j`)
counting against it; 64 groups, names at most 64 octets (ours); 16 groups in an article's Newsgroups
field (ours: INN sets no limit); 1,000,000 octets per article as it arrives, with its terminator, as
INN counts `maxartsize`, whose default it is; 65,536 octets for the header section and 998 for a
header line (ours, the line limit of RFC 5322). A full store refuses new articles (441); it never
drops old ones to make room. Comments may nest as deep as these bounds allow: their depth is a
count, as `DN.News.ArticleSpec` keeps it, not a stack.

### Configuration

The host is given the spool directory, a run directory for the mark of a failed sync, the groups,
the server's path identity and the networks allowed to post (by default loopback, until
authentication, RFC 4643, is added), and hands the groups and the path identity to the program,
which checks them: group names as RFC 5536 §3.1.4 allows, none reserved, and the path identity as a
domain name. Each opened connection carries whether it may post. The host also hands the program its
wall clock, in UTC and not checked to move forward, and random octets: the run's value, which
Message-IDs carry, and sixteen more that key a journal the program creates, written only to that
journal and used for nothing else, the program refusing to start without sixteen; and it logs each
connection's address with the run and its index.

### Which articles are accepted, and what the server adds

- Refused: a missing From, Newsgroups or Subject; a field that may appear once present twice (RFC
  5536 §3, §3.1 and §3.2, RFC 5322 §3.6, RFC 8315 §2), and, by policy as INN, a second
  MIME-Version, Content-Type or Content-Transfer-Encoding, since RFC 2045 describes an entity by one
  of each; any header field not valid by RFC 5536, in particular not US-ASCII, as RFC 5536 §2.2 and
  RFC 5537 §3.5 require (INN accepts UTF-8), with a line of a field body of white space alone, a
  message identifier longer than 250 octets in any field that holds one, a From of several
  mailboxes without a Sender, the distribution "All", or a date, a Received's included, that is no
  date; Injection-Info, Xref, or `POSTED` in Path; the trace fields of injecting agents older than
  RFC 5536 (NNTP-Posting-Host, NNTP-Posting-Date, X-Trace, X-Complaints-To), as RFC 5537 §3.5
  allows and INN does; a Message-ID, compared by octets, that the store has or has reserved; no
  known group among Newsgroups, or a reserved one, names compared as written; a Date or
  Injection-Date more than 24 hours ahead or more than 72 hours past, in UTC; a Control or
  Supersedes field, since this slice carries no control messages and Supersedes is a cancel; an
  Approved field, by policy, so that no approval passes before moderation exists; the fields RFC
  5536 §3.3 makes obsolete and RFC 3798 deprecates for Netnews; anything past the bounds. The order
  RFC 5322 §3.6 gives blocks of trace and resent fields is mail transport's and is not checked.
- Added, in RFC 5537 §3.5's order, Path first and the proto-article's fields after it as they were:
  Message-ID, `<seq.random@path-identity>` (the article's sequence number in the store and the
  run's random value), and Date from the wall clock, when absent; the Path tail
  entry and the `POSTED` entry for the path identity; Injection-Info with the path identity and a
  `logging-data` parameter naming the run and the connection; Injection-Date, unless the
  proto-article has one or had both Message-ID and Date. A present Injection-Date is kept. The body
  is not changed.
- An article to known and unknown groups is stored in the known ones.
- The four phases, the journal and the index take an article with the role it arrives in; POST
  checks it as an injecting agent, and feeds and import, in later issues, as their roles require.

### What the slice answers from the store

- POST, and the capability `POST`, while the store accepts, has at least one group and the client
  may post; the greeting is then 200, and 201 otherwise. Once the store stops accepting, new
  connections are greeted with 201 and are not offered POST; those greeted before get 403.
- HEAD and STAT by message-id answer from the store (221, 223). ARTICLE and BODY are implemented in
  full: by message-id from the store, with the number 0, and 412 to a number or to no argument,
  since GROUP is not implemented. READER is not advertised until the reader commands are (#18).
  HELP lists ARTICLE, BODY and POST.
- A server started without a spool answers as 0003 fixes.

### What is proved and what is tested

The specifications, their proofs and the lanes that hold them against references written apart
from them are done; what needs the program or the host comes with them, as marked.

- Proved in Lean, of specifications:
  - which articles are accepted and what is added, each rule shown to matter by a version with it
    broken, as `DN.News.CommandSpec` does for command lines;
  - the streaming block framer gives the specification's verdict however the article is cut;
  - a journal of records reads back as those records; an append cut short — a prefix of its frame,
    that prefix and zeros, or its length and octets not ending in the end mark, to its length —
    reads as a torn tail, whatever the tag, when no frame that checks starts in it; a frame that
    does not check, with a record after it framed where it lies, is corruption; a start's frame is
    shorter than any other record's;
  - under a model of crashes in the vocabulary of Pillai and Bornholt (`DN.News.FsModel`) — a crash
    leaves each name, independently, holding what it held at the directory's last sync or anything
    it has held since, and each file, independently, with the octets no operation touched since its
    last sync followed by any octets, up to the most it has held since, assumed never to make a
    frame whose tag checks where it was not written, as above; a file no name is left holding is
    freed; so a synced file's data and a name whose directory was synced survive; a failed operation
    may have done any part of what it was asked, an append any first part of its octets and anything
    else all or nothing, and after a failed sync of a file or of the directory no later sync of it is
    trusted until power is lost — recovery after a crash at any point of any run, operations failing
    or not, yields every article answered 240, possibly some whose commit record was written but not
    answered, and never one refused before its record was written or a partial one (`store_safe` in
    `DN.News.StoreRun`: runs from an empty directory — starts, each with its own key and the last
    start's groups or more, the program's steps, crashes, the process ending — while numbers last),
    of the program as `DN.News.StoreOps` models it, whose steps take its part as given: a commit
    only once its file is placed, one at a time, with its own number, the file's size, a record the
    journal can hold and article numbers allocated in groups the store carries (`Allocated`); 240
    only after the journal's sync; no article accepted after a failed sync or write of the journal.
    That the host's concurrent jobs come down to such steps is argued, not proven, and one process
    runs at a time, as the lock is to ensure. After its actions a start finds the same articles
    again (`recover_again`, while numbers last); that it then has nothing left to do is tested. A
    restart after a failed sync of the journal or the directory without a loss of power is not
    covered, as above.
- To be proved of the program, once it is written: the CRC-32C and SipHash-2-4 functions it prints
  compute what `DN.News.Journal` and `DN.News.SipHash` define, as `DN.News.FramerCode` proves the
  framers; no run of the program fails, by the analysis of [0004](0004-safety-analysis.md). The
  analysis now costs about 40 s and 7.4 GB; if the store's code takes it past 12 GB, the program is
  split into functions and the analysis extended to calls.
- Tested against references written apart from the specifications ([baseline](../baseline.md)):
  the grammar of header fields; acceptance, with the article corpus of INN's tests
  (`tests/data/articles`, ISC licence) and our own expected outcomes for an injecting agent, and the
  header fields RFC 5322, RFC 5537 and RFC 8315 print; the journal; the file system model; recovery,
  with the table of corruptions `fn` keeps for its own store; the store's program, held at every
  point of runs drawn from a fixed seed to what a crash may leave there; and libfiu's points and
  LazyFS, each held to what the tests below take of it.
- To be tested with the program and the host:
  - that the program is the specification, as for the session: the model, an independent reference
    in Python and the compiled program against each other;
  - the host's worker pool, with failed and slow syncs, no space and short writes injected at its
    points of failure;
  - process crashes: the server killed at each operation of a job, then restarted;
  - power loss: the spool on LazyFS, a FUSE file system that keeps unsynced data in its own cache
    and drops it on command, cleared at each operation of a job, then restarted; LazyFS makes
    creations, renames and removals durable at once, so a missing directory sync is caught by the
    model, not by this test; and appends torn by LazyFS's `torn-op` — a prefix kept, the end kept,
    the ends kept and the middle lost;
  - a corrupt store at every entry point — start, POST, HEAD, STAT, ARTICLE, BODY — after the table
    `fn` keeps for its own store;
  - two connections posting the same Message-ID, and overlapping crossposts, at once;
  - POST and reading back with `nntplib` and raw sockets, across restarts.
- Not claimed: that the kernel and the file system keep the guarantees of the model; anything about
  the host's workers beyond the tests; that the program is its specification on every run.

## Consequences

- The layout gains file jobs and their completions, the wall clock, the run's random value and a
  journal's key, the configuration, and whether a connection may post; the heap grows to 4 MiB, and
  the theorem that the layout fits the heap moves with it — done, unused yet.
- `native/nntp_host.c` gains the worker pool, the lock, and `--spool`, `--group`,
  `--path-identity` and `--post-from`.
- 0003's answers change as above: the greeting, CAPABILITIES, HELP, and HEAD and STAT by message-id.
- New lanes: done — the grammar of header fields, acceptance, the journal, the file system model,
  recovery against the table of corruptions, the store's runs, and the tools the crash tests rest
  on: libfiu's points and LazyFS, which needs `/dev/fuse` and the right to mount it, as a user in a
  user namespace of its own or through `fusermount3` — in CI as a job of its own, locally in a
  container of its own; to come — the crash lane on LazyFS; the `nntp` lane gains POST and
  restarts.
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
