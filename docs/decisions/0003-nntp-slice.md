# 0003. The first NNTP slice: what it answers, how it frames input, and what is proved

Status: accepted, 2026-09-27.

## Question

[#16](https://github.com/emberian/dragons-net/issues/16) is the first code that speaks NNTP. It
has to fix, before any of it is written: which commands the slice answers and how; how the
program and the host exchange events inside the design of
[0002](0002-entry-and-memory.md); the limits on input and time, and what happens past each of
them; and what of all this is a theorem and what is a test.

## What the standard fixes

From [RFC 3977](../../rfcs/rfc3977.txt):

- A command line is `keyword *(WS token) EOL`, with `EOL = *(SP / TAB) CRLF`, `WS = 1*(SP / TAB)`
  and a keyword of at least three characters (§9.2, §9.8). Keywords are case-insensitive; one
  command per line; a command line is at most 512 octets with its CRLF, and its arguments at most
  497 (§3.1).
- A multi-line block is lines ending in CRLF, with no NUL and no CR or LF apart from those line
  ends; a line starting with "." is dot-stuffed, the block ends with "." CRLF, and the reader
  undoes both (§3.1.1). No line length is set for blocks.
- 500 answers an unknown command and 501 a syntax error, but a server must not answer a mandatory
  command with 500; a line must not be truncated or split and then interpreted (§3.2.1).
  CAPABILITIES, HEAD, HELP, QUIT and STAT are mandatory (§3.4, and the usage of each).
- The server processes pipelined commands in order and keeps their responses in that order
  (§3.5).
- An inactivity timer, if any, should be at least three minutes, with a shorter limit allowed for
  the first command; on expiry the server should close without a response (§3.1). A server that
  ends a connection for its own reasons gives 400 to the next command (§3.2.1).
- The greeting is 200 when posting is allowed and 201 when it is not (§5.1). CAPABILITIES lists
  `VERSION 2` first and only what the session can do; given a keyword it does not know, it answers
  as if there were none, and given an argument that is not a keyword, 501 (§3.3.2, §5.2). HELP is
  100 and a free-text block (§7.2). QUIT is 205, after which the server closes, and an argument to
  it is a 501 (§5.4); HELP takes none either (§9.2), so one is a syntax error (§3.2.1).
- HEAD and STAT with no group selected answer 412 to a number or to no argument, and 430 to a
  message-id the server does not have (§6.2.2, §6.2.4).

## What servers do where the standard is silent

INN, the reference NNTP server, at commit `6843efc`:

- `include/inn/nntp.h`: `NNTP_MAXLEN_COMMAND 512`, `NNTP_MAXLEN_ARG 497`,
  `NNTP_MAXLEN_MSGID 250`.
- `nnrpd/line.c` ends a line at LF and drops a CR before it, so it takes a bare LF as a line end.
  `nnrpd/nnrpd.c` ignores an empty line, skips leading white space when it splits a line
  (`nArgify`), and answers an overlong line (`RTlong`) with 501 when its first word names a
  command it has and with 500 otherwise, keeping the connection open.
- [`inn.conf`](https://www.eyrie.org/~eagle/software/inn/docs/inn.conf.html): 10 seconds for the
  first command (`initialtimeout`), 1800 seconds of inactivity (`clienttimeout`), 1,000,000
  octets for an article (`maxartsize`).

The SMTP smuggling defects of 2023 (CVE-2023-51764, -51765, -51766) came from servers that took
`<LF>.<CR><LF>` as the end of a data block while others did not; NVD names the remedy as always
refusing an LF without CR. Leniency about line ends is where two parsers of one stream come to
disagree.

A server that renews an inactivity timer on every byte can be held by a client that sends one
byte at a time, so the timer needs a deadline beside it that bytes do not renew. A server that
closes with unread input on the socket makes Linux answer with a reset, which can destroy the
last response before the client reads it; web servers therefore close in two steps, shutting
down their side first and reading what still arrives for a while (nginx `lingering_close`: at
most 30 s in all, at most 5 s of silence).

## Decision

### What the slice answers

- On a new connection, the greeting: `201`, the server's name and revision, and the address of
  its source — the offer AGPL-3.0 §13 asks to make prominently.
- CAPABILITIES: `101`, then `VERSION 2`, `IMPLEMENTATION` with the revision, and nothing the
  session cannot do; no READER, no POST, no LIST.
- HELP: `100`, then a block listing the commands the server has and, again, the revision and the
  address of its source.
- HEAD and STAT, against a store that is empty until
  [#17](https://github.com/emberian/dragons-net/issues/17): `412` to a number or to no argument,
  since no group can be selected; `430` to a message-id; `501` to anything that is neither. A
  number is one to sixteen digits of value at most 2,147,483,647 (§6, §9.8), zero included, as
  INN takes it; a message-id has the form of §9.8: `<`, one to 248 printable octets other than
  `>`, then `>`. CAPABILITIES answers an argument that is a keyword of §9.8 as if there were none,
  and anything else with `501`.
  With them the slice answers every mandatory command of RFC 3977, so `VERSION 2` is not a false
  claim.
- QUIT: `205`, after which the connection closes; input after the QUIT is not answered.
- Anything else is `500`. The order of the checks is: an empty or white-space-only line is
  ignored, as INN does; a line whose first word is not a command the server has is `500`,
  whatever else is wrong with it; a line naming such a command that is malformed in any way —
  bytes it may not contain, arguments it does not take, too long — is `501`. An overlong line is
  never ignored, since only its first octets are kept: with no word among them it is `500`.
- Pipelined commands are answered in order, one response per command.

### How input is framed

- A command line ends at an LF. It is a command only if a CR stands right before that LF and
  nowhere else, and it contains no NUL; otherwise it is malformed and answered as above. Unlike
  INN, a bare LF therefore ends the line without making it a command, so no command is ever taken
  from a line the standard does not allow, and the answer is still given at once.
- Leading and trailing spaces and TABs are ignored, as INN ignores them, and so is case in
  keywords; words are separated by spaces and TABs, so a byte such as NUL joined to a keyword makes
  another word.
- A line longer than 512 octets with its line end is not kept: the program keeps enough of it to
  know its first word, drops the rest up to the LF, and answers it by the rule above. The
  connection stays open, so the answers stay aligned with the commands.
- A multi-line block — read by no command of this slice, but framed by the same code, for #17 —
  ends only at CRLF "." CRLF. Its lines end at CRLF only; NUL, a CR or an LF inside a line make
  the block invalid; dot-stuffing is undone. A block that is invalid or larger than its buffer is
  read and discarded to its terminator, then refused whole, never truncated; one that is both is
  refused as invalid.

### Time and resources

| Limit | Value | Source |
| --- | --- | --- |
| command line, with its line end | 512 octets | RFC 3977 §3.1 |
| arguments | 497 octets | RFC 3977 §3.1 |
| message-id | 250 octets | INN `NNTP_MAXLEN_MSGID` |
| first command after the greeting | 10 s | INN `initialtimeout`; RFC 3977 §3.1 allows it |
| inactivity: no command answered and no output taken | 1800 s | INN `clienttimeout`; RFC 3977 asks for at least 180 |
| one command line, from its first octet to its line end | 180 s | ours: a deadline bytes do not renew, no shorter than RFC 3977's minimum |
| closing after QUIT | 30 s in all, 5 s of silence | nginx `lingering_time`, `lingering_timeout` |
| connections | 64 | ours, for the slice; set at build time |

When a deadline passes the connection is closed without a response and what it had not yet been
sent is dropped (RFC 3977 §3.1). A client can hold a connection for as long as it sends a command
within every inactivity period, as with INN; the connection limit bounds how many can, and limits
per client belong with the operational limits of
[#21](https://github.com/emberian/dragons-net/issues/21), as do a 400 greeting at the limit and a
400 to the next command when the server shuts down.

Backpressure: while a connection has output the kernel has not taken, the program asks the host
not to read from it, and processes no further command already received from it. When the output
is taken, the program resumes: it first answers the commands it holds, then asks for input again.
The command-line deadline runs from when the program begins reading a line, and only while it is
waiting for the rest of that line; the inactivity deadline counts output taken as activity, so a
client that reads slowly is not closed while it reads, and one that stops reading is closed when
the inactivity deadline passes.

After a QUIT, the host sends the 205, shuts down the sending side, reads and drops what still
arrives, and closes when the client closes or the lingering limits pass. When the client shuts
down its sending side (end of input), the program answers the commands it already has and then
closes. A reset or a failed send closes at once.

### The vocabulary between program and host

As [0002](0002-entry-and-memory.md) set out: the program's `main` loops, and each turn makes two
external calls on arrays in its heap. A connection is named by an index below the connection
limit and a generation the host increases each time it gives the index to a new connection; a
generation is a word, and the host does not give out an index and generation it gave out before.

- `@dn_next` takes the time the program needs its next turn at, written into the first word of
  its array before the call, in the host's clock: the earliest deadline it waits for, or the
  clock of the last batch (at least 1) when a connection can go on at once, or zero for none. The
  host uses it as its `poll` timeout. It depends on how much of each send the kernel took, which
  the program learns only once `@dn_emit` returns. It returns a batch: the host's monotonic clock in
  milliseconds, the revision and the address of the source the replies name, then up to `K`
  events — opened, bytes received (in the event's own slot, at most one slot's worth), ready to
  write, end of input, closed. The host touches the heap only inside a call, so it cannot finish
  a send on its own between calls. The configuration bytes of both calls carry the version of the
  layout; a host that finds another version stops the run in that call.
- `@dn_emit` hands the host a batch of actions: their number, then a slot for each connection
  that holds its action, or kind zero when it has none. Per
  connection there is at most one action per batch, so bytes cannot be reordered: send these
  bytes, then say whether to read from the connection; close gracefully (after QUIT or the end
  of input, once everything sent was taken); or close at once. The host reads from the connection
  only once everything the send carried was taken, and reports input from a connection at most
  once a batch. For a send, the host writes back into the same array how much the kernel took at
  once; the program reads nothing else of the array back. What the kernel did not take stays with
  the program, which sends it again when a later batch reports the connection ready to write.
- The host knows sockets and the clock and nothing of the protocol. It gives out what one `poll`
  reported before polling again; polls a connection for input only while the program asks for
  input from it; stops polling the listening socket while every index is in use; receives and
  sends only inside a call and only within the array the call names, checks that array lies in
  the heap, sends with `MSG_NOSIGNAL`, and writes the heap header before `cml_main`. It carries
  out an action only if the generation in it is the connection's current one; the program ignores
  an event whose generation is not the one it holds for that index.
- A host that breaks this contract — more events than a batch, more bytes than a slot, an index
  past the table, input the program did not ask for, more taken than sent, an index opened twice,
  a clock that goes back or reaches 2^62, an event of no kind the layout has, an identity that
  does not fit the replies, a word of the program's own area the program finds out of the range
  it keeps it in (which a host that writes only into its arrays is not seen to cause, in tests)
  — stops the run: the program writes the code of the breach into a word
  of its own area and returns from `main`, and the host, whose runtime ends the run there, reads
  the code. The model also refuses a count for no send, which the layout cannot express: each
  count lies in its send's slot.

The layout — offsets down to the fields of an event and an action, `K`, slot size, the version,
the codes of events, of actions and of the stops the host has to know — is defined once in Lean
and emitted as a C header, so that the program and the host cannot disagree about it.

### What is proved and what is tested

- The whole server `main`: in the Lean model of Pancake, extended with the call through which a
  run enters `main` and with `semantics`, which says whether a run fails, terminates or diverges:
  for every FFI oracle, every amount of fuel (the model's clock) and every content of the heap
  after its header, provided the heap covers the program's layout, the run is not `Fail`. Each
  outcome is then running out of fuel, the end of a run the host chose inside a call
  (`FinalFFI`), or a return, which the loop is written to make only when the host breaks the
  contract; the theorem does not say which. `Fail` in the upstream semantics
  also covers running off the end of `main`, so the loop is written never to fall through. The
  theorem is assembled from theorems about the pieces the program is built from, as for the byte
  copy and the number printer; for the session's program, from a safety analysis proven sound
  once and run on the program by the kernel ([0004](0004-safety-analysis.md)).
- The framing code is equal to a framing specification written from the grammar above, whatever
  the split of the input into received chunks.
- Replies are the texts `DN.News.CommandSpec` gives, laid out once in the program's own area
  and copied from there with the identity; that the program sends them is tested with the rest of
  the session, not proven. The reply language of [0001](0001-embedding.md) is not used here.
- The session — which command gets which reply, in which order, and when a connection closes — is
  specified in Lean apart from its code. The code is held against the specification by the model,
  an independent reference in Python and the compiled code: on transcripts split at every octet,
  on hostile sockets and against an independent client. A theorem relating the session code to
  its specification is not part of this slice.
- Not claimed: anything about the C host beyond what the FFI oracle quantifies over, and the rest
  of what [assurance](../assurance.md) lists as trusted (the transcription of the semantics, the
  printer and CakeML's parser, the runtime, the linker); running out of stack, which the upstream
  theorem allows unless the stack is at least the bound the compiler computes (the host provisions
  1 MiB; the bound itself is not yet obtained, [assurance](../assurance.md) item 8); the step from the model with fuel to the trace of an
  unending run.

## Consequences

- The model gains the entry call and `semantics`; the gate learns a second profile: a `main` with
  external calls to the two names above, arrays addressed from `@base`, and a loop that ends only
  when the host ends a call or breaks the contract.
- `lean/DN/News` holds the framing specification and code; the session specification and code
  follow it.
- `native/nntp_host.c` is the server's host. The exported kernels stay tests outside the theorem.
- `docs/nntp.md` lists what the slice answers; `docs/assurance.md` items 7 and 8 move from
  "decided" to "built" for this server.

## References

1. RFC 3977, Network News Transfer Protocol (NNTP): §3.1, §3.1.1, §3.2.1, §3.3.2, §3.4, §3.5,
   §5.1, §5.2, §5.4, §6.2.2, §6.2.4, §7.2, §9.2, §9.8.
2. INN at `6843efc`: `include/inn/nntp.h`, `nnrpd/line.c`, `nnrpd/nnrpd.c`, `lib/argparse.c`,
   <https://github.com/InterNetNews/inn>; `inn.conf(5)`,
   <https://www.eyrie.org/~eagle/software/inn/docs/inn.conf.html>.
3. NVD: CVE-2023-51764, CVE-2023-51765, CVE-2023-51766.
4. nginx, `ngx_http_core_module`: `lingering_close`, `lingering_time`, `lingering_timeout`,
   <https://nginx.org/en/docs/http/ngx_http_core_module.html>.
5. CakeML `ed31510`, `pancake/semantics/panSemScript.sml`: `semantics_def` and the `Call` clause.
