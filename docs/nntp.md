# NNTP implementation plan

The server answers over sockets on loopback: [decision 0003](decisions/0003-nntp-slice.md) fixes what its first slice answers, how it frames input, its limits and what of it is proved. The baseline says what of its [framing](baseline.md#framers), [session](baseline.md#session-model), [program](baseline.md#session-program) and [server](baseline.md#nntp-server) is proved and what is only tested.

Article storage ([#17](https://github.com/emberian/dragons-net/issues/17)): [decision 0005](decisions/0005-article-store.md) fixes the store, how the host reaches the disk, which articles POST accepts, what the slice answers from the store, and what of it is proved. The store is proven in the model and held against independent references ([journal](baseline.md#journal), [file system](baseline.md#file-system), [store](baseline.md#store), [store runs](baseline.md#store-runs), [session](baseline.md#session-model)); the server is tested under [crashes](baseline.md#crashes), [power loss](baseline.md#power-loss) and [faults](baseline.md#faults).

Reading — ARTICLE, HEAD, BODY and STAT by message-id, and by number in the group GROUP selects, with NEXT and LAST, and the overview, OVER and HDR — is in the program ([session program](baseline.md#session-program)), and the server answers it over sockets ([NNTP server](baseline.md#nntp-server)).

POST is in the program ([session program](baseline.md#session-program)), and the server takes it from the networks `--post-from` names, loopback by default ([NNTP server](baseline.md#nntp-server)). With a spool the host logs each connection on stderr as `connection RUN.N from ADDRESS port PORT`, `RUN.N` being the `logging-data` its articles carry; a line stderr cannot take at once is counted, not waited for.

This plan separates a first useful implementation from later extensions without treating optional protocol features as already supported.

## Initial profile

Implement RFC 3977 with a non-mode-switching reader/poster profile. Advertise only capabilities whose behavior is implemented and tested. A discovery-only development server is not a complete implementation of RFC 3977: HEAD and STAT are mandatory too.

The command inventory below follows [RFC 3977 Appendix B](../rfcs/rfc3977.txt). LIST ACTIVE and LIST NEWSGROUPS are required when advertising READER (§7.6.2).

Without a store the server answers the mandatory commands ([decision 0003](decisions/0003-nntp-slice.md)):

- CAPABILITIES: `VERSION 2` and `IMPLEMENTATION`; a keyword argument is ignored;
- HELP and QUIT;
- HEAD and STAT as a server with no group selected and no articles: 412 to a number or no argument, 430 to a message-id;
- MODE READER: 502, then the connection closes, as §5.3.2 asks of a server that does not advertise READER.

A line naming one of these commands that is malformed — an argument the command does not take, a byte it may not hold, more than 512 octets — gets 501. A line naming any other command gets 500, and an empty line is ignored. Rows that name no issue are **planned**.

| Capability | Commands | Intended stage |
| --- | --- | --- |
| Mandatory | CAPABILITIES, HEAD, HELP, QUIT, STAT | Answered; HEAD and STAT from the store by message-id and by number (#17, #18) |
| READER | ARTICLE, BODY, DATE, GROUP, LAST, LISTGROUP, NEWGROUPS, NEXT | Done (#17, #18) |
| LIST | LIST, LIST ACTIVE, LIST NEWSGROUPS | Done (#18) |
| POST | POST | Done (#17) |
| OVER | OVER, LIST OVERVIEW.FMT | Done, `OVER MSGID` (#19) |
| HDR | HDR, LIST HEADERS | Done, any header (#19) |
| IHAVE | IHAVE | Peer ingestion (#22) |
| NEWNEWS | NEWNEWS | Incremental peer/client discovery (#22) |
| LIST extensions in RFC 3977 | LIST ACTIVE.TIMES, LIST DISTRIB.PATS | ACTIVE.TIMES with the groups' creation dates (#21); DISTRIB.PATS not planned |
| MODE-READER | MODE READER | Not advertised: the server is not mode-switching and answers MODE READER as §5.3.2 asks of one (#18) |

Capability output includes VERSION 2 first, as required by §3.3.2. It must reflect the current session and permissions. Do not infer implementation from the software name or advertise a capability solely because a command keyword is recognized.

### Commands

What each command of RFC 3977 gets with a store, and what holds it: the session's lanes (`session_check.py` for the model, `session_native.py` for the program), the nntp lane over sockets with `nntplib` and Perl's Net::NNTP, and the crash, power and faults lanes. Without a store the first slice answers as above.

| Command | RFC 3977 | Answer | Held by |
| --- | --- | --- | --- |
| CAPABILITIES | §5.2 | `VERSION 2`, `IMPLEMENTATION`, READER, HDR, `LIST ACTIVE HEADERS NEWSGROUPS OVERVIEW.FMT`, `OVER MSGID`, and POST while the client may post | session lanes, nntp lane, faults lane after the store stops |
| MODE READER | §5.3 | 200 while the client may post, else 201, changing nothing | session lanes, Net::NNTP |
| QUIT | §5.4 | 205, then the connection closes | session lanes, nntp lane |
| GROUP | §6.1.1 | 211 with the count and the lowest and highest numbers, the first article current; 411 | session lanes, `nntplib`, Net::NNTP |
| LISTGROUP | §6.1.2 | GROUP's 211, then the numbers in the range of the articles held as the group is selected | session lanes, nntp lane, Net::NNTP |
| LAST, NEXT | §6.1.3, §6.1.4 | 223 with the article moved to; 412, 420, 421, 422 | session lanes, `nntplib`, Net::NNTP |
| ARTICLE, HEAD, BODY | §6.2.1 to §6.2.3 | By message-id, number or the current article, 220, 221, 222 and the file with Xref; 412, 420, 423, 430, 403 | session lanes, nntp, crash and faults lanes |
| STAT | §6.2.4 | 223; 412, 420, 423, 430 | session lanes, `nntplib`, Net::NNTP |
| POST | §6.3.1 | 340, then 240 once the journal is synced, or 441; 440, 403 | session lanes, nntp, crash, power and faults lanes |
| DATE | §7.1 | 111 and the wall clock in UTC | session lanes, `nntplib`, Net::NNTP |
| HELP | §7.2 | 100, the commands, the revision and the address of the source | session lanes, `nntplib` |
| NEWGROUPS | §7.3 | 231 and an empty list, as no group has a creation date (#21); a time without GMT is UTC, the server's | session lanes, `nntplib`, Net::NNTP |
| LIST, LIST ACTIVE | §7.6.1, §7.6.3 | 215, then a line a group the wildmat takes: name, highest, lowest, `y` while the store accepts, else `n` | session lanes, nntp lane, faults lane after the store stops |
| LIST NEWSGROUPS | §7.6.6 | 215 and an empty list, as no group has a description (#21) | session lanes, `nntplib`, Net::NNTP |
| IHAVE, NEWNEWS | §6.3.2, §7.4 | 500 (#22) | session lanes |
| OVER, XOVER | §8.3, RFC 2980 §2.8 | 224, then each article's line from its file read and checked whole, none made current; 412, 420, 423, 430; XOVER takes no message-id and gives an empty range an empty list, as INN | session lanes, `nntplib` |
| HDR, XHDR | §8.5, RFC 2980 §2.6 | 225, or XHDR's 221, then a line an article, the first field of its name; 503 for a metadata item but `:bytes` and `:lines`; XHDR labels a message-id's line with it and leaves out an article without the field | session lanes, XHDR by `nntplib` |
| LIST OVERVIEW.FMT, HEADERS | §8.4, §8.6 | 215: the seven fields, `:bytes` and `:lines` written `Bytes:` and `Lines:` for slrn, then `Xref:full`; `:`, `:bytes` and `:lines` | session lanes, OVERVIEW.FMT by `nntplib` |
| LIST ACTIVE.TIMES, DISTRIB.PATS | §7.6.4, §7.6.5 | 501; ACTIVE.TIMES with #21 | session lanes |

The status of LIST ACTIVE is the group's on this server, not the client's: a client that may not post sees `y` too (§7.6.3).

## Protocol test plan

* **Framing:** CRLF split at every boundary, multiple commands in a receive, empty/malformed command lines, command length limits, disconnect mid-line, article dot-stuffing and terminators across chunks. Decide resource limits and recovery behavior explicitly.
* **Session state:** selected group and current article transitions, empty groups and article holes, NEXT/LAST boundaries, numeric versus Message-ID forms, failures that preserve or invalidate state as specified.
* **Wire responses:** correct status codes, single/multiline form, dot transparency, order under pipelining, and partial writes. Pair golden transcripts with an independent client.
* **Article acceptance:** required headers and syntax, Message-ID identity, duplicate insertion, crossposts, Path handling appropriate to the role, size limits, and rejected input that never becomes visible.
* **Durability:** crash before/after body persistence, index update, and success response. Restart must preserve the documented acceptance guarantee. Test disk-full and interrupted writes.
* **Resource ownership:** bounded queues and buffers, slow readers/writers, disconnect during POST, cancellation/completion races, no reuse while a worker or kernel still owns a buffer.

## Further standards

The offline [RFC collection](../rfcs/manifest.json) supplies exact document hashes and source URLs.

| RFC | Role | Plan |
| --- | --- | --- |
| 5536 | Netnews article format | Required for article ingestion/storage; its grammar is taken from the text ([details](baseline.md#header-field-grammar)) |
| 5322 | Internet Message Format | The syntax RFC 5536 restricts: addresses, dates, comments, message identifiers |
| 5234 | ABNF and its core rules | The notation of every grammar here |
| 3986 | URI generic syntax | IPv4 and IPv6 addresses in a Path diagnostic |
| 2045, 2231 | MIME parameters and tokens | The `token` and `parameter` of Archive, User-Agent and Injection-Info; MIME's own fields are checked by RFC 5536's general rules only |
| 5537 | Netnews architecture and procedures | The duties of an injecting agent (§3.5), which the article specification follows ([details](baseline.md#article-acceptance)); relaying and serving roles as they are added |
| 7143 | iSCSI | Its CRC-32C (§13.1), which is to check every article's file, and the examples it prints (appendix A.4) ([details](baseline.md#journal)) |
| 3798 | Message disposition notification | Its Disposition-Notification-To, which it deprecates for Netnews (as RFC 8098, which obsoletes it, still does), is refused |
| 4643 | Authentication | Add with an explicit access-control and transport-security design |
| 4642 | Transport security (TLS) | Add with the authentication profile, in the form RFC 8143 leaves it |
| 8143 | TLS update to RFC 4642 | Implicit TLS on port 563 is preferred over STARTTLS |
| 4644 | Streaming feeds | Add after durable IHAVE ingestion and deduplication work |
| 6048 | LIST extensions | Add according to actual client/feed needs |
| 8054 | Compression | Later; include resource and decompression limits |
| 8315 | Cancel locks | The syntax of Cancel-Lock and Cancel-Key is checked with the other header fields; acting on them is later, as cancellation policy is separate from basic article delivery |
| 4707 | Netnews Administration System (Experimental) | Reference only; not planned |
| 2980 | Historical extensions | Compatibility reference; not a substitute for RFC 3977 |

TLS design needs RFC 4642 as updated by RFC 8143, which prefers implicit TLS on port 563 over STARTTLS; both are in the local collection. Moderation, control messages, authentication, and relaying have policy consequences beyond recognizing commands. Defer capabilities deliberately and document the role the server actually performs.

## Source offer for a network service

The licence is AGPL, so anyone who runs a modified dn over the network owes its users the corresponding source (LICENSE, section 13). Meeting that obligation is a protocol decision rather than a legal footnote, and we will carry the offer where a remote user can see it: the cheapest place in NNTP is the `HELP` response, which is free text, plus a line in the capabilities documentation, naming the running version and a URL that serves its source. Whatever the shape, it belongs in the first milestone that answers commands, not after deployment. The first slice does this: the greeting and the last line of the help name the revision and the address of the source the server is started with (`--revision` and `--source`, both required), and CAPABILITIES names the revision in `IMPLEMENTATION`; nothing yet ties the revision to the build.

## Offline exchange and filesystem views

Define a versioned batch envelope for immutable articles with explicit bounds, integrity checks, and restartable import. Import should reuse the network path's article validation, deduplication, and durable acceptance transaction. Test exporting, carrying a batch with no network connection, importing twice, and recovering from an interrupted import.

9P or another filesystem interface can expose groups, articles, or submission queues later. It should reuse the same storage rules; raw writable spool directories would bypass those invariants. A friendly human interface can consume the same article and thread data once those contracts settle.
