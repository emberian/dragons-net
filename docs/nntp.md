# NNTP implementation plan

The first slice answers over sockets on loopback; [decision 0003](decisions/0003-nntp-slice.md) fixes what the first slice answers, how it frames input, its limits and what of it is proved. The framing is built: `DN.News.FrameSpec` states it over the whole stream, `DN.News.Framer` proves the framers give it however the input is cut into chunks, and `DN.News.FramerCode` proves the functions printed from them make exactly the framers' steps; the compiled code is held against the model and an independent reference ([details](baseline.md#framers)). The session's `main` runs the line framer's statements in place, where they are tested with the session, not proven. The session is specified: `DN.News.CommandSpec` says which reply each line gets and `DN.News.SessionSpec` how a connection is greeted, answered, held back and closed, held against an independent reference on a simulated host ([details](baseline.md#session-model)). The session's program (`DN.Server.Session`) is compiled, held against that model turn by turn, and proven in the model never to fail ([details](baseline.md#session-program)); `native/nntp_host.c` serves it over sockets, checked from outside with `nntplib`, raw clients and recorded transcripts, with the report of each run's turns held against the session's judge, the model and the sockets ([details](baseline.md#nntp-server)). Article storage ([#17](https://github.com/emberian/dragons-net/issues/17)) is next. This plan separates a first useful implementation from later extensions without treating optional protocol features as already supported.

## Initial profile

Implement RFC 3977 with a non-mode-switching reader/poster profile. Advertise only capabilities whose behavior is implemented and tested. A discovery-only development server is not a complete implementation of RFC 3977: HEAD and STAT are mandatory too.

The command inventory below follows [RFC 3977 Appendix B](../rfcs/rfc3977.txt). LIST ACTIVE and LIST NEWSGROUPS are required when advertising READER (§7.6.2). The first slice answers the mandatory commands without a store: CAPABILITIES (`VERSION 2` and `IMPLEMENTATION`; a keyword argument is ignored), HELP and QUIT, and HEAD and STAT as a server with no group selected and no articles (412 to a number or no argument, 430 to a message-id). A line naming one of these commands that is malformed — an argument the command does not take, a byte it may not hold, more than 512 octets — gets 501; a line naming any other command gets 500, and an empty line is ignored ([decision 0003](decisions/0003-nntp-slice.md)). The other rows are **planned**.

| Capability | Commands | Intended stage |
| --- | --- | --- |
| Mandatory | CAPABILITIES, HEAD, HELP, QUIT, STAT | First slice: answered, without a store; the store is #17 |
| READER | ARTICLE, BODY, DATE, GROUP, LAST, LISTGROUP, NEWGROUPS, NEXT | Reader completeness |
| LIST | LIST, LIST ACTIVE, LIST NEWSGROUPS | Reader completeness |
| POST | POST | Durable posting |
| OVER | OVER, LIST OVERVIEW.FMT | Practical reader compatibility |
| HDR | HDR, LIST HEADERS | Practical reader compatibility |
| IHAVE | IHAVE | Peer ingestion |
| NEWNEWS | NEWNEWS | Incremental peer/client discovery |
| LIST extensions in RFC 3977 | LIST ACTIVE.TIMES, LIST DISTRIB.PATS | Broader core coverage |
| MODE-READER | MODE READER | Compatibility review; initially avoid mode-switching |

Capability output includes VERSION 2 first, as required by §3.3.2. It must reflect the current session and permissions. Do not infer implementation from the software name or advertise a capability solely because a command keyword is recognized.

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
| 5536 | Netnews article format | Required for article ingestion/storage |
| 5537 | Netnews architecture and procedures | Required as injection/relay roles are added |
| 4643 | Authentication | Add with an explicit access-control and transport-security design |
| 4642 | Transport security (TLS) | Add with the authentication profile, in the form RFC 8143 leaves it |
| 8143 | TLS update to RFC 4642 | Implicit TLS on port 563 is preferred over STARTTLS |
| 4644 | Streaming feeds | Add after durable IHAVE ingestion and deduplication work |
| 6048 | LIST extensions | Add according to actual client/feed needs |
| 8054 | Compression | Later; include resource and decompression limits |
| 8315 | Cancel locks | Later; cancellation policy is separate from basic article delivery |
| 4707 | Netnews Administration System (Experimental) | Reference only; not planned |
| 2980 | Historical extensions | Compatibility reference; not a substitute for RFC 3977 |

TLS design needs RFC 4642 as updated by RFC 8143, which prefers implicit TLS on port 563 over STARTTLS; both are in the local collection. Moderation, control messages, authentication, and relaying have policy consequences beyond recognizing commands. Defer capabilities deliberately and document the role the server actually performs.

## Source offer for a network service

The licence is AGPL, so anyone who runs a modified dn over the network owes its users the corresponding source (LICENSE, section 13). Meeting that obligation is a protocol decision rather than a legal footnote, and we will carry the offer where a remote user can see it: the cheapest place in NNTP is the `HELP` response, which is free text, plus a line in the capabilities documentation, naming the running version and a URL that serves its source. Whatever the shape, it belongs in the first milestone that answers commands, not after deployment. The first slice does this: the greeting and the last line of the help name the revision and the address of the source the server is started with (`--revision` and `--source`, both required), and CAPABILITIES names the revision in `IMPLEMENTATION`; nothing yet ties the revision to the build.

## Offline exchange and filesystem views

Define a versioned batch envelope for immutable articles with explicit bounds, integrity checks, and restartable import. Import should reuse the network path's article validation, deduplication, and durable acceptance transaction. Test exporting, carrying a batch with no network connection, importing twice, and recovering from an interrupted import.

9P or another filesystem interface can expose groups, articles, or submission queues later. It should reuse the same storage rules; raw writable spool directories would bypass those invariants. A friendly human interface can consume the same article and thread data once those contracts settle.
