# NNTP implementation plan

There are no NNTP commands implemented yet. `DN.News.Framing` proves a chunk-composition property for CRLF detection; it is the beginning of a specification, not a protocol parser. This plan separates a first useful implementation from later extensions without treating optional protocol features as already supported.

## Initial profile

Implement RFC 3977 with a non-mode-switching reader/poster profile. Advertise only capabilities whose behavior is implemented and tested. A discovery-only development server is not a complete implementation of RFC 3977: HEAD and STAT are mandatory too.

The command inventory below follows [RFC 3977 Appendix B](../rfcs/rfc3977.txt). LIST ACTIVE and LIST NEWSGROUPS are required when advertising READER (§7.6.2). All rows are currently **planned**.

| Capability | Commands | Intended stage |
| --- | --- | --- |
| Mandatory | CAPABILITIES, HEAD, HELP, QUIT, STAT | First protocol/store slice |
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
| 4644 | Streaming feeds | Add after durable IHAVE ingestion and deduplication work |
| 6048 | LIST extensions | Add according to actual client/feed needs |
| 8054 | Compression | Later; include resource and decompression limits |
| 8315 | Cancel locks | Later; cancellation policy is separate from basic article delivery |
| 4707 | Response-code registration | Reference for extensions |
| 2980 | Historical extensions | Compatibility reference; not a substitute for RFC 3977 |

TLS design also needs RFC 4642, which is not yet in the local collection. Moderation, control messages, authentication, and relaying have policy consequences beyond recognizing commands. Defer capabilities deliberately and document the role the server actually performs.

## Offline exchange and filesystem views

Define a versioned batch envelope for immutable articles with explicit bounds, integrity checks, and restartable import. Import should reuse the network path's article validation, deduplication, and durable acceptance transaction. Test exporting, carrying a batch with no network connection, importing twice, and recovering from an interrupted import.

9P or another filesystem interface can expose groups, articles, or submission queues later. It should reuse the same storage rules; raw writable spool directories would bypass those invariants. A friendly human interface can consume the same article and thread data once those contracts settle.
