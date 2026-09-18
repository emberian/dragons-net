# Project backlog

The live [roadmap, #28](https://github.com/emberian/dragons-net/issues/28), owns
the project work list. Its 27 initial work items have acceptance criteria,
reviewed source references, area/priority/status labels, and milestones. They
are GitHub sub-issues of the roadmap; hard prerequisites also use GitHub's
blocked-by relationships. Issue bodies explain the sequencing. Update both the
relationship and prose when a dependency changes.

The initial backlog follows the [inherited-code review](reviews/README.md).
Nested-load printing and CI failure propagation were repaired in `1db1e29`;
the remaining issues describe unfinished work. This is not a claim that the
inherited native code is ready to activate or that all compiler proofs compose.

## Work streams

| Milestone | Initial scope |
| --- | --- |
| [Compiler assurance](https://github.com/emberian/dragons-net/milestone/1) | #1–#8: inhabited contracts, FFI/frame facts, generated regressions, parser and semantic bridges, HOL rebuild, patched bootstrap, and compiler inputs |
| [Owned native dataplane](https://github.com/emberian/dragons-net/milestone/2) | #9–#15: identities, terminality, resource bounds, timers, io_uring/kqueue, and comparable service benchmarks |
| [Durable NNTP service](https://github.com/emberian/dragons-net/milestone/3) | #16–#21: bounded framing, durable articles, reader/poster commands, overview, access policy, and service operations |
| [Federation and future interfaces](https://github.com/emberian/dragons-net/milestone/4) | #22–#27: feeds, offline bundles, human UI, 9P/filesystem views, Dragon egg ABI, and extension policy |

Milestones are parallel work streams, without invented delivery dates.
The later work is deliberately marked as backlog. Capability and policy decisions
will produce further bounded issues; the list is not a promise that all RFC
extensions can be implemented in six tasks.

## Good starting points

For compiler assurance, start with [inhabited contracts (#1)](https://github.com/emberian/dragons-net/issues/1),
[FFI and frame conditions (#2)](https://github.com/emberian/dragons-net/issues/2),
or [generated native regressions (#3)](https://github.com/emberian/dragons-net/issues/3).
The [HOL rebuild (#5)](https://github.com/emberian/dragons-net/issues/5) is an
independent infrastructure task.

For the optimized dataplane, agree [identities (#9)](https://github.com/emberian/dragons-net/issues/9),
[operation terminality (#10)](https://github.com/emberian/dragons-net/issues/10),
and [finite resource accounting (#11)](https://github.com/emberian/dragons-net/issues/11)
before accepting the native port. Keep the existing echo workload as its reference.

For protocol work, [framing (#16)](https://github.com/emberian/dragons-net/issues/16)
and [the durable spool (#17)](https://github.com/emberian/dragons-net/issues/17)
can proceed using the reference host. They do not need to wait for an optimized
reactor or an entire compiler correctness theorem.

See [CONTRIBUTING](../CONTRIBUTING.md) for claiming work, status/priority meanings,
validation, and closing issues. Ownership is intentionally unassigned; no external
contributor has been committed to a task. Status labels need maintainer review
when prerequisites close; there is no hidden automation updating them.
