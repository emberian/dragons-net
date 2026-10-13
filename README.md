# dn

[![checks](https://github.com/emberian/dragons-net/actions/workflows/ci.yml/badge.svg)](https://github.com/emberian/dragons-net/actions/workflows/ci.yml)

**A compiler and dataplane foundation for Dragon’s News: an ambitious little NNTP server, and eventually a component of the dregg dragon’s egg operating system.**

The path is **Lean specifications and proofs → Pancake → CakeML → native code**, with a narrow host for sockets, buffers and durable storage, built on the inherited `orb-compiler`, `orb`, `drorb` and datacake work.

**Today: compiler infrastructure, models, a generated-code TCP echo server, and an NNTP server answering RFC 3977's mandatory commands on loopback, recovering its store at start; not yet a usable news server or an end-to-end verified executable.**

Start with [the compiler baseline](docs/baseline.md) and [assurance boundaries](docs/assurance.md); the [inherited-code review](docs/reviews/README.md) records the defects found in what was inherited.

## What’s here

| Area | Current state |
| --- | --- |
| [Compiler](lean/DN/Compiler) | The emitted Pancake subset and its proofs: syntax, lowering, the checked emitter, model execution, the safety analysis and a proven weakest precondition. |
| [Source language](lean/DN/Dsl) | A deeply embedded language of replies, proven in the model to compile to code that does what each program means ([why deep](docs/decisions/0001-embedding.md)). |
| [Server loop](lean/DN/Server) | The server's `main` and the session's program, reaching the host through external calls, proven in the model never to fail for any host and clock from a heap covering their layout ([details](docs/baseline.md#session-program)). |
| [Dataplane models](lean/DN/Dataplane) | Rings, slabs, completions, wakeups, deadlines and flow control, proven of the models; no refinement to a running host. |
| [Host primitives](crates/dn-runtime) | A tested Rust slab, connection permits and a partial-write cursor. |
| [Concurrency exploration](models) | Eight Rust models and 30 Loom tests, with recorded defects the tests must catch. |
| [Native execution](docs/baseline.md) | 35,520 differential cases, 300 generated programs, 26,039 copy-kernel checks, 311 CRC-32C buffers, 370 SipHash-2-4 messages, 28,704 journal readings, 2,066 recovered directories and 5,790 reply-table calls through the real compiler. |
| [TCP echo](docs/echo.md) | A bounded `poll` host calling the generated copy kernel. |
| [Backend work](backend/README.md) | Pinned CakeML/HOL source, a curated datacake patch, the proof rebuild and the compiler bootstrap, scripted. |
| [Migration sources](migration/dataplane/README.md) | The original native host, preserved byte for byte as reference ([porting risks](docs/porting-risks.md)). |
| [News](lean/DN/News) | Framers ([details](docs/baseline.md#framers)), the session's specification ([details](docs/baseline.md#session-model)) and program, the NNTP server ([details](docs/baseline.md#nntp-server)), and the article store specified and proven in the model ([decision 0005](docs/decisions/0005-article-store.md)), its CRC-32C and SipHash-2-4 proven, its scanner and recovery tested and recovery run at start. |

`scripts/Audit.lean`, `leanchecker` and nanoda re-check every declaration of `lean/DN` against the allowed axioms after a source gate; this is about the proofs' soundness, not the specifications' strength ([assurance](docs/assurance.md), [Pancake semantics](docs/pancake-semantics.md)). The gate is a tripwire, not a sandbox: check untrusted changes in isolation, without secrets.

## Build and check

Install Git, Python 3.12, [elan](https://github.com/leanprover/elan), [rustup](https://rustup.rs/) and a C toolchain; the checks run on Linux x86-64 and fetch their pinned tools on first use (elsewhere, `bash scripts/check.sh build`).

```sh
git clone https://github.com/emberian/dragons-net.git dn
cd dn
bash scripts/lint.sh
bash scripts/check.sh
bash scripts/check_all.sh
```

`lint.sh` runs the static checks, `check.sh` the source gate, build, proofs, audit and the model checks (stages `build`, `proofs`, `tests`), and `check_all.sh` adds the native lanes of `scripts/native_lanes.sh` ([baseline](docs/baseline.md#reproduce-the-baseline)); a check that passed on the same inputs is not run again.

`dn-compiler` prints the native examples, fixtures and programs the lanes compile, for instance `.lake/build/bin/dn-compiler emit-region > build/region.pnk`.

[CI](.github/workflows/ci.yml) runs lint, a build without network, the proofs on a fresh machine and the tests and native lanes; [`verify`](.github/workflows/verify.yml) reports from the default branch whether a run's checks are the project's; [backend](.github/workflows/backend.yml) rebuilds the patched proof; [nightly](.github/workflows/scheduled.yml) runs the slow and networked checks.

## Pick up the work

The [roadmap](https://github.com/emberian/dragons-net/issues/28), the [backlog guide](docs/project.md), [CONTRIBUTING](CONTRIBUTING.md), the [handoff](docs/handoff.md), [architecture](docs/architecture.md), the [NNTP plan](docs/nntp.md) and the [decisions](docs/decisions/) say where to start.

## Provenance and license

Project code is AGPL-3.0-or-later ([LICENSE](LICENSE), [NOTICE](NOTICE)); the CakeML patch keeps its BSD license and RFC texts their notices, and [the extraction manifest](docs/provenance.json) records every inherited file's source and hash.
