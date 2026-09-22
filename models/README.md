# Concurrency models

These eight crates were extracted from the orb concurrency twins and renamed. They are an independent Cargo workspace, so an ordinary build of the runtime library does not pull in loom.

| Model | Concern |
| --- | --- |
| `ring` | Publication and reclamation across producer/consumer ownership |
| `wake` | Wakeup coordination and lost-wakeup counterexamples |
| `borrow-recycle` | Recycling only after the borrowing worker signals completion |
| `splitsend` | Split completion and buffer lifetime |
| `multishot` | Multiple receive completions and termination |
| `conn-limit` | Concurrent connection admission |
| `config-publish` | Whole-generation publication versus torn reads |
| `oneshot-recv` | Ownership around one-shot receives |

The `dn-runtime` crate has its own loom tests (`crates/dn-runtime/tests/loom.rs`). They are the only ones that drive shipped code: the atomics inside `ConnectionLimit` are the instrumented ones under `cfg(loom)`, so what is explored is the gate the host links, not a transcription of it. The models below describe the historical reactor in `migration/`, which nothing in this repository builds.

Run `python3 scripts/check_models.py` for ordinary tests or add `--loom` for interleaving exploration. The runner compares the discovered tests against `models/expected-tests.txt` and refuses any difference, so a crate dropped from the workspace or a `cfg` that stops matching fails the lane instead of quietly shrinking it. Some tests deliberately find a counterexample to a broken variant; that expected discovery is success. `python3 scripts/mutate_rust.py` replays a recorded set of defects — a publication not ordered against the close, a dropped coalescing condition, a take that is not atomic, a bound checked after the increment — against a copy of the tree and requires the tests to go red on each; the scheduled workflow runs it.

The runner sets no preemption bound. A test that calls `loom::model` therefore explores every interleaving; the few models that would not converge that way set a bound of 3 themselves and say so at the call site. Bounded exploration is not a proof either way: loom checks the C11 model it implements, treats `SeqCst` accesses as `AcqRel` (which can flag correct code), and does not model load buffering (which can miss a real bug). The models do not execute io_uring or kqueue and do not prove the preserved host code implements these algorithms.
