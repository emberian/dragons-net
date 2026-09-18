# Concurrency models

These eight crates were extracted from the orb concurrency twins and renamed. They are an independent Cargo workspace, so the small active runtime library does not depend on Loom.

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

Run `python3 scripts/check_models.py` for ordinary tests or add `--loom` for interleaving exploration. The latter enables `cfg(loom)`, discovers tests before running them, and rejects a near-empty suite. Currently it discovers 25 tests. Some tests deliberately find a counterexample to a broken variant; that expected discovery is success.

The default preemption bound is 2; individual ring/wake tests set 3. This is bounded exploration, with no permutation-count truncation configured by the runner. The models do not execute io_uring or kqueue and do not prove the preserved host code implements these algorithms.
