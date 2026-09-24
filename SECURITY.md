# Security

This is research code: a compiler and dataplane under construction, with proofs about models
rather than about running systems. Nothing here is deployed, and the theorems that exist do not
cover the C host, the build system or this repository's own scripts. Treat a green check as
evidence about the models and the checks, not as a safety claim about a program you can run.

## Reporting

If private reporting is enabled on this repository, use it: Security → Report a vulnerability.
Otherwise open an issue that describes the impact and how to reach you, without a working
exploit, and ask for a private channel.

There is no bounty.

## What is in scope

* The C host and the code generated into it (`native/`), the Rust primitives (`crates/`), the
  models (`models/`), the Lean library (`lean/`).
* The build and check machinery: `scripts/`, the workflows in `.github/`, the pinned tool
  manifests (`tools.lock.json`, `backend/lock.json`) and the extraction manifest
  (`docs/provenance.json`). A way to make a check pass on input it should refuse is a
  vulnerability here, and the most valuable kind.

## What is not

* `migration/` is a preserved snapshot of earlier work, kept unchanged for extraction. It is not
  built, not run and not maintained; its defects are recorded in `docs/porting-risks.md` instead.
  Reports about it are welcome as issues, not as advisories.
* The documents under `rfcs/` are copies of published standards.
