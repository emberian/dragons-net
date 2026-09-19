# Contributing to dn

Start with the [project backlog](docs/project.md), [handoff](docs/handoff.md),
[review findings](docs/reviews/README.md), and [assurance boundaries](docs/assurance.md).
The working baseline is a compiler and generated-code TCP echo service. NNTP,
optimized OS adapters, and end-to-end verification are work in progress.

## Choose and scope work

Pick a `status:ready` issue and comment that you intend to work on it. Issues are
unassigned until someone takes responsibility; priority is not ownership. Check
for an existing issue before opening another. Use the work-item form for a new
feature, proof, integration task, or investigation and the bug form for a
reproducible defect. Link the roadmap and related issues.

Keep each issue's acceptance criteria and dependencies current. `status:blocked`
means hard prerequisites remain open. `status:backlog` means intentionally
deferred, even if exploratory work is possible. When a prerequisite closes,
review the dependent issue before changing its status; this is a maintainer
workflow, not automated label management. An implementation PR can explore a
blocked task, but should not claim acceptance before its required contracts exist.

`priority:p1` identifies the next foundations or migration gates, `p2` their
follow-on work, and `p3` deferred expansion. `risk:migration` identifies risks in
inactive inherited sources; it does not describe a reproduced defect in the
running echo service. Milestones are parallel work streams with no assigned dates.

Split discoveries that materially expand scope into linked work items. Do not
close a partially completed issue by silently dropping acceptance criteria.
For design tasks, link the decision and bounded follow-ups; for implementation
tasks, link the code and evidence. Record explicit replacements or deferrals.

## Develop and validate

Use a branch and a focused PR. Follow [AGENTS.md](AGENTS.md)'s build and assurance
rules; they also describe the expectations for human contributions. Do not edit
the frozen migration source or require access to sibling repositories.

Run `bash scripts/lint.sh` and `bash scripts/check.sh` for active code changes. Never run concurrent Lake
builds in one checkout. Use `python3 scripts/check_models.py --loom` when changing
concurrency models, and the [native baseline](docs/baseline.md) on Linux x86-64
when changing emitted code, compiler/FFI boundaries or the host. Backend proof
changes use the separate [HOL lane](backend/README.md). State which checks ran,
which did not, and why. For documentation-only changes, check links and diffs;
do not invent test results.

Every module under `lean/DN` is audited automatically. No `sorry`, custom axioms,
`native_decide`, or weakened claims to make a gate pass. A theorem with an
impossible premise is not useful assurance: provide witnesses and review what
the precondition actually means. Distinguish kernel proofs, bounded exploration,
model execution, native tests, and benchmarks. Use independent comparisons and
negative controls where they exercise a real boundary.

## Submit and close

Reference the issue in the PR and explain the observable change, validation and
remaining limitations. Use `Closes #...` only when the acceptance criteria are
met. Preserve attribution and source hashes, update capability/assurance claims,
and attach the relevant CI evidence. Performance claims need comparable workload
and environment data, not only a digest microbenchmark.

On completion, update the roadmap and inspect dependent issues. CI protects the
tested baseline; it does not discharge the open ownership or compiler proof
obligations recorded in the backlog.
