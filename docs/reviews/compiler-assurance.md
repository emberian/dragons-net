# Compiler assurance review

Review findings describe the inspected baseline. See [triage and current disposition](README.md) for fixes applied during this review and unresolved obligations.

Scope: `Semantics`, `Region`, `Compose`, `Clock`, `Certificate`, `ProofProducing`, `LowerBridgeSem`, and `ByteCopy`, compared where relevant with the pinned CakeML `panSemScript.sml`. No source or build changes were made.

## High — data-dependent `ProofProducing` certificates have impossible premises

**Locations:** `lean/DN/Compiler/Compose.lean:26-27`, `lean/DN/Compiler/ProofProducing.lean:239-256`, `lean/DN/Compiler/ProofProducing.lean:503-528`, `lean/DN/Compiler/ProofProducing.lean:544-557`; the same defect appears in the supposedly non-vacuous demo at `lean/DN/Compiler/Compose.lean:227-242`.

`Refines` quantifies over every `PancakeState`. Consequently the hypotheses used to make a local read or store total also quantify over every state:

* `hcode : ∀ s, s.locals "code" = some (codeVal s)`;
* `hbuf : ∀ s, s.locals "buf" = some (bufVal s)`;
* `hregion : ∀ s k, ..., s.memaddrs (...) = true`;
* `hslot` and `hin` in `demoServe_emit_correct` have the same shape.

Each is contradictory. Instantiate a local hypothesis with a state whose `locals := fun _ => none`; its conclusion is `none = some _`. Instantiate a memory-domain hypothesis with `memaddrs := fun _ => false`; its conclusion is `false = true`. Thus `redirectStatusStage_cert`, `httpStamp_cert`, `crlfStamp_cert`, their translated subtypes, and `demoServe_emit_correct` have no caller. This is more severe than merely lacking a whole-compiler theorem: the named model-level results described as a “real stage”, “certificate”, or “non-vacuous” cannot be applied.

This minimal contradiction was checked by Lean 4 with `lake env lean /tmp/DNCompilerAssuranceContradiction.lean` (exit 0):

```lean
import DN.Compiler.ProofProducing
open DN.Compiler

theorem hbuf_premise_is_false (bufVal : PancakeState Unit → Word)
    (hbuf : ∀ s : PancakeState Unit, s.locals "buf" = some (bufVal s)) : False := by
  let s : PancakeState Unit :=
    { locals := fun _ => none, memory := fun _ => 0,
      memaddrs := fun _ => false, be := false, clock := 0,
      ffi := (), baseAddr := 0 }
  have h := hbuf s
  simp [s] at h
```

`Certificate` does not repair these results. Its inhabited-precondition field exists at `Certificate.lean:10-14`, but the affected functions return `Refines` proofs or subtypes over `Refines`, not `Certificate`. By contrast, `increment` at `Certificate.lean:23-32` uses the sound pattern: a state-indexed precondition plus a witness.

Repository reference tracing found no use of these named certificate theorems in `Main.lean`, `Kernels.lean`, or the native scripts. The CLI exposes only `emit-region`, `emit-echo`, and `emit-baseline` (`Main.lean:16-22`). `ProofProducing` is imported by the audit and inherited `ServeFragment`/`ServeSlice`/`ServeFull` modules, so the defect currently affects inherited/research APIs and assurance language, not the maintained native CLI path.

**Immediate containment:** quarantine these APIs as inherited, non-applicable demonstrations; remove “non-vacuous”, “real stage”, and “certificate” language from their documentation, and add a gate theorem/test recording that the old premises imply `False`. Do not use them as evidence for the active compiler path.

**Repair path:** parameterize the loop-free stage judgment by a precondition, or express it with `RefinesClk` (whose state-indexed premise is already defined at `Clock.lean:26-28`). Make primitive obligations `∀ s, P s → ...`, propagate pre/postconditions through sequence and conditionals, and return `Certificate` with an explicit witness. This is a broader API repair and need not block the bounded quarantine.

**Regression:** add Lean theorems that derive `False` from each old premise, then replace the premises and exhibit concrete states with bound `code`/`buf` and a finite addressable region. Exercise each corrected certificate on those states and assert the result local, changed bytes, and preservation of unrelated locals/memory.

## High — `serve_head_landsB` is mislabeled as a printed-source end-to-end theorem

**Location:** `lean/DN/Compiler/LowerBridgeSem.lean:396-413`.

The comment says the theorem proves “the printed `.pnk` response head is correct from emitted-syntax to landed-bytes.” Its conclusion only states that the internal function `lowerStmtsFold (storesInto dst bs)` produces an internal `PancakeProg`, then runs that program in the Lean transcription. It mentions neither the pretty-printer output nor the CakeML parser. This directly crosses the source-representation boundary that `docs/assurance.md` correctly lists as open.

The result is useful as an AST-to-model theorem, but it is not evidence about printed bytes accepted by the real parser. A printer escaping, precedence, tokenization, or parser conversion error can invalidate the advertised conclusion while this theorem remains true.

**Fix:** rename/reword the claim as internal lowering/model correctness. Reserve “printed `.pnk`” and “end-to-end” for a theorem or independently checked bridge connecting `pp*` output, the pinned parser's accepted AST, and this `PancakeProg`.

**Regression/proof obligation:** for arbitrary supported `storesInto`, establish `parse (print stmts) = stmts` (or a precise corresponding parser AST) and then prove the parser conversion equals `lowerStmtsFold`. Until HOL extraction is available, a differential parser test with minimized counterexamples is evidence, not a proof, and should be labeled that way.

## Medium — the FFI model permits writeback beyond the declared array

**Locations:** `lean/DN/Compiler/Semantics.lean:81-90`, `lean/DN/Compiler/Semantics.lean:351-364`; inherited behavior in `.deps/cakeml/pancake/semantics/panSemScript.sml:714-724`.

`FFIResult.ret` contains an unconstrained `newBytes : List (BitVec 8)`. `ExtCall` reads exactly `arrLen` bytes but writes all returned bytes starting at `arrPtr`; it never requires `newBytes.length = arrLen` (or even `≤ arrLen`). A legal Lean `Oracle` can therefore return `arrLen + 1` bytes and mutate the next address, or wrap around the 64-bit address space. The Lean code is faithful to the raw HOL evaluation clause, which also passes `new_bytes` straight to `write_bytearray`; the missing item is the FFI invariant that makes this safe/useful, not a mismatch in this clause.

Calling `Oracle` an “explicit trusted assumption” does not state the required assumption. Any future `ExtCall` frame theorem can be false unless it carries a length/address contract. This also matters for preservation claims: FFI return preserves locals but does not confine memory effects to the caller-declared array under the current type.

**Fix:** introduce a contracted oracle result carrying a proof that returned length equals the input array length (matching the backend FFI invariant), or add that property as an explicit premise to every theorem about `ExtCall`. Add non-wrapping/addressability premises for every byte written. Document the exact HOL invariant being transcribed rather than treating arbitrary `Oracle.call` as the trusted boundary.

**Regression:** define an adversarial oracle returning one extra byte and show today that the extra byte changes when addressable. The corrected semantics/contract should reject that result or make the overlong branch unrepresentable. Also test zero length and pointer wraparound.

## Medium — the strongest byte-copy theorem omits caller-visible state behavior

**Location:** `lean/DN/Compiler/ByteCopy.lean:228-244` (implementation setup at `:245-261`).

`copySeg_landsB` proves destination contents, a byte-level memory frame, and preservation of `memaddrs`/endianness. The program also overwrites locals `dst`, `src`, `i`, and `len`; these are ordinary assignments, not lexical `Dec` bindings. The theorem neither exposes this clobber set nor proves preservation of all other locals. It also omits `ffi`, `baseAddr`, the exact consumed clock, and an explicit normal-result fact beyond the execution equality. The implementation does preserve `ffi`/`baseAddr`, preserves unrelated locals, leaves the four scratch locals bound, and consumes one clock per copied byte; those facts are recoverable but are absent from the public contract.

This makes safe composition needlessly weak and creates a practical collision risk: a caller using any scratch name loses its value even though the theorem's prose reads like a reusable body copy. The memory frame is also phrased through `memLoadByte`; a word-level frame (`s'.memory w = s.memory w` outside destination-aligned words) would make downstream whole-word preservation obligations much easier to discharge.

**Fix:** either scope scratch locals with `Dec` and prove restoration, or state the clobber set explicitly. Strengthen the postcondition with unrelated-local preservation, `ffi` and `baseAddr` preservation, exact/founded clock consumption, and a word-level memory frame outside `{ byteAlign (dst+i) }`. A result-slot wrapper should specify its return/result behavior separately.

**Regression:** start with sentinel values in all four scratch locals plus one unrelated local, run lengths 0 and 1, and assert the chosen contract. Add a same-word test showing only the selected destination byte changes and a cross-word test showing all other words are identical.

## Low — inherited HOL fidelity is asserted by comments, not checked at the boundary

**Locations:** `lean/DN/Compiler/Semantics.lean:17-53`, `:108-152`, `:273-326`; CakeML references include `.deps/cakeml/pancake/semantics/panSemScript.sml:583-603`, `:615-643`, and `:714-724`.

The reviewed clauses agree structurally with the pinned HOL source: `StoreByte` truncates to a byte; `Seq` and `While` apply `fix_clock`; timeout/return clear locals; `ExtCall` reads `(pointer,length)` pairs and performs right-fold writeback. This manual agreement is useful but remains fragile because no executable cross-semantics test targets failure-state fields. Existing positive theorems emphasize successful runs.

**Prioritized obligation:** add a small generated differential corpus over model states and this fragment, including missing locals, invalid memory, timeout, return, FFI-final, and partial FFI writeback. Compare result constructor, locals, memory, FFI state, base address, and clock—not only the computed word. Preserve minimized mismatches. This is the narrowest practical guard against transcription drift before attempting a general HOL correspondence theorem.
