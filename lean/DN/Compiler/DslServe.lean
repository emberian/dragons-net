-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.DslServe

Retained compiler/dataplane development and regression examples.
Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md. HTTP examples are compiler workloads, not dn server features.
-/

import DN.Compiler.ServeSlice

namespace DN.Compiler.DslServe

open DN.Compiler DN.Compiler.SerializeCompile DN.Compiler.ServeSlice

/-! ## 1. The serve context and the leaf grammars -/

/-- The routing-relevant request facts the stages gate / branch on. The deployed
serve's context carries the raw input, dispatched request, and an attribute bag;
here the two facts this serve slice routes off: the decoded method tag
(GET/POST/HEAD/OPTIONS pre-decoded to `{0,1,2,3}`) and the declared body length (the
body-size gate's input). -/
structure Ctx where
  method  : Word
  bodyLen : Nat

/-- Request predicates — the guards a `gate` / `condR` branches on. -/
inductive ReqPred where
  /-- The real METHOD FILTER refusal: the method tag is NOT one of the allowed
  `{0,1,2,3}` (`¬ method < 4`) → refuse `405`. -/
  | methodDisallowed
  /-- The body-size limit: the declared body exceeds `limit` → gate `413`. -/
  | bodyOver (limit : Nat)
  /-- Unconditional. -/
  | always
  deriving Repr

/-- Evaluate a predicate against the context (signed method compare = the deployed
`signedLt` the method filter uses). -/
def ReqPred.eval : ReqPred → Ctx → Bool
  | .methodDisallowed, c => ! signedLt c.method 4
  | .bodyOver limit,   c => decide (limit < c.bodyLen)
  | .always,           _ => true

/-- Bounded body transforms — the `rewriteBody` payload. `appendConst` (append a
statically-known byte string) is the deployed `ResponseBuilder.appendBody`. -/
inductive BodyLoop where
  | appendConst (suffix : Bytes)
  deriving Repr

/-- Run a body transform. -/
def BodyLoop.apply : BodyLoop → Bytes → Bytes
  | .appendConst s, b => b ++ s

/-- The transform's (statically-known, bounded) length effect — what the emitted
program adds to its in-memory `Content-Length` counter. -/
def BodyLoop.deltaLen : BodyLoop → Nat
  | .appendConst s => s.length

/-- The transform grows the body by EXACTLY its declared delta — the fact that lets
the incrementally-maintained `Content-Length` match the from-scratch body length. -/
theorem BodyLoop.apply_length (t : BodyLoop) (b : Bytes) :
    (t.apply b).length = b.length + t.deltaLen := by
  cases t with
  | appendConst s => simp [BodyLoop.apply, BodyLoop.deltaLen]

/-! ## 2. THE SHARED DSL — the deep embedding of the serve middleware stages -/

/-- `StageProg` — the ONE algebra every lane compiles. `denote` (deployed serve)
and `compile` (translator) are the two interpretations over this single syntax. -/
inductive StageProg where
  /-- Append a response header (deployed `ResponseBuilder.addHeader`). -/
  | addHeader (name val : Bytes)
  /-- Set the response status line (deployed `setStatus` ∘ `setReason`). -/
  | setStatus (code : Nat) (reason : Bytes)
  /-- Short-circuit with a status when the request predicate holds (a `.respond`
  gate); a canned reason phrase is derived from the code. -/
  | gate (c : ReqPred) (code : Nat)
  /-- Bounded body transform (deployed `ResponseBuilder.appendBody`). -/
  | rewriteBody (t : BodyLoop)
  /-- Sequential composition (the middleware onion, in request order). -/
  | seq (a b : StageProg)
  /-- Branch on the request. -/
  | condR (c : ReqPred) (a b : StageProg)
  deriving Repr

/-- Canned reason phrase for a gate status code (the deployed refusal reasons). -/
def reasonOf (code : Nat) : Bytes :=
  if code = 405 then sb "Method Not Allowed"
  else if code = 413 then sb "Payload Too Large"
  else if code = 200 then sb "OK"
  else sb ""

/-! ## 3. Interpretation (i): `denote` — the DEPLOYED serve semantics -/

/-- The reference serve state threaded left-to-right: the accumulating `Response`
plus whether a gate has already fired (`gated` — later gates / status stores are
suppressed to keep the gate's status, but header / body transforms still apply, as
the deployed onion runs the inner response transforms over a short-circuit). -/
structure DState where
  resp  : Response
  gated : Bool

/-- One denotation step — each constructor's effect is the deployed pipeline's own
`ResponseBuilder` op (see `denote_*_faithful`). -/
def denoteStep (c : Ctx) : DState → StageProg → DState
  | st, .addHeader n v =>
      { st with resp := { st.resp with headers := st.resp.headers ++ [(n, v)] } }
  | st, .setStatus code reason =>
      if st.gated then st
      else { st with resp := { st.resp with status := code, reason := reason } }
  | st, .gate p code =>
      if st.gated then st
      else if p.eval c then
        { resp := { st.resp with status := code, reason := reasonOf code }, gated := true }
      else st
  | st, .rewriteBody t =>
      { st with resp := { st.resp with body := t.apply st.resp.body } }
  | st, .seq a b => denoteStep c (denoteStep c st a) b
  | st, .condR p a b => if p.eval c then denoteStep c st a else denoteStep c st b

/-- The deployed serve semantics of a stage program over a base (handler) response. -/
def denote (p : StageProg) (base : Response) (c : Ctx) : Response :=
  (denoteStep c { resp := base, gated := false } p).resp

/-! ### Per-op faithfulness to the deployed serve's `ResponseBuilder`

Each RHS below is EXACTLY the deployed `build_*` refinement lemma's RHS — so the
DSL's per-stage effect is the deployed pipeline's per-stage effect. -/

/-- `addHeader` = deployed `build_addHeader`. -/
theorem denote_addHeader_faithful (c : Ctx) (r : Response) (n v : Bytes) :
    (denoteStep c ⟨r, false⟩ (.addHeader n v)).resp
      = { r with headers := r.headers ++ [(n, v)] } := rfl

/-- `setStatus` (ungated) = deployed `build_setStatus` ∘ `build_setReason`. -/
theorem denote_setStatus_faithful (c : Ctx) (r : Response) (code : Nat) (reason : Bytes) :
    (denoteStep c ⟨r, false⟩ (.setStatus code reason)).resp
      = { r with status := code, reason := reason } := rfl

/-- `rewriteBody (appendConst s)` = deployed `build_appendBody`. -/
theorem denote_rewriteBody_faithful (c : Ctx) (r : Response) (s : Bytes) :
    (denoteStep c ⟨r, false⟩ (.rewriteBody (.appendConst s))).resp
      = { r with body := r.body ++ s } := rfl

/-! ## 4. Interpretation (ii): `compile` — the TRANSLATOR lowering -/

/-- The translator serve state: the wire record built INCREMENTALLY (the
`Content-Length` counter maintained as the body grows) plus the gate flag. -/
structure CState where
  wire  : Wire
  gated : Bool

/-- One compilation step — mirrors `denoteStep` but on the wire record, keeping the
`Content-Length` counter incrementally (the emitted program adds `t.deltaLen` to its
counter, it does not recompute `body.length`). -/
def compileStep (c : Ctx) : CState → StageProg → CState
  | st, .addHeader n v =>
      { st with wire := { st.wire with headers := st.wire.headers ++ [(n, v)] } }
  | st, .setStatus code reason =>
      if st.gated then st
      else { st with wire := { st.wire with status := code, reason := reason } }
  | st, .gate p code =>
      if st.gated then st
      else if p.eval c then
        { wire := { st.wire with status := code, reason := reasonOf code }, gated := true }
      else st
  | st, .rewriteBody t =>
      { st with wire := { st.wire with body := t.apply st.wire.body, contentLength := st.wire.contentLength + t.deltaLen } }
  | st, .seq a b => compileStep c (compileStep c st a) b
  | st, .condR p a b => if p.eval c then compileStep c st a else compileStep c st b

/-- The wire record the translator lowering builds for a stage program. -/
def compileWire (p : StageProg) (base : Response) (c : Ctx) : Wire :=
  (compileStep c { wire := build base, gated := false } p).wire

/-- The compiled serve output bytes: the translator serializer over the
incrementally-built wire. -/
def compile (p : StageProg) (base : Response) (c : Ctx) : Bytes :=
  serializeWire (compileWire p base c)

/-! ## 5. THE KEYSTONE — the compiler is correct for ALL stage programs

The translator's incremental wire (`compileStep`) is exactly the wire the deployed
serve's from-scratch `build` pins (`denoteStep`): the `Content-Length` counter
maintained by `+= deltaLen` equals the final `body.length`. ONE induction over the
algebra. -/

/-- The reference→translator state map: the incremental wire is `build` of the
reference response, the gate flags agree. -/
def dToC (dst : DState) : CState := { wire := build dst.resp, gated := dst.gated }

/-- The step invariant: the translator's incremental step commutes with the
reference step through `dToC` — an incremental wire that is `build` of the current
response STAYS `build` of the current response after the step (the `Content-Length`
counter maintained by `+= deltaLen` tracks the body length). ONE induction over the
algebra covers every constructor. -/
theorem compileStep_dToC (c : Ctx) (p : StageProg) :
    ∀ dst : DState, compileStep c (dToC dst) p = dToC (denoteStep c dst p) := by
  induction p with
  | addHeader n v =>
      intro dst; simp [compileStep, denoteStep, dToC, build]
  | setStatus code reason =>
      intro dst; cases hg : dst.gated <;>
        simp [compileStep, denoteStep, dToC, build, hg]
  | gate p code =>
      intro dst
      cases hg : dst.gated
      · cases hp : p.eval c <;> simp [compileStep, denoteStep, dToC, build, hg, hp]
      · simp [compileStep, denoteStep, dToC, build, hg]
  | rewriteBody t =>
      intro dst; simp [compileStep, denoteStep, dToC, build, BodyLoop.apply_length]
  | seq a b iha ihb =>
      intro dst
      show compileStep c (compileStep c (dToC dst) a) b = dToC (denoteStep c (denoteStep c dst a) b)
      rw [iha dst]; exact ihb _
  | condR p a b iha ihb =>
      intro dst
      show (if p.eval c then compileStep c (dToC dst) a else compileStep c (dToC dst) b)
          = dToC (if p.eval c then denoteStep c dst a else denoteStep c dst b)
      cases hp : p.eval c <;> simp [iha, ihb]

/-- **`stageprog_compile_correct` — the keystone.** For every stage program, base
response, and context: the compiled serve bytes equal the serialization of the
deployed serve's response. ONE proof, all stages. -/
theorem stageprog_compile_correct (p : StageProg) (base : Response) (c : Ctx) :
    compile p base c = serialize (denote p base c) := by
  have hw : (compileStep c { wire := build base, gated := false } p).wire
      = build (denoteStep c { resp := base, gated := false } p).resp := by
    rw [show ({ wire := build base, gated := false } : CState)
          = dToC { resp := base, gated := false } from rfl, compileStep_dToC]
    rfl
  simp only [compile, compileWire, denote, serialize]
  rw [hw]

/-! ## 6. THE SERVE — a real serve slice as ONE `StageProg` term -/

/-- The empty handler base the stages build the response from (status 0, no headers,
empty body). -/
def emptyBase : Response := { status := 0, reason := [], headers := [], body := [] }

/-- Append a list of headers as a right-nested `seq` of `addHeader`s. -/
def seqAddHeaders : List (Bytes × Bytes) → StageProg
  | []          => .rewriteBody (.appendConst ([] : Bytes))
  | [nv]        => .addHeader nv.1 nv.2
  | nv :: rest  => .seq (.addHeader nv.1 nv.2) (seqAddHeaders rest)

/-- The `200 OK` route: the deployed security headers, a `200 OK` status, the body. -/
def okStage : StageProg :=
  .seq (seqAddHeaders secHeaders)
    (.seq (.setStatus 200 (sb "OK"))
      (.rewriteBody (.appendConst (sb "hello\n"))))

/-- The `405 Method Not Allowed` route: the RFC-9110 §10.2.1 `Allow` header, the
security headers, a `405` status, the body. -/
def refuseStage : StageProg :=
  .seq (.addHeader (sb "Allow") (sb "GET, POST, HEAD, OPTIONS"))
    (.seq (seqAddHeaders secHeaders)
      (.seq (.setStatus 405 (sb "Method Not Allowed"))
        (.rewriteBody (.appendConst (sb "method not allowed\n")))))

/-- **The serve.** A body-size `gate` (413), then the method-filter `condR` routing
to the `200`/`405` responses. 6 stage constructors composed. -/
def serveProg : StageProg :=
  .seq (.gate (.bodyOver 1000000) 413)
    (.condR .methodDisallowed refuseStage okStage)

/-! ## 7. VERIFICATION — the compiled serve = the leanc serve on a request corpus

The corpus: three allowed methods (GET/POST/OPTIONS = 0/1/3), two refused
(5/9), and one oversized body (the 413 gate). For each, the compiled serve bytes
equal the leanc-faithful reference serialization of the deployed response
(`refSerialize (denote …)`), kernel-evaluated. -/

/-! GET (allowed) → `resp200`; a refused method (9) → `resp405`: `denote serveProg`
reproduces the deployed method-filter routing `miniServe` (compared on the wire
bytes — the serve's observable). -/
def regression_345 : Bool := decide (serialize (denote serveProg emptyBase ⟨(0 : Word), 0⟩) = serialize resp200
  )
def regression_346 : Bool := decide (serialize (denote serveProg emptyBase ⟨(1 : Word), 0⟩) = serialize resp200
  )
def regression_347 : Bool := decide (serialize (denote serveProg emptyBase ⟨(3 : Word), 0⟩) = serialize resp200
  )
def regression_348 : Bool := decide (serialize (denote serveProg emptyBase ⟨(5 : Word), 0⟩) = serialize resp405
  )
def regression_349 : Bool := decide (serialize (denote serveProg emptyBase ⟨(9 : Word), 0⟩) = serialize resp405
  )

-- routing = the deployed `miniServe` (allowed → 200, refused → 405)
def regression_352 : Bool := decide (serialize (denote serveProg emptyBase ⟨(0 : Word), 0⟩) = serialize (miniServe 0)
  )
def regression_353 : Bool := decide (serialize (denote serveProg emptyBase ⟨(9 : Word), 0⟩) = serialize (miniServe 9)
  )

-- the 413 body-size gate fires on an oversized request (status 413, distinct bytes)
def regression_356 : Bool := decide ((denote serveProg emptyBase ⟨(0 : Word), 2000000⟩).status = 413
  )

/-! **The byte-identity differential.** For every request in the corpus, the
DSL-compiled serve output bytes equal the leanc-faithful reference serve output
bytes. -/
def regression_361 : Bool := decide (compile serveProg emptyBase ⟨(0 : Word), 0⟩ = refSerialize (denote serveProg emptyBase ⟨(0 : Word), 0⟩)
  )
def regression_362 : Bool := decide (compile serveProg emptyBase ⟨(1 : Word), 0⟩ = refSerialize (denote serveProg emptyBase ⟨(1 : Word), 0⟩)
  )
def regression_363 : Bool := decide (compile serveProg emptyBase ⟨(3 : Word), 0⟩ = refSerialize (denote serveProg emptyBase ⟨(3 : Word), 0⟩)
  )
def regression_364 : Bool := decide (compile serveProg emptyBase ⟨(5 : Word), 0⟩ = refSerialize (denote serveProg emptyBase ⟨(5 : Word), 0⟩)
  )
def regression_365 : Bool := decide (compile serveProg emptyBase ⟨(9 : Word), 0⟩ = refSerialize (denote serveProg emptyBase ⟨(9 : Word), 0⟩)
  )
def regression_366 : Bool := decide (compile serveProg emptyBase ⟨(0 : Word), 2000000⟩ = refSerialize (denote serveProg emptyBase ⟨(0 : Word), 2000000⟩)
  )

-- compiled = the leanc bytes of the ROUTED response (200 vs 405), byte for byte
def regression_369 : Bool := decide (compile serveProg emptyBase ⟨(0 : Word), 0⟩ = refSerialize resp200
  )
def regression_370 : Bool := decide (compile serveProg emptyBase ⟨(9 : Word), 0⟩ = refSerialize resp405
  )

-- routing non-vacuity: allowed and refused compile to DISTINCT bytes
def regression_373 : Bool := decide (compile serveProg emptyBase ⟨(0 : Word), 0⟩ ≠ compile serveProg emptyBase ⟨(9 : Word), 0⟩
  )

/-! ## 8. Machine-code / A1 tie — the compiled serve's bytes are what the emitted
DN.Compiler program writes to memory.

`DN.Compiler.ServeSlice.serveSlice_correct` proves the emitted program `serveSliceProg`
runs to a state whose output region holds `serialize (if signedLt tag 4 then resp200
else resp405)`, byte for byte. The theorems below show that byte string is EXACTLY
`compile serveProg emptyBase` on the corresponding request — so the DSL-compiled
serve is the machine-written (A1-validated) serve. -/

/-- The compiled GET serve is the exact byte string `serveSlice_correct` writes for
an allowed method (`serialize resp200`). -/
theorem serveProg_get_eq_machine :
    compile serveProg emptyBase ⟨(0 : Word), 0⟩ = serialize resp200 := by
  have hd : denote serveProg emptyBase ⟨(0 : Word), 0⟩ = resp200 := rfl
  rw [stageprog_compile_correct, hd]

/-- The compiled refused serve is the exact byte string `serveSlice_correct` writes
for a disallowed method (`serialize resp405`). -/
theorem serveProg_refuse_eq_machine :
    compile serveProg emptyBase ⟨(9 : Word), 0⟩ = serialize resp405 := by
  have hd : denote serveProg emptyBase ⟨(9 : Word), 0⟩ = resp405 := rfl
  rw [stageprog_compile_correct, hd]

/-- The routed byte string, tying the compiled serve to the machine cert's
postcondition `serialize (if signedLt tag 4 then resp200 else resp405)` for the two
corpus tags. -/
theorem serveProg_eq_serveSlice_postcondition :
    compile serveProg emptyBase ⟨(0 : Word), 0⟩
        = serialize (if signedLt (0 : Word) 4 then resp200 else resp405)
    ∧ compile serveProg emptyBase ⟨(9 : Word), 0⟩
        = serialize (if signedLt (9 : Word) 4 then resp200 else resp405) := by
  refine ⟨?_, ?_⟩
  · show compile serveProg emptyBase ⟨(0 : Word), 0⟩ = serialize resp200
    exact serveProg_get_eq_machine
  · show compile serveProg emptyBase ⟨(9 : Word), 0⟩ = serialize resp405
    exact serveProg_refuse_eq_machine

end DN.Compiler.DslServe
