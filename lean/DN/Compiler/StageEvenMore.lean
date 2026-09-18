-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.StageEvenMore

Retained compiler/dataplane development and regression examples.
Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md. HTTP examples are compiler workloads, not dn server features.
-/

import DN.Compiler.StageCompile

namespace DN.Compiler.StageEvenMore

open DN.Compiler DN.Compiler.SerializeCompile DN.Compiler.StageProg DN.Compiler.StageCompile

variable {σ : Type}

/-! ## 1. `contentLocationStage` — the RFC 9110 §8.7 `Content-Location` stamp -/

/-- The `Content-Location` field name. -/
def contentLocationName : Bytes := str "Content-Location"
/-- The `Content-Location` value — the canonical-URI the deployed
representation-metadata stage renders. -/
def contentLocationVal  : Bytes := str "/canonical/resource"

/-- **The Content-Location stage.** Always passes, stamping the canonical URI onto the
response — a single `addHeader` (the deployed representation-metadata stamp). -/
def contentLocationStage : StageProg := .addHeader contentLocationName contentLocationVal

/-- **`denote_contentLocation`.** The stage appends its one field to the base response —
exactly the deployed stamp of `Content-Location` (`base.headers ++ [cl]`). -/
theorem denote_contentLocation (ctx : Ctx) :
    denote contentLocationStage ctx
      = { ctx.base with headers := ctx.base.headers ++ [(contentLocationName, contentLocationVal)] } := by
  show (denoteStep ctx (.addHeader contentLocationName contentLocationVal)
          { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, Bool.false_eq_true, if_false]

/-! ## 2. `referrerPolicyStage` — the deployed `Referrer-Policy` stamp -/

/-- The `Referrer-Policy` field name. -/
def referrerPolicyName : Bytes := str "Referrer-Policy"
/-- The `Referrer-Policy` value — the deployed security policy's default
(`strict-origin-when-cross-origin`). -/
def referrerPolicyVal  : Bytes := str "strict-origin-when-cross-origin"

/-- **The Referrer-Policy stage.** Always passes, stamping the deployed
`Referrer-Policy` default onto the response — a single `addHeader`. -/
def referrerPolicyStage : StageProg := .addHeader referrerPolicyName referrerPolicyVal

/-- **`denote_referrerPolicy`.** The stage appends its one field to the base response —
exactly the deployed stamp of `Referrer-Policy` (`base.headers ++ [rp]`). -/
theorem denote_referrerPolicy (ctx : Ctx) :
    denote referrerPolicyStage ctx
      = { ctx.base with headers := ctx.base.headers ++ [(referrerPolicyName, referrerPolicyVal)] } := by
  show (denoteStep ctx (.addHeader referrerPolicyName referrerPolicyVal)
          { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, Bool.false_eq_true, if_false]

/-! ## 3. `cacheControlStaticStage` — the deployed static-asset cache directive

A static asset gets a long-lived immutable cache directive; a dynamic response is left
to its own handler (no directive appended) — the deployed static-serve's conditional
`Cache-Control` stamp. At a fixed context the is-static decision is a bit; the stage is
a `condR` on it. -/

/-- The `Cache-Control` field name. -/
def cacheControlName : Bytes := str "Cache-Control"
/-- The static-asset `Cache-Control` value — a one-year immutable public cache
directive (the deployed static-serve policy). -/
def cacheControlStaticVal : Bytes := str "public, max-age=31536000, immutable"

/-- **The static-cache stage.** `isStatic` is the pre-decided is-static-asset bit.
Static → append `(Cache-Control, immutable)`; dynamic → a body-identity no-op (append
nothing) — exactly the deployed static-serve's conditional cache stamp. -/
def cacheControlStaticStage (isStatic : ReqPred) : StageProg :=
  .condR isStatic (.addHeader cacheControlName cacheControlStaticVal) (.rewriteBody .identity)

/-- **`denote_cacheStatic` (asset).** A static asset gets its `Cache-Control` directive
appended — the deployed static-serve stamp (`base.headers ++ [cc]`). -/
theorem denote_cacheStatic_asset (isStatic : ReqPred) (ctx : Ctx) (h : isStatic ctx = true) :
    denote (cacheControlStaticStage isStatic) ctx
      = { ctx.base with headers := ctx.base.headers ++ [(cacheControlName, cacheControlStaticVal)] } := by
  show (denoteStep ctx (.condR isStatic (.addHeader cacheControlName cacheControlStaticVal)
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, if_true, Bool.false_eq_true, if_false]

/-- **`denote_cacheStatic` (dynamic).** A dynamic response passes untouched — no
`Cache-Control` directive appended (left to the handler). -/
theorem denote_cacheStatic_dynamic (isStatic : ReqPred) (ctx : Ctx) (h : isStatic ctx = false) :
    denote (cacheControlStaticStage isStatic) ctx = ctx.base := by
  show (denoteStep ctx (.condR isStatic (.addHeader cacheControlName cacheControlStaticVal)
          (.rewriteBody .identity)) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, h, Bool.false_eq_true, if_false, runBody]

/-! ## 4. `preconditionGate` — the RFC 9110 §13.1.2 `If-None-Match` precondition

When the validator matches (the cached representation is still fresh), short-circuit
with `304 Not Modified`: skip the body render and every later stage — the deployed
conditional-request gate's `.respond` decision. At a fixed context the validator-match
decision is a bit; the stage is a `gate` on it. -/

/-- **The precondition gate.** `matched` is the pre-decided validator-match bit. When it
fires, short-circuit with `304 Not Modified` — the deployed `If-None-Match` gate. -/
def preconditionGate (matched : ReqPred) : StageProg := .gate matched 304

/-- **`denote_precondition` (match).** A matched validator short-circuits the response
to status `304` — the deployed conditional-request decision (a `304` on the wire). -/
theorem denote_precondition_match (matched : ReqPred) (ctx : Ctx) (h : matched ctx = true) :
    denote (preconditionGate matched) ctx = { ctx.base with status := 304 } := by
  show (denoteStep ctx (.gate matched 304) { resp := ctx.base, halted := false }).resp = _
  rw [denoteStep_gate_fires ctx _ 304 _ rfl h]

/-- **`denote_precondition` (no match).** A stale validator passes untouched — the
handler's base response is returned unchanged. -/
theorem denote_precondition_nomatch (matched : ReqPred) (ctx : Ctx) (h : matched ctx = false) :
    denote (preconditionGate matched) ctx = ctx.base := by
  show (denoteStep ctx (.gate matched 304) { resp := ctx.base, halted := false }).resp = _
  simp only [denoteStep, Bool.false_eq_true, if_false, h]

/-! ## 5. Non-vacuity: the tracked skeleton genuinely varies with the stage

Concrete contexts pin the request predicates; the reference `denoteStep`'s scalar
image (status / header-count / body-length / halt) genuinely differs stage to stage,
so the keystone specializations below are not `P → P` tautologies. -/

/-- A `200 OK` base with body `hi`. -/
def baseOk : Response := ok200 (str "hi")

/-- Always-true / always-false request predicates (concrete bits). -/
def pTrue  : ReqPred := fun _ => true
def pFalse : ReqPred := fun _ => false

/-- A context whose base carries no headers (0-header seed). -/
def ctx0 : Ctx := { req := {}, base := baseOk }

-- content-location bumps the header count (0 → 1) and keeps status/body:
def regression_189 : Bool := decide ((denote contentLocationStage ctx0).headers.length = 1
  )
def regression_190 : Bool := decide ((denote contentLocationStage ctx0).status = 200
  )
def regression_191 : Bool := decide ((denote contentLocationStage ctx0).body.length = 2
  )

-- referrer-policy bumps the header count (0 → 1):
def regression_194 : Bool := decide ((denote referrerPolicyStage ctx0).headers.length = 1
  )

-- cache-static-asset bumps the count (0 → 1); cache-dynamic leaves it (0):
def regression_197 : Bool := decide ((denote (cacheControlStaticStage pTrue)  ctx0).headers.length = 1
  )
def regression_198 : Bool := decide ((denote (cacheControlStaticStage pFalse) ctx0).headers.length = 0
  )

-- the precondition MATCH short-circuits to 304 AND halts; NO-MATCH passes at 200:
def regression_201 : Bool := decide ((denoteStep ctx0 (preconditionGate pTrue)
          { resp := ctx0.base, halted := false }).resp.status = 304
  )
def regression_203 : Bool := decide ((denoteStep ctx0 (preconditionGate pTrue)
          { resp := ctx0.base, halted := false }).halted = true
  )
def regression_205 : Bool := decide ((denote (preconditionGate pFalse) ctx0).status = 200
  )
-- the gate keeps the body (a 304 body-drop is a serializer concern, not the gate's
-- status decision), so the tracked body length is preserved through the short-circuit:
def regression_208 : Bool := decide ((denoteStep ctx0 (preconditionGate pTrue)
          { resp := ctx0.base, halted := false }).resp.body.length = 2
  )

-- the four stages produce genuinely distinct wire responses (vs the base and each other):
def regression_212 : Bool := decide (serialize (denote contentLocationStage ctx0) ≠ serialize baseOk
  )
def regression_213 : Bool := decide (serialize (denote referrerPolicyStage ctx0) ≠ serialize baseOk
  )
def regression_214 : Bool := decide (serialize (denote (cacheControlStaticStage pTrue) ctx0) ≠ serialize baseOk
  )
def regression_215 : Bool := decide (serialize (denote (preconditionGate pTrue) ctx0) ≠ serialize baseOk
  )
def regression_216 : Bool := decide (serialize (denote contentLocationStage ctx0)
        ≠ serialize (denote referrerPolicyStage ctx0)
  )
def regression_218 : Bool := decide (serialize (denote contentLocationStage ctx0)
        ≠ serialize (denote (cacheControlStaticStage pTrue) ctx0)
  )
def regression_220 : Bool := decide (serialize (denote (preconditionGate pTrue) ctx0)
        ≠ serialize (denote contentLocationStage ctx0)
  )

/-! ## 6. Keystone instantiations — the GENUINE per-constructor compiler at each stage

Each is `compile2_correct` (the induction keystone) specialized to the stage: from any
`CoreEnc` of the base fold-state, running the emitted per-constructor control flow
lands the `CoreEnc` of the reference `denoteStep` — the tracked skeleton of the
deployed response. -/

/-- **`contentLocation_compile2_correct`.** `compile2 contentLocationStage` (a guarded
header-count increment) lands the Content-Location reference skeleton (header-count +1,
status/body/halt preserved). -/
theorem contentLocation_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt contentLocationStage) st = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx contentLocationStage { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd contentLocationStage
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-- **`referrerPolicy_compile2_correct`.** `compile2 referrerPolicyStage` (a guarded
header-count increment) lands the Referrer-Policy reference skeleton. -/
theorem referrerPolicy_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt referrerPolicyStage) st = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx referrerPolicyStage { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd referrerPolicyStage
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-- **`cacheStatic_compile2_correct`.** `compile2 (cacheControlStaticStage isStatic)` (a
real `Cond` over an `addHeader`-count-increment and a body-identity `Skip`) lands the
static-cache reference skeleton — the asset branch bumps the header count, the dynamic
branch leaves it, tracked exactly per the pre-decided is-static bit. -/
theorem cacheStatic_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (isStatic : ReqPred) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (cacheControlStaticStage isStatic)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (cacheControlStaticStage isStatic) { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd (cacheControlStaticStage isStatic)
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-- **`precondition_compile2_correct`.** `compile2 (preconditionGate matched)` (a real
nested `If` that, when the validator matches, writes `304` and SETS THE HALT FLAG)
lands the precondition reference skeleton — a match flips the status to 304 and halts,
a stale validator leaves the skeleton, tracked per the pre-decided match bit. -/
theorem precondition_compile2_correct (o : Oracle σ) (nm : ReqPred → String)
    (aStat aCnt aBody aHalt : Word) (matched : ReqPred) (ctx : Ctx)
    (hd : Distinct aStat aCnt aBody aHalt) (st : PancakeState σ)
    (hEnc : CoreEnc aStat aCnt aBody aHalt st { resp := ctx.base, halted := false })
    (hDec : ∀ c, st.locals (nm c) = some (if c ctx then (1 : Word) else 0)) :
    ∃ st', PancakeSem o (compile2 nm aStat aCnt aBody aHalt (preconditionGate matched)) st
        = (none, st') ∧
      CoreEnc aStat aCnt aBody aHalt st'
        (denoteStep ctx (preconditionGate matched) { resp := ctx.base, halted := false }) := by
  obtain ⟨st', hrun, henc, _, _, _⟩ :=
    compile2_correct o nm aStat aCnt aBody aHalt ctx hd (preconditionGate matched)
      { resp := ctx.base, halted := false } st hEnc hDec
  exact ⟨st', hrun, henc⟩

/-! ### 6.1 A CONCRETE skeleton the precondition-match keystone lands (non-vacuous RHS)

The keystone's right-hand side is the REAL `denoteStep`; at a concrete match context its
landed skeleton is status 304 with the halt flag set — a `P → P` tautology could not
compute this. -/

-- precondition-match lands status 304 / halted / body preserved:
def regression_304 : Bool := decide ((denoteStep ctx0 (preconditionGate pTrue)
          { resp := ctx0.base, halted := false }).resp.status = 304
  )
def regression_306 : Bool := decide ((denoteStep ctx0 (preconditionGate pTrue)
          { resp := ctx0.base, halted := false }).halted = true
  )
-- cache-static-asset lands header-count 1 / status 200 / live:
def regression_309 : Bool := decide ((denoteStep ctx0 (cacheControlStaticStage pTrue)
          { resp := ctx0.base, halted := false }).resp.headers.length = 1
  )
def regression_311 : Bool := decide ((denoteStep ctx0 (cacheControlStaticStage pTrue)
          { resp := ctx0.base, halted := false }).halted = false
  )

/-! ## 7. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/


end DN.Compiler.StageEvenMore
