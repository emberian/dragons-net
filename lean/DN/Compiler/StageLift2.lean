-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.StageLift2

Retained compiler/dataplane development and regression examples.
Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md. HTTP examples are compiler workloads, not dn server features.
-/

import DN.Compiler.StageProg2

namespace DN.Compiler.StageLift2

open DN.Compiler DN.Compiler.SerializeCompile DN.Compiler.StageProg DN.Compiler.StageOnion

variable {σ : Type}

/-! ## 1. Multi-header append in the response algebra

`addHeadersR hs` is a `RespProg` `seq`-chain of `addHeader`s. Its `denoteR` appends
the whole list — proven by structural induction, so it covers a set of ANY size. -/

/-- Append a whole header list, one `RespProg.addHeader` per entry, in order. -/
def addHeadersR : List (Bytes × Bytes) → RespProg
  | []          => .skip
  | (n, v) :: t => .seq (.addHeader n v) (addHeadersR t)

/-- **`denoteR_addHeadersR`.** The `seq`-chain of appends denotes to appending the
whole list to the arriving response's headers — for ANY list and ANY response. -/
theorem denoteR_addHeadersR (ctx : Ctx) :
    ∀ (hs : List (Bytes × Bytes)) (r : Response),
      denoteR ctx (addHeadersR hs) r = { r with headers := r.headers ++ hs } := by
  intro hs
  induction hs with
  | nil =>
    intro r
    show r = { r with headers := r.headers ++ [] }
    rw [List.append_nil]
  | cons nv t ih =>
    intro r
    obtain ⟨n, v⟩ := nv
    show denoteR ctx (addHeadersR t) (denoteR ctx (.addHeader n v) r) = _
    show denoteR ctx (addHeadersR t) { r with headers := r.headers ++ [(n, v)] } = _
    rw [ih { r with headers := r.headers ++ [(n, v)] }]
    show ({ r with headers := (r.headers ++ [(n, v)]) ++ t } : Response) = _
    rw [List.append_assoc]
    rfl

/-! ## 2. THE STAMP SHAPE — a conditional header append, re-pinned to `denoteR`

The deployed stamp stage passes the request untouched and, in its response phase,
appends one `(name, val)` under its own decision. With the affine builder erased
(the deployed `build_addHeader` equation), that response-phase effect on a response
`r` is `stampFn` below. `stampProg2` is the `RespProg` that computes it. -/

/-- **The deployed stamp's functional response effect** (builder erased via
`build_addHeader`): append `(name, val)` at the END of `r`'s headers exactly when the
stage's decision `p` fires at this context. -/
def stampFn (p : ReqPred) (name val : Bytes) (ctx : Ctx) (r : Response) : Response :=
  if p ctx then { r with headers := r.headers ++ [(name, val)] } else r

/-- **The stamp program** — the `RespProg` a conditional stamp stage's response phase
IS: `condR p (addHeader name val) skip`. No `gate`, no `halted` — this is a pure
response transform in the gate-free algebra. -/
def stampProg2 (p : ReqPred) (name val : Bytes) : RespProg :=
  .condR p (.addHeader name val) .skip

/-- **`denoteR_stampProg` — THE STAMP LIFT (re-pinned).** For ANY decision `p`, name,
value, context and arriving response `r`, the stamp program's `denoteR` computes
exactly the deployed conditional append `stampFn`. Both branches are discharged
(fire appends, pass leaves `r` untouched), so it is not vacuous; and it holds for
ANY `r` — the true response arriving from the inner onion, not a pre-baked `ctx.base`. -/
theorem denoteR_stampProg (p : ReqPred) (name val : Bytes) (ctx : Ctx) (r : Response) :
    denoteR ctx (stampProg2 p name val) r = stampFn p name val ctx r := by
  show (if p ctx then denoteR ctx (.addHeader name val) r else denoteR ctx .skip r)
      = stampFn p name val ctx r
  unfold stampFn
  cases h : p ctx with
  | true => rfl
  | false => rfl

/-- The unconditional stamp (F1: `Date`, request-id) is the stamp at the always-true
decision. -/
def alwaysStampProg (name val : Bytes) : RespProg := stampProg2 (fun _ => true) name val

/-- **`denoteR_alwaysStamp`.** The unconditional stamp always appends `(name, val)`. -/
theorem denoteR_alwaysStamp (name val : Bytes) (ctx : Ctx) (r : Response) :
    denoteR ctx (alwaysStampProg name val) r
      = { r with headers := r.headers ++ [(name, val)] } := by
  show denoteR ctx (stampProg2 (fun _ => true) name val) r = _
  rw [denoteR_stampProg]
  show (if (fun _ => true) ctx then { r with headers := r.headers ++ [(name, val)] } else r) = _
  rfl

/-! ### 2.1 The stamp as a two-phase stage — passes, then stamps -/

/-- **The stamp STAGE** — a pure transform stage: `guard := false` (never gates),
`refusal := skip`, `onResp := stampProg2 p name val`. -/
def stampSpec (p : ReqPred) (name val : Bytes) : StageSpec :=
  { guard := fun _ => false, refusal := .skip, onResp := stampProg2 p name val }

/-- **`runChain_stampSpec`.** A single stamp stage over a handler passes to the
handler and stamps its response — the deployed conditional append over `handler ctx`. -/
theorem runChain_stampSpec (p : ReqPred) (name val : Bytes)
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [stampSpec p name val] = stampFn p name val ctx (handler ctx) := by
  rw [runChain_stage_effect ctx handler (stampSpec p name val) [] rfl, runChain_nil]
  show denoteR ctx (stampProg2 p name val) (handler ctx) = _
  rw [denoteR_stampProg]

/-! ## 3. THE MULTI-HEADER STAMP STAGE — the security-header set, at any size

`secStage`'s response phase (StageProg2 §4.2) is a `seq` of two `addHeader`s; the
general form is `addHeadersR` over the whole rendered policy list. -/

/-- **The multi-header stamp stage** — appends a whole header set on pass. -/
def stampSetSpec (nvs : List (Bytes × Bytes)) : StageSpec :=
  { guard := fun _ => false, refusal := .skip, onResp := addHeadersR nvs }

/-- **`runChain_stampSetSpec`.** A single multi-header stamp stage appends its whole
set to the handler's response, in order — the deployed `foldl addHeader`, at any size. -/
theorem runChain_stampSetSpec (nvs : List (Bytes × Bytes))
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [stampSetSpec nvs]
      = { handler ctx with headers := (handler ctx).headers ++ nvs } := by
  rw [runChain_stage_effect ctx handler (stampSetSpec nvs) [] rfl, runChain_nil]
  show denoteR ctx (addHeadersR nvs) (handler ctx) = _
  rw [denoteR_addHeadersR]

/-! ## 4. THE GATE SHAPE — a firing guard with a fresh refusal record

A deployed gate answers `refusal` when its decision fires and passes otherwise. In
the two-phase onion this is a `StageSpec` whose `guard` is the fire decision and whose
`refusal` is the record built OVER `blankResp` (the deployed `.respond r` fresh-response
semantics — NOT a mutation of the base). `onResp := skip` (a pure gate is response-
transparent). -/

/-- **The refusal payload** — overwrite the status line, replace the body, append the
refusal's own headers. Built over `blankResp` (empty headers), this denotes to the
refusal record ON THE NOSE, with no `ctx.base.headers = []` side condition. -/
def refusalProg (r : Response) : RespProg :=
  .seq (.setStatus r.status r.reason)
    (.seq (.rewriteBody (.replace r.body)) (addHeadersR r.headers))

/-- **`denoteR_refusalProg` — hypothesis-free.** The refusal payload, run over the
fresh `blankResp` seed, denotes to EXACTLY the refusal record `r`. (The old flat gate
appended onto `ctx.base.headers` and kept its body — needing a side condition and
leaking the base body; the fresh seed fixes both.) -/
theorem denoteR_refusalProg (ctx : Ctx) (r : Response) :
    denoteR ctx (refusalProg r) blankResp = r := by
  show denoteR ctx (addHeadersR r.headers)
        (denoteR ctx (.rewriteBody (.replace r.body))
          (denoteR ctx (.setStatus r.status r.reason) blankResp)) = r
  rw [denoteR_addHeadersR]
  show ({ status := r.status, reason := r.reason,
          headers := ([] : List (Bytes × Bytes)) ++ r.headers, body := r.body } : Response) = r
  rw [List.nil_append]

/-- **The gate STAGE** — `guard := fire`, `refusal := refusalProg r`, `onResp := skip`. -/
def gateSpec (fire : ReqPred) (r : Response) : StageSpec :=
  { guard := fire, refusal := refusalProg r, onResp := .skip }

/-- The generic deployed single-gate serve: the refusal when the decision fires,
otherwise the HANDLER's response (the handler and every later stage are skipped on
the refusal path). -/
def gateEmitH (fire : ReqPred) (r : Response) (handler : Ctx → Response) (ctx : Ctx) : Response :=
  if fire ctx then r else handler ctx

/-- **`runChain_gateSpec` — the single-gate lift (re-pinned).** For ANY fire decision,
ANY refusal record and ANY handler, a gate stage's serve is EXACTLY the generic
deployed gate's emitted response. Both branches live (fire → the fresh refusal; pass →
the handler), so not vacuous. -/
theorem runChain_gateSpec (fire : ReqPred) (r : Response) (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateSpec fire r] = gateEmitH fire r handler ctx := by
  unfold gateEmitH
  cases h : fire ctx with
  | true =>
    rw [runChain_gate_short_circuits ctx handler (gateSpec fire r) []
          (show (gateSpec fire r).guard ctx = true from h), if_pos rfl]
    show denoteR ctx (refusalProg r) blankResp = r
    exact denoteR_refusalProg ctx r
  | false =>
    rw [runChain_stage_effect ctx handler (gateSpec fire r) []
          (show (gateSpec fire r).guard ctx = false from h),
        runChain_nil, if_neg (show ¬ ((false : Bool) = true) by decide)]
    show denoteR ctx .skip (handler ctx) = handler ctx
    rfl

/-! ### 4.1 The if-CHAIN gate — nested multi-status refusals in ONE stage

Several deployed gates are ordered if-chains answering a different refusal per branch
(auth `401`/`403`/`500`; framing `400`/`400`/`417`). In the onion this is ONE stage:
the `guard` fires iff any branch fires, and the `refusal` is a nested `condR` selecting
the first firing branch's refusal record. -/

/-- The nested-`condR` refusal: the first firing branch's refusal record. -/
def gateChainRefusal : List (ReqPred × Response) → RespProg
  | []          => .skip
  | (f, r) :: t => .condR f (refusalProg r) (gateChainRefusal t)

/-- The chain's guard: fires iff SOME branch fires. -/
def anyFires : List (ReqPred × Response) → ReqPred
  | []          => fun _ => false
  | (f, _) :: t => fun c => f c || anyFires t c

/-- **The if-chain gate STAGE.** -/
def gateChainSpec (branches : List (ReqPred × Response)) : StageSpec :=
  { guard := anyFires branches, refusal := gateChainRefusal branches, onResp := .skip }

/-- The generic deployed if-chain gate's emitted response: the first firing branch's
refusal, else the HANDLER (a request clearing every branch passes through). -/
def gateChainEmitH : List (ReqPred × Response) → (Ctx → Response) → Ctx → Response
  | [],          h, ctx => h ctx
  | (f, r) :: t, h, ctx => if f ctx then r else gateChainEmitH t h ctx

/-- The key inductive step: whether the chain guard fires selects the refusal fold or
the handler, exactly as the deployed if-chain does. -/
theorem gateChain_select (ctx : Ctx) (handler : Ctx → Response) :
    ∀ (branches : List (ReqPred × Response)),
      (if anyFires branches ctx then denoteR ctx (gateChainRefusal branches) blankResp
       else handler ctx)
        = gateChainEmitH branches handler ctx := by
  intro branches
  induction branches with
  | nil => rfl
  | cons fr t ih =>
    obtain ⟨f, r⟩ := fr
    show (if (f ctx || anyFires t ctx) then
            denoteR ctx (.condR f (refusalProg r) (gateChainRefusal t)) blankResp
          else handler ctx)
        = (if f ctx then r else gateChainEmitH t handler ctx)
    cases hf : f ctx with
    | true =>
      rw [Bool.true_or, if_pos rfl, if_pos rfl]
      show denoteR ctx (.condR f (refusalProg r) (gateChainRefusal t)) blankResp = r
      show (if f ctx then denoteR ctx (refusalProg r) blankResp
            else denoteR ctx (gateChainRefusal t) blankResp) = r
      rw [hf, if_pos rfl]
      exact denoteR_refusalProg ctx r
    | false =>
      rw [Bool.false_or, if_neg (show ¬ ((false : Bool) = true) by decide)]
      show (if anyFires t ctx then
              denoteR ctx (.condR f (refusalProg r) (gateChainRefusal t)) blankResp
            else handler ctx) = gateChainEmitH t handler ctx
      show (if anyFires t ctx then
              (if f ctx then denoteR ctx (refusalProg r) blankResp
               else denoteR ctx (gateChainRefusal t) blankResp)
            else handler ctx) = gateChainEmitH t handler ctx
      rw [hf, if_neg (show ¬ ((false : Bool) = true) by decide)]
      exact ih

/-- **`runChain_gateChainSpec` — the if-chain lift (re-pinned).** A nested multi-status
gate's serve is the first firing branch's fresh refusal, else the handler — the generic
deployed if-chain gate. ONE stage; ANY number of branches. -/
theorem runChain_gateChainSpec (branches : List (ReqPred × Response))
    (handler : Ctx → Response) (ctx : Ctx) :
    runChain ctx handler [gateChainSpec branches] = gateChainEmitH branches handler ctx := by
  rw [runChain_cons]
  show (if anyFires branches ctx then
          respFold ctx [] (denoteR ctx (gateChainRefusal branches) blankResp)
        else denoteR ctx .skip (runChain ctx handler []))
      = gateChainEmitH branches handler ctx
  show (if anyFires branches ctx then denoteR ctx (gateChainRefusal branches) blankResp
        else handler ctx)
      = gateChainEmitH branches handler ctx
  exact gateChain_select ctx handler branches

/-! ## 5. THE CORRECT-DENOTE PIN — response phases CARRY onto a refusal

This is the semantics the migration exists for. With a stamp stage OUTSIDE a firing
gate, the stamp's header is carried ONTO the gate's refusal — via the proven keystone
`runChain_gate_keystone`. The OLD flat `denote` DROPS it (the `halted` flag absorbs the
stamp), and the old `gateChain_short_circuits` proved everything after a gate VANISHES —
both wrong for the two-phase onion. -/

/-- **`stamp_carries_on_gate_refusal` — the whole point.** An outer unconditional stamp
over a firing inner gate: the serve is the gate's fresh refusal WITH the stamp's header
appended — for ANY handler (which never runs). The old flat interpreter cannot produce
this response at all (its fired gate absorbs the stamp). -/
theorem stamp_carries_on_gate_refusal (name val : Bytes) (fire : ReqPred) (refuseR : Response)
    (handler : Ctx → Response) (ctx : Ctx) (hfire : fire ctx = true) :
    runChain ctx handler [stampSpec (fun _ => true) name val, gateSpec fire refuseR]
      = { refuseR with headers := refuseR.headers ++ [(name, val)] } := by
  have hpre : ∀ s ∈ [stampSpec (fun _ => true) name val], s.guard ctx = false := by
    intro s hs
    simp at hs
    rw [hs]; rfl
  have hg : (gateSpec fire refuseR).guard ctx = true := hfire
  rw [show ([stampSpec (fun _ => true) name val, gateSpec fire refuseR] : List StageSpec)
        = [stampSpec (fun _ => true) name val] ++ gateSpec fire refuseR :: [] from rfl,
      runChain_gate_keystone ctx handler [stampSpec (fun _ => true) name val]
        (gateSpec fire refuseR) [] hpre hg]
  show denoteR ctx (stampProg2 (fun _ => true) name val)
        (denoteR ctx (refusalProg refuseR) blankResp) = _
  rw [denoteR_refusalProg, denoteR_stampProg]
  show (if (fun _ => true) ctx then { refuseR with headers := refuseR.headers ++ [(name, val)] }
        else refuseR) = { refuseR with headers := refuseR.headers ++ [(name, val)] }
  rfl

/-- **The multi-header form** — a whole security-header SET carried onto a gate refusal
(the general `secHeaders_on_refusal`, for any header list, any refusal, any handler). -/
theorem stampSet_carries_on_gate_refusal (nvs : List (Bytes × Bytes))
    (fire : ReqPred) (refuseR : Response) (handler : Ctx → Response) (ctx : Ctx)
    (hfire : fire ctx = true) :
    runChain ctx handler [stampSetSpec nvs, gateSpec fire refuseR]
      = { refuseR with headers := refuseR.headers ++ nvs } := by
  have hpre : ∀ s ∈ [stampSetSpec nvs], s.guard ctx = false := by
    intro s hs
    simp at hs
    rw [hs]; rfl
  have hg : (gateSpec fire refuseR).guard ctx = true := hfire
  rw [show ([stampSetSpec nvs, gateSpec fire refuseR] : List StageSpec)
        = [stampSetSpec nvs] ++ gateSpec fire refuseR :: [] from rfl,
      runChain_gate_keystone ctx handler [stampSetSpec nvs]
        (gateSpec fire refuseR) [] hpre hg]
  show denoteR ctx (addHeadersR nvs) (denoteR ctx (refusalProg refuseR) blankResp) = _
  rw [denoteR_refusalProg, denoteR_addHeadersR]

/-! ### 5.1 OLD-vs-NEW contrast + non-vacuity (kernel `#guard`s)

The SAME serve intent — "method gate + a stamp header" — under the old flat `denote`
versus the migrated onion. The old fold DROPS the header from the refusal; the onion
carries it. Concrete refusal records (transcribed field-for-field, RFC status/reason). -/

/-- `405` method-not-allowed refusal (carries the `Allow` header, non-empty body). -/
def methodNotAllowed : Response :=
  { status := 405, reason := str "Method Not Allowed",
    headers := [(str "Allow", str "GET, POST, HEAD, OPTIONS")],
    body := str "method not allowed\n" }

/-- `403` CIDR-admission refusal. -/
def forbidden403 : Response :=
  { status := 403, reason := str "Forbidden", headers := [],
    body := str "forbidden: ip not admitted" }

/-- The `X-Frame-Options` stamp used in the contrast (a real security header). -/
def xfoStamp : StageSpec := stampSpec (fun _ => true) xfoName xfoVal

/-- The method gate as a two-phase stage. -/
def gate405Spec : StageSpec := gateSpec (fun ctx => ! isAllowed ctx.req.method) methodNotAllowed

-- OLD flat DSL: gate fires, the stamp op after it is ABSORBED — the 405 goes out bare:
def regression_410 : Bool := decide ((StageProg.denote (.seq methodFilter securityHeaders) ctxPost).headers = []
  )
-- NEW onion: the SAME 405 refusal CARRIES the stamp header (outer stamp, inner gate):
def regression_412 : Bool := decide ((runChain ctxPost (fun c => c.base) [xfoStamp, gate405Spec]).headers
        = (methodNotAllowed.headers ++ [(xfoName, xfoVal)])
  )
def regression_414 : Bool := decide ((runChain ctxPost (fun c => c.base) [xfoStamp, gate405Spec]).status = 405
  )
-- and the refusal record is fresh (its own reason + body reach the wire, no base leak):
def regression_416 : Bool := decide ((runChain ctxPost (fun c => c.base) [xfoStamp, gate405Spec]).reason = str "Method Not Allowed"
  )
def regression_417 : Bool := decide ((runChain ctxPost (fun c => c.base) [xfoStamp, gate405Spec]).body = str "method not allowed\n"
  )
-- an allowed method passes: the handler answers, the stamp still applies:
def regression_419 : Bool := decide ((runChain ctxGet (fun c => c.base) [xfoStamp, gate405Spec]).status = 200
  )
def regression_420 : Bool := decide ((runChain ctxGet (fun c => c.base) [xfoStamp, gate405Spec]).headers = [(xfoName, xfoVal)]
  )

-- the single-gate lift lands the real refusal on fire and the handler on pass:
def regression_423 : Bool := decide ((runChain ctxPost (fun c => c.base) [gate405Spec]).status = 405
  )
def regression_424 : Bool := decide (serialize (runChain ctxGet (fun c => c.base) [gate405Spec]) = serialize baseOk
  )
def regression_425 : Bool := decide (serialize (runChain ctxPost (fun c => c.base) [gate405Spec])
        ≠ serialize (runChain ctxPost (fun c => c.base) [gateSpec (fun _ => true) forbidden403])
  )

-- the if-chain picks the FIRST firing branch, in order (a nested multi-status gate):
def regression_429 : Bool := decide ((runChain ctxPost (fun c => c.base)
          [gateChainSpec [(fun _ => true, forbidden403), (fun _ => true, methodNotAllowed)]]).status = 403
  )
def regression_431 : Bool := decide ((runChain ctxPost (fun c => c.base)
          [gateChainSpec [(fun _ => false, forbidden403), (fun _ => true, methodNotAllowed)]]).status = 405
  )
def regression_433 : Bool := decide (serialize (runChain ctxGet (fun c => c.base)
          [gateChainSpec [(fun _ => false, forbidden403), (fun _ => false, methodNotAllowed)]])
        = serialize baseOk
  )

-- the stamp genuinely drives both branches (fire appends, pass does not):
def regression_438 : Bool := decide ((denoteR ctxGet (stampProg2 (fun _ => true) xfoName xfoVal) baseOk).headers
        = baseOk.headers ++ [(xfoName, xfoVal)]
  )
def regression_440 : Bool := decide ((denoteR ctxGet (stampProg2 (fun _ => false) xfoName xfoVal) baseOk).headers = baseOk.headers
  )

/-! ## 6. Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound}, 0 sorryAx. -/


end DN.Compiler.StageLift2
