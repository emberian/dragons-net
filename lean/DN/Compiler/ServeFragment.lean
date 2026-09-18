-- SPDX-License-Identifier: AGPL-3.0-or-later
/-
# DN.Compiler.ServeFragment

Retained compiler/dataplane development and regression examples.
Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md. HTTP examples are compiler workloads, not dn server features.
-/

import DN.Compiler.ProofProducing

namespace DN.Compiler.ServeFragment

open DN.Compiler DN.Compiler.Region DN.Compiler.Compose DN.Compiler.ProofProducing

variable {σ : Type}

/-! ## Stage 1 — ConnLimit: `admits connCap active` (EXACT `active < 4`)

drorb `Reactor/Stage/ConnLimit.lean`: `admits cap active := (cap == 0 || active <
cap)`, deployed `connCap = 4`. Since `4 == 0` is `false`, the deployed decision is
EXACTLY `active < 4`. `activeVal s` is the current active-connection count word.
Writes `result := 1` (admit) / `0` (deny → 503 downstream). Data-dependent guard
reads local `"active"` — needs the input-scoping fact `hactive`. -/
def connLimitDecision (activeVal : PancakeState σ → Word) : Stage σ :=
  .cond (.cmp .less (.var "active") (.const 4)) (fun s => signedLt (activeVal s) 4)
    (.prim (assignPrim "result" (.const 1) (fun _ => 1)))
    (.prim (assignPrim "result" (.const 0) (fun _ => 0)))

theorem connLimitDecision_wf (o : Oracle σ) (activeVal : PancakeState σ → Word)
    (hactive : ∀ s : PancakeState σ, s.locals "active" = some (activeVal s)) :
    WF o (connLimitDecision activeVal) := by
  wf_auto

/-- CERTIFICATE, AUTO-PRODUCED for the ConnLimit decision. -/
theorem connLimitDecision_cert (o : Oracle σ) (activeVal : PancakeState σ → Word)
    (hactive : ∀ s : PancakeState σ, s.locals "active" = some (activeVal s)) :
    Refines o (emit (connLimitDecision activeVal)) (denote (connLimitDecision activeVal)) :=
  emit_correct_generic o _ (connLimitDecision_wf o activeVal hactive)

def connLimitDecision_translated (o : Oracle σ) (activeVal : PancakeState σ → Word)
    (hactive : ∀ s : PancakeState σ, s.locals "active" = some (activeVal s)) :
    { p : PancakeProg // Refines o p (denote (connLimitDecision activeVal)) } :=
  translateCert o (connLimitDecision activeVal) (connLimitDecision_wf o activeVal hactive)

/-! ## Stage 2 — BodyLimit: `oversized req` (EXACT `7 < cldigits`)

drorb `Reactor/Stage/BodyLimit.lean`: `oversized := decide (maxCLDigits < len)`,
deployed `maxCLDigits = 7`. EXACTLY `7 < len` on the `Content-Length` digit count.
`clVal s` is that count word. Writes `result := 1` (oversized → 413) / `0`
(within). The guard reads local `"cldigits"` on the RIGHT of `<`. -/
def bodyLimitDecision (clVal : PancakeState σ → Word) : Stage σ :=
  .cond (.cmp .less (.const 7) (.var "cldigits")) (fun s => signedLt 7 (clVal s))
    (.prim (assignPrim "result" (.const 1) (fun _ => 1)))
    (.prim (assignPrim "result" (.const 0) (fun _ => 0)))

theorem bodyLimitDecision_wf (o : Oracle σ) (clVal : PancakeState σ → Word)
    (hcl : ∀ s : PancakeState σ, s.locals "cldigits" = some (clVal s)) :
    WF o (bodyLimitDecision clVal) := by
  wf_auto

/-- CERTIFICATE, AUTO-PRODUCED for the BodyLimit decision. -/
theorem bodyLimitDecision_cert (o : Oracle σ) (clVal : PancakeState σ → Word)
    (hcl : ∀ s : PancakeState σ, s.locals "cldigits" = some (clVal s)) :
    Refines o (emit (bodyLimitDecision clVal)) (denote (bodyLimitDecision clVal)) :=
  emit_correct_generic o _ (bodyLimitDecision_wf o clVal hcl)

def bodyLimitDecision_translated (o : Oracle σ) (clVal : PancakeState σ → Word)
    (hcl : ∀ s : PancakeState σ, s.locals "cldigits" = some (clVal s)) :
    { p : PancakeProg // Refines o p (denote (bodyLimitDecision clVal)) } :=
  translateCert o (bodyLimitDecision clVal) (bodyLimitDecision_wf o clVal hcl)

/-! ## Stage 3 — IpFilter: `deployAdmits a` (EXACT on the CIDR first octet)

drorb `Reactor/Stage/IpFilter.lean` (HOL4 C29): the deployed ruleset is the SINGLE
block `deny 10.0.0.0/8` with `defaultDeny := false`. A `/8` CIDR match tests only
the first octet, so `deployAdmits a = (firstOctet a ≠ 10)`, i.e. admit iff
`octet < 10 ∨ 10 < octet`. `octetVal s` is the first octet word. Writes
`result := 1` (admit) / `0` (deny → 403). The nested `cond` cascade reads local
`"octet"` in both guards. -/
def ipfilterDecision (octetVal : PancakeState σ → Word) : Stage σ :=
  .cond (.cmp .less (.var "octet") (.const 10)) (fun s => signedLt (octetVal s) 10)
    (.prim (assignPrim "result" (.const 1) (fun _ => 1)))
    (.cond (.cmp .less (.const 10) (.var "octet")) (fun s => signedLt 10 (octetVal s))
      (.prim (assignPrim "result" (.const 1) (fun _ => 1)))
      (.prim (assignPrim "result" (.const 0) (fun _ => 0))))

theorem ipfilterDecision_wf (o : Oracle σ) (octetVal : PancakeState σ → Word)
    (hoctet : ∀ s : PancakeState σ, s.locals "octet" = some (octetVal s)) :
    WF o (ipfilterDecision octetVal) := by
  wf_auto

/-- CERTIFICATE, AUTO-PRODUCED for the IpFilter decision. -/
theorem ipfilterDecision_cert (o : Oracle σ) (octetVal : PancakeState σ → Word)
    (hoctet : ∀ s : PancakeState σ, s.locals "octet" = some (octetVal s)) :
    Refines o (emit (ipfilterDecision octetVal)) (denote (ipfilterDecision octetVal)) :=
  emit_correct_generic o _ (ipfilterDecision_wf o octetVal hoctet)

def ipfilterDecision_translated (o : Oracle σ) (octetVal : PancakeState σ → Word)
    (hoctet : ∀ s : PancakeState σ, s.locals "octet" = some (octetVal s)) :
    { p : PancakeProg // Refines o p (denote (ipfilterDecision octetVal)) } :=
  translateCert o (ipfilterDecision octetVal) (ipfilterDecision_wf o octetVal hoctet)

/-! ## Stage 4 — MethodFilter: `isAllowed m` (TAG form `tag < 4`)

drorb `Reactor/Stage/MethodFilter.lean`: `isAllowed m := allowedMethods.contains m`
over `[GET, POST, HEAD, OPTIONS]`. The real `contains` is a LIST-membership LOOP
over byte-strings; on the enum→tag encoding the redirect reference also uses
(allowed methods as `{0,1,2,3}`, others `≥ 4`) the decision is EXACTLY `tag < 4`.
`tagVal s` is the method tag word. Writes `result := 1` (allowed) / `0` (405). The
byte-string decode is the P3 loop; this is the tag-domain decision. -/
def methodFilterDecision (tagVal : PancakeState σ → Word) : Stage σ :=
  .cond (.cmp .less (.var "method") (.const 4)) (fun s => signedLt (tagVal s) 4)
    (.prim (assignPrim "result" (.const 1) (fun _ => 1)))
    (.prim (assignPrim "result" (.const 0) (fun _ => 0)))

theorem methodFilterDecision_wf (o : Oracle σ) (tagVal : PancakeState σ → Word)
    (hmethod : ∀ s : PancakeState σ, s.locals "method" = some (tagVal s)) :
    WF o (methodFilterDecision tagVal) := by
  wf_auto

/-- CERTIFICATE, AUTO-PRODUCED for the MethodFilter (tag-domain) decision. -/
theorem methodFilterDecision_cert (o : Oracle σ) (tagVal : PancakeState σ → Word)
    (hmethod : ∀ s : PancakeState σ, s.locals "method" = some (tagVal s)) :
    Refines o (emit (methodFilterDecision tagVal)) (denote (methodFilterDecision tagVal)) :=
  emit_correct_generic o _ (methodFilterDecision_wf o tagVal hmethod)

def methodFilterDecision_translated (o : Oracle σ) (tagVal : PancakeState σ → Word)
    (hmethod : ∀ s : PancakeState σ, s.locals "method" = some (tagVal s)) :
    { p : PancakeProg // Refines o p (denote (methodFilterDecision tagVal)) } :=
  translateCert o (methodFilterDecision tagVal) (methodFilterDecision_wf o tagVal hmethod)

/-! ## Stage 5 — SecurityHeaders: `wireHeaders policy` (EXACT, CLOSED, ZERO hyps)

drorb `Reactor/Stage/SecurityHeaders.lean` (C26): `onResponse` UNCONDITIONALLY
folds a fixed header list onto the response — no branch, no loop, no input read.
Modelled as a `seq` of three distinct CLOSED `assign`s setting header-present flags
(`hsts`, `xfo`, `nosniff` — the deployed HSTS + X-Frame-Options + X-Content-Type).
All expressions are closed, so `wf_auto` closes `WF` with NO hypotheses (the
`closedDemo` class). Non-vacuous: three distinct locals are written. -/
def securityHeadersDecision : Stage σ :=
  .seq (.prim (assignPrim "hsts" (.const 1) (fun _ => 1)))
    (.seq (.prim (assignPrim "xfo" (.const 1) (fun _ => 1)))
      (.prim (assignPrim "nosniff" (.const 1) (fun _ => 1))))

/-- `wf_auto` closes the SecurityHeaders decision with ZERO hypotheses. -/
theorem securityHeadersDecision_wf (o : Oracle σ) :
    WF o (securityHeadersDecision (σ := σ)) := by
  wf_auto

/-- CERTIFICATE, AUTO-PRODUCED for the SecurityHeaders decision (zero hyps). -/
theorem securityHeadersDecision_cert (o : Oracle σ) :
    Refines o (emit (securityHeadersDecision (σ := σ)))
      (denote (securityHeadersDecision (σ := σ))) :=
  emit_correct_generic o _ (securityHeadersDecision_wf o)

def securityHeadersDecision_translated (o : Oracle σ) :
    { p : PancakeProg // Refines o p (denote (securityHeadersDecision (σ := σ))) } :=
  translateCert o securityHeadersDecision (securityHeadersDecision_wf o)

/-! ## Emitted-DN.Compiler witnesses (Stack L target = `Sem.PancakeProg`)

Each `emit <stage>` is a concrete nested `If (Cmp Less …) (Assign "result" …) …`
(or, for SecurityHeaders, a `Seq` of `Assign`s) over the model AST — the same
shape the HOL4 C-series probes lowered. Instantiate the data projections at `Unit`
and read the emitted program to confirm it genuinely computes the decision. -/
section EmitWitness

/-- Read a named local (default 0) so each emitted program is a closed term. -/
def localVal (name : String) : PancakeState σ → Word := fun s => (s.locals name).getD 0


end EmitWitness

end DN.Compiler.ServeFragment
