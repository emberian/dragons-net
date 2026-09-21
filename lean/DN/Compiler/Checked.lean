import DN.Compiler.Keywords
import DN.Compiler.Lower

/-! Conservative validation for the exported native subset used by the CLI.
This checks syntax/scope, not memory safety or a complete Pancake type system.
Raw `ppFun` remains an internal printer and is not a validation boundary. -/
namespace DN.Compiler.Checked
open Syntax Lower

/-- Why the gate refused a function: one constructor per rule, so every rule can be
required to carry an example that it, and nothing else, rejects. -/
inductive Reason
  | exportedName        -- not exported, or the name is not an identifier
  | foreignNamespace    -- an exported name outside this project's prefix
  | parameterCount      -- more parameters than the native profile takes
  | parameterShape      -- a parameter that is not one word
  | parameterName       -- a parameter name that is not an identifier
  | duplicateParameter  -- the same parameter name twice
  | literalWidth        -- a literal that does not fit a machine word
  | unboundVariable     -- a read of a name that is not in scope
  | baseAddress         -- the FFI control-block pointer
  | loadShape           -- a load of something other than one word
  | shiftAmount         -- a shift that is not a literal below one word
  | declarationName     -- a declared name that is not an identifier
  | redeclaration       -- a name declared while already in scope
  | unboundAssignment   -- an assignment to a name that is not in scope
  | callEffect          -- a call to another function
  | externalEffect      -- an external call
  | notExported         -- the function is not marked for export
  | unreachable         -- a statement after one that always leaves the function
  | missingReturn       -- a body that can run to its end without returning
  deriving BEq

def Reason.message : Reason → String
  | .exportedName => "invalid exported function name"
  | .foreignNamespace => "exported name outside the dn_ namespace"
  | .parameterCount => "native profile supports at most four parameters"
  | .parameterShape => "nonscalar parameter"
  | .parameterName => "invalid parameter name"
  | .duplicateParameter => "duplicate parameter"
  | .literalWidth => "literal wider than a machine word"
  | .unboundVariable => "variable not in scope"
  | .baseAddress => "base address is outside the exported profile"
  | .loadShape => "load of a shape other than one word"
  | .shiftAmount => "shift by other than a literal below one word"
  | .declarationName => "invalid declared name"
  | .redeclaration => "name already in scope"
  | .unboundAssignment => "assignment to a variable not in scope"
  | .callEffect => "calls are outside the exported profile"
  | .externalEffect => "external calls are outside the exported profile"
  | .notExported => "function is not exported"
  | .unreachable => "statement after one that always leaves the function"
  | .missingReturn => "body can reach its end without returning"

/-- A word the lexer of any pinned revision reads as a keyword cannot be a name:
the emitted source has to parse under both. -/
def reserved : List String := Keywords.all

def identifier (s : String) : Bool :=
  let letters (c : Char) := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
  match s.toList with
  | [] => false
  | c :: cs => letters c && cs.all (fun x => letters x || ('0' ≤ x && x ≤ '9')) &&
      !reserved.contains s

/-- An exported name becomes a global symbol of the linked program, where it can displace
a libc or runtime function of the same name. Keep exports in one namespace. -/
def exportPrefix : String := "dn_"

def inNamespace (s : String) : Bool := s.toList.take exportPrefix.length == exportPrefix.toList

def expression (scope : List String) : PExpr → Except Reason Unit
  | .const n => if n < 2^64 then .ok () else .error .literalWidth
  | .var x => if scope.contains x then .ok () else .error .unboundVariable
  | .base => .error .baseAddress
  | .binop _ a b => do expression scope a; expression scope b
  | .loadw sh a => if sh == 1 then expression scope a else .error .loadShape
  | .loadb a => expression scope a
  -- The semantics has no value for a nonzero shift of a whole word or more, so the
  -- distance has to be a literal the gate can see.
  | .shr l r =>
    match r with
    | .const n => if n < 64 then expression scope l else .error .shiftAmount
    | _ => .error .shiftAmount

mutual
/-- Statements after which control never reaches the next one. The compiler requires a body
to end this way and warns about anything that follows, so the gate enforces both. -/
def exits : PStmt → Bool
  | .ret _ => true
  | .ite _ t f => exitsL t && exitsL f
  | _ => false
def exitsL : List PStmt → Bool
  | [] => false
  | [s] => exits s
  | _ :: rest => exitsL rest
end

mutual
def statement (scope : List String) : PStmt → Except Reason Unit
  | .dec x e =>
    if !identifier x then .error .declarationName
    else if scope.contains x then .error .redeclaration
    else expression scope e
  | .assign x e => if scope.contains x then expression scope e else .error .unboundAssignment
  | .store a b | .storeb a b => do expression scope a; expression scope b
  | .ret e => expression scope e
  | .ite e a b => do expression scope e; statements scope a; statements scope b
  | .while e b => do expression scope e; statements scope b
  | .ffi _ _ => .error .externalEffect
  | .call _ _ _ => .error .callEffect
def statements (scope : List String) : List PStmt → Except Reason Unit
  | [] => .ok ()
  | s :: rest => do
    statement scope s
    if exits s && !rest.isEmpty then .error .unreachable
    else statements (match s with | .dec x _ => x :: scope | _ => scope) rest
end

/-- The scope a parameter list opens, in the order the parameters are bound. -/
def paramScope : List (Nat × String) → List String → Except Reason (List String)
  | [], scope => .ok scope
  | (shape, name) :: rest, scope =>
    if shape != 1 then .error .parameterShape
    else if !identifier name then .error .parameterName
    else if scope.contains name then .error .duplicateParameter
    else paramScope rest (name :: scope)

/-- Exported scalar functions with at most four parameters and an explicit final
return. This is our initial host ABI profile, not a restriction of all Pancake. -/
def emit (f : PFun) : Except Reason String := do
  unless f.exported do throw .notExported
  unless identifier f.name do throw .exportedName
  unless inNamespace f.name do throw .foreignNamespace
  unless f.params.length ≤ 4 do throw .parameterCount
  let scope ← paramScope f.params []
  statements scope f.body
  unless exitsL f.body do throw .missingReturn
  return ppFun f

/-! ## The accepted subset lowers

Nothing else in the gate checks that an accepted function has a model image: these
lemmas prove it, so the check cannot rot into an unreachable branch. -/

theorem expression_lowers {scope : List String} :
    ∀ e : PExpr, expression scope e = .ok () → (lowerExp e).isSome = true := by
  intro e
  induction e with
  | base => intro _; rfl
  | const n => intro _; rfl
  | var x => intro _; rfl
  | binop op a b iha ihb =>
    intro h
    simp only [expression, bind, Except.bind] at h
    cases hA : expression scope a with
    | error e => rw [hA] at h; simp at h
    | ok u =>
      rw [hA] at h
      have ha := iha (by rw [hA])
      have hb := ihb h
      cases hLa : lowerExp a with
      | none => rw [hLa] at ha; simp at ha
      | some a' =>
        cases hLb : lowerExp b with
        | none => rw [hLb] at hb; simp at hb
        | some b' => cases op <;> simp [lowerExp, hLa, hLb]
  | loadw sh a ih =>
    intro h
    simp only [expression] at h
    split at h
    · rename_i hsh
      have ha := ih h
      cases hLa : lowerExp a with
      | none => rw [hLa] at ha; simp at ha
      | some a' =>
        have : sh = 1 := by simpa using hsh
        subst this
        simp [lowerExp, hLa]
    · simp at h
  | loadb a ih =>
    intro h
    simp only [expression] at h
    have ha := ih h
    cases hLa : lowerExp a with
    | none => rw [hLa] at ha; simp at ha
    | some a' => simp [lowerExp, hLa]
  | shr l r ihl ihr =>
    intro h
    simp only [expression] at h
    split at h
    · split at h
      · have hl := ihl h
        cases hLl : lowerExp l with
        | none => rw [hLl] at hl; simp at hl
        | some l' => simp [lowerExp, hLl]
      · simp at h
    · simp at h

private theorem exp_some {scope : List String} {e : PExpr} (h : expression scope e = .ok ()) :
    ∃ v, lowerExp e = some v := by
  have := expression_lowers (scope := scope) e h
  cases hv : lowerExp e with
  | none => rw [hv] at this; simp at this
  | some v => exact ⟨v, rfl⟩

private theorem seq_ok {x y : Except Reason Unit} (h : (do x; y) = .ok ()) :
    x = .ok () ∧ y = .ok () := by
  cases hx : x with
  | error e => rw [hx] at h; simp [bind, Except.bind] at h
  | ok u =>
    rw [hx] at h
    simp [bind, Except.bind] at h
    exact ⟨by cases u; rfl, h⟩



theorem checked_lowers :
    (∀ (scope : List String) (s : PStmt),
        statement scope s = .ok () → (lowerStmt1 s).isSome = true) ∧
    (∀ (scope : List String) (ss : List PStmt),
        statements scope ss = .ok () → (lowerStmtsFold ss).isSome = true) := by
  apply statement.mutual_induct
  · intro scope x e hid h; simp [statement, hid] at h
  · intro scope x e hid hin h
    simp only [statement, if_neg hid, if_pos hin] at h
    simp at h
  · intro scope x e hid hin h
    simp only [statement, if_neg hid, if_neg hin] at h
    obtain ⟨v, hv⟩ := exp_some h
    simp [lowerStmt1, hv]
  · intro scope x e hin h
    simp only [statement, if_pos hin] at h
    obtain ⟨v, hv⟩ := exp_some h
    simp [lowerStmt1, hv]
  · intro scope x e hin h
    simp only [statement, if_neg hin] at h
    simp at h
  · intro scope a b h
    simp only [statement] at h
    obtain ⟨ha, hb⟩ := seq_ok h
    obtain ⟨a', hva⟩ := exp_some ha
    obtain ⟨b', hvb⟩ := exp_some hb
    simp [lowerStmt1, hva, hvb]
  · intro scope a b h
    simp only [statement] at h
    obtain ⟨ha, hb⟩ := seq_ok h
    obtain ⟨a', hva⟩ := exp_some ha
    obtain ⟨b', hvb⟩ := exp_some hb
    simp [lowerStmt1, hva, hvb]
  · intro scope e h
    simp only [statement] at h
    obtain ⟨v, hv⟩ := exp_some h
    simp [lowerStmt1, hv]
  · intro scope e a b iha ihb h
    simp only [statement] at h
    obtain ⟨he, hrest⟩ := seq_ok h
    obtain ⟨ha, hb⟩ := seq_ok hrest
    obtain ⟨c, hc⟩ := exp_some he
    have h1 := iha ha
    have h2 := ihb hb
    cases hfa : lowerStmtsFold a with
    | none => rw [hfa] at h1; simp at h1
    | some a' =>
      cases hfb : lowerStmtsFold b with
      | none => rw [hfb] at h2; simp at h2
      | some b' => simp [lowerStmt1, hc, hfa, hfb]
  · intro scope e b ihb h
    simp only [statement] at h
    obtain ⟨he, hb⟩ := seq_ok h
    obtain ⟨c, hc⟩ := exp_some he
    have h2 := ihb hb
    cases hfb : lowerStmtsFold b with
    | none => rw [hfb] at h2; simp at h2
    | some b' => simp [lowerStmt1, hc, hfb]
  · intro scope name args h; simp [statement] at h
  · intro scope r fn args h; simp [statement] at h
  · intro scope _; rfl
  · intro scope s rest ihs ihrest h
    simp only [statements] at h
    obtain ⟨hs, hrest'⟩ := seq_ok h
    split at hrest'
    · exact absurd hrest' (by simp)
    have h1 := ihs hs
    have h2 := ihrest hrest'
    cases rest with
    | nil => simpa [lowerStmtsFold] using h1
    | cons t ts =>
      cases hf : lowerStmtsFold (t :: ts) with
      | none => rw [hf] at h2; simp at h2
      | some p =>
        cases hl : lowerStmt1 s with
        | none => rw [hl] at h1; simp at h1
        | some q =>
          cases s with
          | dec n v =>
            cases hw : lowerExp v with
            | none => simp [lowerStmt1, hw] at h1
            | some w => simp [lowerStmtsFold, hw, hf]
          | assign a b => simp [lowerStmtsFold, hl, hf]
          | store a b => simp [lowerStmtsFold, hl, hf]
          | storeb a b => simp [lowerStmtsFold, hl, hf]
          | ffi a b => simp [lowerStmtsFold, hl, hf]
          | call a b c => simp [lowerStmtsFold, hl, hf]
          | ret a => simp [lowerStmtsFold, hl, hf]
          | ite a b c => simp [lowerStmtsFold, hl, hf]
          | «while» a b => simp [lowerStmtsFold, hl, hf]



theorem statements_lower {scope : List String} {ss : List PStmt} {u : Unit}
    (h : statements scope ss = .ok u) : (lowerStmtsFold ss).isSome = true := by
  cases u
  exact checked_lowers.2 scope ss h

theorem accepted_lowers {f : PFun} {src : String} (h : emit f = .ok src) :
    (lower f).isSome = true := by
  simp only [emit, bind, Except.bind] at h
  repeat' split at h
  all_goals first
    | exact absurd h (by simp)
    | (simp only [lower]; apply statements_lower; assumption)

/-- A function the gate refuses, paired with the closest one it accepts: the pair pins
which rule did the refusing, so a rule cannot quietly stop working. -/
structure RuleCase where
  reason : Reason
  rejected : PFun
  accepted : PFun

private def body1 : List PStmt := [.ret (.var "a")]
private def fn (name : String) (params : List (Nat × String)) (body : List PStmt) : PFun :=
  { name := name, exported := true, params := params, body := body }
private def probe (params : List (Nat × String)) (body : List PStmt) : PFun :=
  fn "dn_probe" params body
private def scalar (body : List PStmt) : PFun := probe [(1, "a")] body

/-- One case per rule. `catalog_covers_every_reason` makes a new rule without a case
fail to compile, and `catalog_is_honest` keeps each case on the rule it names. -/
def catalog : List RuleCase :=
  [{ reason := .exportedName, rejected := fn "while" [(1, "a")] body1, accepted := scalar body1 },
   { reason := .foreignNamespace, rejected := fn "atoi" [(1, "a")] body1, accepted := scalar body1 },
   { reason := .parameterCount,
     rejected := probe [(1, "a"), (1, "b"), (1, "c"), (1, "d"), (1, "e")] body1,
     accepted := probe [(1, "a"), (1, "b"), (1, "c"), (1, "d")] body1 },
   { reason := .parameterShape, rejected := probe [(2, "a")] body1, accepted := scalar body1 },
   { reason := .parameterName, rejected := probe [(1, "1a")] [.ret (.const 0)],
     accepted := scalar body1 },
   { reason := .duplicateParameter, rejected := probe [(1, "a"), (1, "a")] body1,
     accepted := probe [(1, "a"), (1, "b")] body1 },
   { reason := .literalWidth, rejected := scalar [.ret (.const (2 ^ 64))],
     accepted := scalar [.ret (.const (2 ^ 64 - 1))] },
   { reason := .unboundVariable, rejected := scalar [.ret (.var "b")], accepted := scalar body1 },
   { reason := .baseAddress, rejected := scalar [.ret .base], accepted := scalar body1 },
   { reason := .loadShape, rejected := scalar [.ret (.loadw 2 (.var "a"))],
     accepted := scalar [.ret (.loadw 1 (.var "a"))] },
   { reason := .shiftAmount, rejected := scalar [.ret (.shr (.var "a") (.const 64))],
     accepted := scalar [.ret (.shr (.var "a") (.const 63))] },
   { reason := .declarationName, rejected := scalar [.dec "1x" (.var "a"), .ret (.var "a")],
     accepted := scalar [.dec "x" (.var "a"), .ret (.var "x")] },
   { reason := .redeclaration,
     rejected := scalar [.dec "x" (.var "a"), .dec "x" (.var "a"), .ret (.var "x")],
     accepted := scalar [.dec "x" (.var "a"), .dec "y" (.var "a"), .ret (.var "y")] },
   { reason := .unboundAssignment, rejected := scalar [.assign "x" (.var "a"), .ret (.var "a")],
     accepted := scalar [.dec "x" (.var "a"), .assign "x" (.var "a"), .ret (.var "x")] },
   { reason := .externalEffect, rejected := scalar [.ffi "write" [.var "a"], .ret (.var "a")],
     accepted := scalar body1 },
   { reason := .callEffect, rejected := scalar [.call "x" "dn_other" [.var "a"], .ret (.var "a")],
     accepted := scalar body1 },
   { reason := .notExported,
     rejected := { name := "dn_probe", exported := false, params := [(1, "a")], body := body1 },
     accepted := scalar body1 },
   { reason := .unreachable,
     rejected := scalar [.ite (.var "a") [.ret (.var "a")] [.ret (.const 0)], .ret (.var "a")],
     accepted := scalar [.ite (.var "a") [.ret (.var "a")] [.ret (.const 0)]] },
   { reason := .missingReturn, rejected := scalar [.dec "x" (.var "a")],
     accepted := scalar [.dec "x" (.var "a"), .ret (.var "x")] }]

def rejectedWith (f : PFun) (r : Reason) : Bool :=
  match emit f with
  | .error r' => r' == r
  | .ok _ => false

/-- Every rule has a case: a new `Reason` without one does not compile. -/
theorem catalog_covers_every_reason (r : Reason) : catalog.any (fun c => c.reason == r) = true := by
  cases r <;> decide

/-- Each case is refused for the rule it names, and its accepted twin passes, so a case
cannot be kept alive by a different rule. -/
theorem catalog_is_honest :
    catalog.all (fun c => rejectedWith c.rejected c.reason && (emit c.accepted).isOk) = true := by
  decide

theorem injected_name_rejected : identifier "x); return 9; //" = false := by decide
theorem keyword_rejected : identifier "while" = false := by decide

/-- The lexer reads `@base`, `@top` and `@biw` as keywords only with the `@`, which the
identifier shape rejects on its own; the bare words are ordinary names. -/
theorem at_form_is_not_a_name : identifier "@base" = false := by decide
theorem bare_base_is_a_name : identifier "base" = true := by decide

/-- Names the C host and the Cake runtime already define, which an export would displace
or clash with at assembly time. -/
theorem host_names_rejected :
    ["atoi", "memcpy", "malloc", "main", "cml_main", "cake_return", "can_enter"].all
      (fun n => rejectedWith (fn n [(1, "a")] body1) .foreignNamespace) = true := by decide

theorem branch_local_does_not_escape :
    statements [] [.ite (.const 1) [.dec "x" (.const 2)] [], .ret (.var "x")]
      = .error .unboundVariable := rfl

end DN.Compiler.Checked
