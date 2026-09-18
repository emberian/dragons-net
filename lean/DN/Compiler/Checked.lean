import DN.Compiler.Lower

/-! Conservative validation for the exported native subset used by the CLI.
This checks syntax/scope, not memory safety or a complete Pancake type system.
Raw `ppFun` remains an internal printer and is not a validation boundary. -/
namespace DN.Compiler.Checked
open Syntax Lower

def reserved : List String :=
  ["skip", "st", "stw", "st8", "st16", "st32", "if", "else", "while",
   "break", "continue", "raise", "return", "tick", "var", "with", "handle",
   "biw", "named", "lds", "ld8", "ldw", "ld16", "ld32", "base", "top",
   "struct", "in", "fun", "export", "true", "false", "inline"]

def identifier (s : String) : Bool :=
  let letters (c : Char) := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
  match s.toList with
  | [] => false
  | c :: cs => letters c && cs.all (fun x => letters x || ('0' ≤ x && x ≤ '9')) &&
      !reserved.contains s

def expression (scope : List String) : PExpr → Bool
  | .const n => n < 2^64
  | .var x => scope.contains x
  | .base => false
  | .binop _ a b => expression scope a && expression scope b
  | .loadw sh a => sh == 1 && expression scope a
  | .loadb a => expression scope a

mutual
def statement (scope : List String) : PStmt → Bool
  | .dec x e => identifier x && !scope.contains x && expression scope e
  | .assign x e => scope.contains x && expression scope e
  | .store a b | .storeb a b => expression scope a && expression scope b
  | .ret e => expression scope e
  | .ite e a b => expression scope e && statements scope a && statements scope b
  | .while e b => expression scope e && statements scope b
  | .ffi _ _ | .call _ _ _ => false
def statements (scope : List String) : List PStmt → Bool
  | [] => true
  | s :: rest => statement scope s &&
      statements (match s with | .dec x _ => x :: scope | _ => scope) rest
end

/-- Exported scalar functions with at most four parameters and an explicit final
return. This is our initial host ABI profile, not a restriction of all Pancake. -/
def emit (f : PFun) : Except String String := do
  unless f.exported && identifier f.name do throw "invalid exported function name"
  unless f.params.length ≤ 4 do throw "native profile supports at most four parameters"
  let mut scope := []
  for (shape, name) in f.params do
    unless shape == 1 && identifier name && !scope.contains name do
      throw "invalid, duplicate, or nonscalar parameter"
    scope := name :: scope
  unless statements scope f.body do throw "unsupported expression, effect, or local scope"
  unless (match f.body.getLast? with | some (.ret _) => true | _ => false) do
    throw "native profile requires an explicit final return"
  unless (lower f).isSome do throw "function does not lower to the modeled fragment"
  return ppFun f

theorem injected_name_rejected : identifier "x); return 9; //" = false := by decide
theorem keyword_rejected : identifier "while" = false := by decide
theorem free_local_rejected : expression [] (.var "x") = false := rfl
theorem branch_local_does_not_escape :
    statements [] [.ite (.const 1) [.dec "x" (.const 2)] [], .ret (.var "x")] = false := rfl
theorem oversized_literal_rejected : expression [] (.const (2^64)) = false := by decide
theorem duplicate_parameter_rejected :
    (emit { name := "probe", exported := true, params := [(1,"x"),(1,"x")],
            body := [.ret (.var "x")] }).isOk = false := by decide

end DN.Compiler.Checked
