-- SPDX-License-Identifier: AGPL-3.0-or-later
import DN.Compiler.Parse
import DN.Compiler.Precedence

/-!
# DN.Compiler.ParseCorrect

What `DN.Compiler.Parse`, CakeML's parser written again in Lean, makes of every program the gate
prints. The lexer reads the printed text as the printer's tokens (`lex_program`); the grammar reads
those tokens as the trees `tree`, `blockTree` and `funTree` give, at any nesting, with the fuel it
is given (`program_reads`); and those trees, every name made local, read in the model, have the
canonical form of the lowering (`canon_tree`, `canon_block`), which `Canon.canon_eval` shows
identifies only expressions that evaluate alike. `emitProgram_reads`, `emitWith_reads`,
`emit_reads` and `emitMain_reads` say it of what the gate accepts. That `Parse` is CakeML's parser
is tested, not proved (`scripts/check_parse.sh`).
-/

namespace DN.Compiler.ParseCorrect

open DN.Compiler DN.Compiler.Syntax DN.Compiler.Parse

/-! ## The lexer on the printer's text -/

/-- A character after which a word, a number or a run of symbol characters ends. -/
def delim (c : Char) : Bool := c = ' ' || c = '\n' || c = ';' || c = ',' || c = '(' || c = ')'

def Delim : List Char → Prop
  | [] => True
  | c :: _ => delim c = true

/-- `cs` lexes to `ts`, whatever follows that starts with a delimiter. -/
def LexesTo (cs : List Char) (ts : List Tok) : Prop :=
  ∀ rest, Delim rest → lexChars (cs ++ rest) = (lexChars rest).map (ts ++ ·)

/-- `cs` lexes to `ts`, whatever follows. -/
def LexesAny (cs : List Char) (ts : List Tok) : Prop :=
  ∀ rest, lexChars (cs ++ rest) = (lexChars rest).map (ts ++ ·)

theorem LexesAny.to {cs ts} (h : LexesAny cs ts) : LexesTo cs ts := fun rest _ => h rest

theorem LexesAny.nil : LexesAny [] [] := fun rest => by simp

theorem LexesAny.cat {a b ta tb} (ha : LexesAny a ta) (hb : LexesAny b tb) :
    LexesAny (a ++ b) (ta ++ tb) := fun rest => by
  rw [List.append_assoc, ha, hb]
  cases lexChars rest <;> simp

theorem LexesAny.catTo {a b ta tb} (ha : LexesAny a ta) (hb : LexesTo b tb) :
    LexesTo (a ++ b) (ta ++ tb) := fun rest hr => by
  rw [List.append_assoc, ha, hb rest hr]
  cases lexChars rest <;> simp

theorem LexesTo.cat {a b ta tb} (ha : LexesTo a ta) (hb : LexesTo b tb) (hd : Delim b)
    (hne : b ≠ []) : LexesTo (a ++ b) (ta ++ tb) := fun rest hr => by
  have : Delim (b ++ rest) := by
    cases b with
    | nil => exact absurd rfl hne
    | cons c cs => exact hd
  rw [List.append_assoc, ha _ this, hb rest hr]
  cases lexChars rest <;> simp

theorem LexesTo.catAny {a b ta tb} (ha : LexesTo a ta) (hb : LexesAny b tb) (hd : Delim b)
    (hne : b ≠ []) : LexesAny (a ++ b) (ta ++ tb) := fun rest => by
  have : Delim (b ++ rest) := by
    cases b with
    | nil => exact absurd rfl hne
    | cons c cs => exact hd
  rw [List.append_assoc, ha _ this, hb rest]
  cases lexChars rest <;> simp

theorem lexChars_space {c : Char} (h : isSpace c = true) (cs : List Char) :
    lexChars (c :: cs) = lexChars cs := by
  rw [lexChars]; simp [h]

theorem LexesAny.space {c : Char} (h : isSpace c = true) : LexesAny [c] [] := fun rest => by
  simp [lexChars_space h]

theorem LexesAny.spaces : ∀ (n : Nat), LexesAny (List.replicate n ' ') []
  | 0 => LexesAny.nil
  | n + 1 => by
    have := (LexesAny.space (c := ' ') (by decide)).cat (LexesAny.spaces n)
    simpa [List.replicate_succ] using this

/-- A character that is a token by itself, whatever follows. -/
theorem LexesAny.single {c : Char} {t : Tok} (hs : isSpace c = false) (hd : isDigit c = false)
    (hm : c ≠ '-') (hsl : c ≠ '/') (h1 : isSingleton c = true)
    (ht : symTok (String.singleton c) = some t) : LexesAny [c] [t] := fun rest => by
  rw [List.singleton_append, lexChars]
  simp only [hs, hd, hm, hsl, h1, ht, Bool.false_eq_true, ↓reduceIte, decide_false,
    Bool.false_and]
  cases lexChars rest <;> rfl

/-! ### Characters, by their codes -/

theorem code_le (c d : Char) : c ≤ d ↔ c.toNat ≤ d.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

theorem eq_code (c d : Char) : c = d ↔ c.toNat = d.toNat := Char.toNat_inj.symm

/-- A character a word starts with. -/
def startChar (c : Char) : Bool := isAlpha c || c = '_' || c = '@'

theorem startChar_code {c : Char} (h : startChar c = true) :
    (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ c.toNat = 95 ∨
      c.toNat = 64 := by
  simp only [startChar, isAlpha, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, code_le,
    eq_code, Char.reduceToNat] at h
  omega

theorem disjoint_of {L : List Char} {p : Char → Bool} (hL : ∀ x ∈ L, p x = false) {c : Char}
    (h : p c = true) : L.contains c = false := by
  cases hc : L.contains c with
  | false => rfl
  | true =>
    have := hL c (List.contains_iff_mem.mp hc)
    rw [h] at this; cases this

theorem startChar_facts {c : Char} (h : startChar c = true) :
    isSpace c = false ∧ isDigit c = false ∧ c ≠ '-' ∧ c ≠ '/' ∧ isSingleton c = false ∧
      beginsGroup c = false ∧ (isAlpha c || c = '@' || c = '_') = true := by
  have hc := startChar_code h
  refine ⟨?_, ?_, ?_, ?_, disjoint_of (by decide) h, disjoint_of (by decide) h, ?_⟩
  · simp only [isSpace, Bool.or_eq_false_iff, Bool.and_eq_false_imp, decide_eq_false_iff_not,
      eq_code, Char.reduceToNat]
    omega
  · simp only [isDigit, Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not, code_le,
      Char.reduceToNat]
    omega
  · simp only [ne_eq, eq_code, Char.reduceToNat]; omega
  · simp only [ne_eq, eq_code, Char.reduceToNat]; omega
  · simp only [startChar, Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h <;> simp [h]

theorem isDigit_eq (c : Char) : isDigit c = c.isDigit := by
  simp only [isDigit, Char.isDigit, code_le, Char.toNat, UInt32.le_iff_toNat_le, ge_iff_le]

theorem digit_facts {c : Char} (h : isDigit c = true) : isSpace c = false := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, code_le, Char.reduceToNat] at h
  simp only [isSpace, Bool.or_eq_false_iff, Bool.and_eq_false_imp, decide_eq_false_iff_not,
    eq_code, Char.reduceToNat]
  omega

theorem delim_facts {c : Char} (h : delim c = true) :
    isWordRest c = false ∧ isDigit c = false ∧ inGroup c = false := by
  simp only [delim, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((((h | h) | h) | h) | h) | h <;> subst h <;> decide

/-! ### Words, numbers and symbols -/

theorem readWhile_all (p : Char → Bool) :
    ∀ (ws rest : List Char), ws.all p = true → (∀ c t, rest = c :: t → p c = false) →
      readWhile p (ws ++ rest) = (ws, rest)
  | [], [], _, _ => rfl
  | [], c :: t, _, h => by simp [readWhile, h c t rfl]
  | w :: ws, rest, hw, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hw
    simp [readWhile, hw.1, readWhile_all p ws rest hw.2 h]

theorem stop_of_delim {p : Char → Bool} (hp : ∀ c, delim c = true → p c = false) {rest : List Char}
    (hr : Delim rest) : ∀ c t, rest = c :: t → p c = false := by
  intro c t h; subst h; exact hp c hr

theorem bind_cons {t : Tok} (o : Option (List Tok)) :
    (do let r ← o; pure (t :: r)) = o.map ([t] ++ ·) := by
  cases o <;> rfl

theorem lex_word {c : Char} {ws : List Char} {t : Tok} (hc : startChar c = true)
    (hws : ws.all isWordRest = true) (ht : wordTok (String.ofList (c :: ws)) = some t) :
    LexesTo (c :: ws) [t] := fun rest hr => by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := startChar_facts hc
  have hrw := readWhile_all isWordRest ws rest hws
    (stop_of_delim (fun c h => (delim_facts h).1) hr)
  rw [List.cons_append, lexChars]
  simp only [h0, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ↓reduceIte, decide_false,
    Bool.false_and, hrw, ht]
  cases lexChars rest <;> rfl

theorem lex_nat (n : Nat) : LexesTo (Nat.toDigits 10 n) [.int n] := fun rest hr => by
  have hall : ∀ x ∈ Nat.toDigits 10 n, isDigit x = true := fun x hx => by
    rw [isDigit_eq]; exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hx
  cases hd : Nat.toDigits 10 n with
  | nil => exact absurd hd Nat.toDigits_ne_nil
  | cons d ds =>
    have hdd : isDigit d = true := hall d (by simp [hd])
    have hds : ds.all isDigit = true := by
      simp only [List.all_eq_true]; intro x hx; exact hall x (by simp [hd, hx])
    have hrw := readWhile_all isDigit ds rest hds (stop_of_delim (fun c h => (delim_facts h).2.1) hr)
    have hn : decimal (d :: ds) = n := by
      rw [← hd]; exact Nat.ofDigitChars_ten_toDigits
    rw [List.cons_append, lexChars]
    simp only [digit_facts hdd, hdd, Bool.false_eq_true, ↓reduceIte, hrw, hn]
    cases lexChars rest <;> rfl

theorem lex_group {c : Char} {cs : List Char} {t : Tok} (hb : beginsGroup c = true)
    (h0 : isSpace c = false) (h1 : isDigit c = false) (h2 : c ≠ '-') (h3 : c ≠ '/')
    (h4 : isSingleton c = false) (hcs : cs.all inGroup = true)
    (ht : symTok (String.ofList (c :: cs)) = some t) : LexesTo (c :: cs) [t] := fun rest hr => by
  have hrw := readWhile_all inGroup cs rest hcs (stop_of_delim (fun c h => (delim_facts h).2.2) hr)
  rw [List.cons_append, lexChars]
  simp only [h0, h1, h2, h3, h4, hb, Bool.false_eq_true, ↓reduceIte, decide_false,
    Bool.false_and, hrw, ht]
  cases lexChars rest <;> rfl

theorem lex_minus : LexesAny ['-', ' '] [.sym "-"] := fun rest => by
  rw [List.cons_append, lexChars]
  simp only [List.cons_append, List.nil_append]
  have : (isSpace '-') = false := by decide
  simp only [this, show isDigit '-' = false by decide, show isDigit ' ' = false by decide,
    show isSingleton '-' = true by decide, Bool.false_eq_true, ↓reduceIte, List.head?_cons,
    Option.map_some, Option.getD_some, Bool.and_false, show ('-' = '/') = False by decide]
  rw [show symTok (String.singleton '-') = some (.sym "-") by decide, lexChars_space (by decide)]
  cases lexChars rest <;> rfl

theorem lex_free {c : Char} {t : Tok} (hs : isSpace c = false) (hd : isDigit c = false)
    (hm : c ≠ '-') (hsl : c ≠ '/') (h1 : isSingleton c = true)
    (ht : symTok (String.singleton c) = some t) {rest : List Char} {ts : List Tok}
    (h : LexesAny rest ts) : LexesAny (c :: rest) (t :: ts) :=
  (LexesAny.single hs hd hm hsl h1 ht).cat h

theorem lex_free' {c : Char} {t : Tok} (hs : isSpace c = false) (hd : isDigit c = false)
    (hm : c ≠ '-') (hsl : c ≠ '/') (h1 : isSingleton c = true)
    (ht : symTok (String.singleton c) = some t) {rest : List Char} {ts : List Tok}
    (h : LexesTo rest ts) : LexesTo (c :: rest) (t :: ts) :=
  (LexesAny.single hs hd hm hsl h1 ht).catTo h

/-- Space, then what lexes. -/
theorem lex_sp {rest : List Char} {ts : List Tok} (h : LexesTo rest ts) : LexesTo (' ' :: rest) ts :=
  (LexesAny.space (c := ' ') (by decide)).catTo h

theorem lex_spAny {rest : List Char} {ts : List Tok} (h : LexesAny rest ts) :
    LexesAny (' ' :: rest) ts :=
  (LexesAny.space (c := ' ') (by decide)).cat h

/-- A word or a run of symbol characters, a space, then what lexes. -/
theorem lex_then {w : List Char} {t : Tok} (hw : LexesTo w [t]) {rest : List Char} {ts : List Tok}
    (h : LexesTo rest ts) : LexesTo (w ++ ' ' :: rest) (t :: ts) :=
  hw.cat (lex_sp h) (by simp [Delim, delim]) (by simp)

theorem lex_thenAny {w : List Char} {t : Tok} (hw : LexesTo w [t]) {rest : List Char}
    {ts : List Tok} (h : LexesAny rest ts) : LexesAny (w ++ ' ' :: rest) (t :: ts) :=
  hw.catAny (lex_spAny h) (by simp [Delim, delim]) (by simp)

/-! ### Names -/

/-- A name the lexer reads as one: a word that is no keyword. -/
structure IsName (s : String) : Prop where
  word : ∃ c ws, s.toList = c :: ws ∧ startChar c = true ∧ c ≠ '@' ∧ ws.all isWordRest = true
  notKw : keywords.contains s = false

theorem lex_name {s : String} (h : IsName s) : LexesTo s.toList [.ident s] := by
  obtain ⟨c, ws, hs, hc, ha, hws⟩ := h.word
  rw [hs]
  refine lex_word hc hws ?_
  rw [← hs, String.ofList_toList, wordTok, h.notKw]
  simp [String.front_eq, String.front?_eq, hs, ha]

/-! ### Expressions -/

def wrapT (b : Bool) (ts : List Tok) : List Tok := if b then ts else .sym "(" :: ts ++ [.sym ")"]

/-- The tokens of a printed expression. -/
def toks : PExpr → List Tok
  | .base => [.kw "@base"]
  | .const n => [.int n]
  | .var s => [.ident s]
  | .binop op l r =>
    wrapT (Precedence.operandBare op l) (toks l) ++ .sym (opSym op) ::
      wrapT (Precedence.operandBare op r) (toks r)
  | .loadw sh a => .kw "lds" :: .int sh :: wrapT (Precedence.addressBare a) (toks a)
  | .loadb a => .kw "ld8" :: wrapT (Precedence.addressBare a) (toks a)
  | .shr l r => .sym "(" :: toks l ++ .sym ")" :: .sym ">>>" :: toks r
  | .shl l r => .sym "(" :: toks l ++ .sym ")" :: .sym "<<" :: toks r

/-- Every name of the expression is one the lexer reads as a name. -/
def Names : PExpr → Prop
  | .var s => IsName s
  | .binop _ l r | .shr l r | .shl l r => Names l ∧ Names r
  | .loadw _ a | .loadb a => Names a
  | .base | .const _ => True

theorem lex_close {cs : List Char} {ts : List Tok} (h : LexesTo cs ts) :
    LexesTo (cs ++ [')']) (ts ++ [.sym ")"]) :=
  h.cat (LexesAny.single (c := ')') (t := .sym ")") (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).to
    (by simp [Delim, delim]) (by simp)

theorem lex_paren {cs : List Char} {ts : List Tok} (h : LexesTo cs ts) :
    LexesTo ('(' :: cs ++ [')']) (.sym "(" :: ts ++ [.sym ")"]) :=
  lex_free' (c := '(') (t := .sym "(") (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (lex_close h)

theorem lex_wrap (b : Bool) {s : String} {ts : List Tok} (h : LexesTo s.toList ts) :
    LexesTo (if b then s else "(" ++ s ++ ")").toList (wrapT b ts) := by
  cases b
  · simpa [wrapT] using lex_paren h
  · simpa [wrapT] using h

theorem lex_op (op : POp) {rest : List Char} {ts : List Tok} (h : LexesTo rest ts) :
    LexesTo ((opSym op).toList ++ ' ' :: rest) (.sym (opSym op) :: ts) := by
  have free : ∀ c : Char, isSpace c = false → isDigit c = false → c ≠ '-' → c ≠ '/' →
      isSingleton c = true → symTok (String.singleton c) = some (.sym (String.singleton c)) →
      LexesTo (c :: ' ' :: rest) (.sym (String.singleton c) :: ts) :=
    fun c h0 h1 h2 h3 h4 h5 => lex_free' h0 h1 h2 h3 h4 h5 (lex_sp h)
  cases op
  · exact free '+' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact free '*' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact lex_then (lex_group (c := '<') (cs := []) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) h
  · exact lex_then (lex_group (c := '&') (cs := []) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) h
  · exact lex_then (lex_group (c := '=') (cs := ['=']) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) h
  · exact lex_then (lex_group (c := '<') (cs := ['=']) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) h
  · exact lex_minus.catTo h
  · exact free '^' (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  · exact lex_then (lex_group (c := '|') (cs := []) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)) h

theorem lex_shift {l r : List Char} {tl tr : List Tok} (hl : LexesTo l tl) (hr : LexesTo r tr)
    (c : Char) (cs : List Char) (s : String) (hc : beginsGroup c = true) (h0 : isSpace c = false)
    (h1 : isDigit c = false) (h2 : c ≠ '-') (h3 : c ≠ '/') (h4 : isSingleton c = false)
    (hcs : cs.all inGroup = true) (ht : symTok (String.ofList (c :: cs)) = some (.sym s)) :
    LexesTo ('(' :: (l ++ (')' :: ' ' :: (c :: cs ++ ' ' :: r))))
      (.sym "(" :: (tl ++ (.sym ")" :: .sym s :: tr))) := by
  refine lex_free' (c := '(') (t := .sym "(") (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ?_
  refine hl.cat (lex_free' (c := ')') (t := .sym ")") (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (lex_sp (lex_then (lex_group hc h0 h1 h2 h3 h4 hcs ht) hr)))
    (by simp [Delim, delim]) (by simp)

/-- **The printed expression lexes to its tokens.** -/
theorem lex_exp : ∀ e, Names e → LexesTo (ppExpr e).toList (toks e)
  | .base, _ => by
    simpa [ppExpr, toks] using lex_word (c := '@') (ws := ['b', 'a', 's', 'e']) (by decide)
      (by decide) (by decide)
  | .const n, _ => by simpa [ppExpr, toks] using lex_nat n
  | .var s, h => by simpa [ppExpr, toks] using lex_name h
  | .binop op l r, h => by
    have hl := lex_wrap (Precedence.operandBare op l) (lex_exp l h.1)
    have hr := lex_wrap (Precedence.operandBare op r) (lex_exp r h.2)
    have := hl.cat (lex_sp (lex_op op hr)) (by simp [Delim, delim]) (by simp)
    simpa [ppExpr, toks, Precedence.wrapOperand_eq] using this
  | .loadw sh a, h => by
    have ha := lex_wrap (Precedence.addressBare a) (lex_exp a h)
    have := lex_then (lex_word (c := 'l') (ws := ['d', 's']) (t := .kw "lds") (by decide)
      (by decide) (by decide)) (lex_then (lex_nat sh) ha)
    simpa [ppExpr, toks, Precedence.wrapAtom_eq] using this
  | .loadb a, h => by
    have ha := lex_wrap (Precedence.addressBare a) (lex_exp a h)
    have := lex_then (lex_word (c := 'l') (ws := ['d', '8']) (t := .kw "ld8") (by decide)
      (by decide) (by decide)) ha
    simpa [ppExpr, toks, Precedence.wrapAtom_eq] using this
  | .shr l r, h => by
    have := lex_shift (lex_exp l h.1) (lex_exp r h.2) '>' ['>', '>'] ">>>" (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simpa [ppExpr, toks] using this
  | .shl l r, h => by
    have := lex_shift (lex_exp l h.1) (lex_exp r h.2) '<' ['<'] "<<" (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    simpa [ppExpr, toks] using this

/-! ### Statements and functions -/

/-- A foreign function's name, which the lexer reads after `@` as one. -/
structure IsForeign (n : String) : Prop where
  word : ∃ c ws, n.toList = c :: ws ∧ (c :: ws).all isWordRest = true
  notKw : keywords.contains ("@" ++ n) = false

theorem lex_foreign {n : String} (h : IsForeign n) : LexesTo ('@' :: n.toList) [.foreign n] := by
  obtain ⟨c, ws, hs, hws⟩ := h.word
  rw [hs]
  refine lex_word (by decide) hws ?_
  have hl : String.ofList ('@' :: c :: ws) = "@" ++ n := by
    apply String.toList_inj.mp; simp [hs]
  have hd : ((("@" ++ n).drop 1).toString) = n := by
    apply String.toList_inj.mp; simp
  have hf : ("@" ++ n).front = '@' := by simp [String.front_eq, String.front?_eq]
  have hlen : 2 ≤ ("@" ++ n).length := by
    have : ("@" ++ n).toList.length = 2 + ws.length := by simp [hs]; omega
    rw [← String.length_toList]; omega
  rw [hl, wordTok, h.notKw]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [if_pos hf, if_pos hlen, hd]

def argToks : List PExpr → List Tok
  | [] => []
  | [a] => toks a
  | a :: as => toks a ++ .sym "," :: argToks as

mutual
/-- The tokens of a printed statement. -/
def stmtToks : PStmt → List Tok
  | .dec n v => .kw "var" :: .ident n :: .sym "=" :: toks v ++ [.sym ";"]
  | .assign n v => .ident n :: .sym "=" :: toks v ++ [.sym ";"]
  | .store a v => .kw "st" :: toks a ++ .sym "," :: toks v ++ [.sym ";"]
  | .storeb a v => .kw "st8" :: toks a ++ .sym "," :: toks v ++ [.sym ";"]
  | .ffi n args => .foreign n :: .sym "(" :: argToks args ++ [.sym ")", .sym ";"]
  | .call r f args =>
    .kw "var" :: .ident r :: .sym "=" :: .ident f :: .sym "(" :: argToks args ++ [.sym ")", .sym ";"]
  | .ret v => .kw "return" :: toks v ++ [.sym ";"]
  | .ite c t e =>
    .kw "if" :: toks c ++ .sym "{" :: stmtsToks t ++ .sym "}" :: .kw "else" :: .sym "{" ::
      stmtsToks e ++ [.sym "}"]
  | .while c b => .kw "while" :: toks c ++ .sym "{" :: stmtsToks b ++ [.sym "}"]
def stmtsToks : List PStmt → List Tok
  | [] => []
  | s :: ss => stmtToks s ++ stmtsToks ss
end

mutual
/-- Every name of the statement is one the lexer reads as a name. -/
def StmtNames : PStmt → Prop
  | .dec n v | .assign n v => IsName n ∧ Names v
  | .store a v | .storeb a v => Names a ∧ Names v
  | .ffi n args => IsForeign n ∧ ∀ a ∈ args, Names a
  | .call r f args => IsName r ∧ IsName f ∧ ∀ a ∈ args, Names a
  | .ret v => Names v
  | .ite c t e => Names c ∧ StmtsNames t ∧ StmtsNames e
  | .while c b => Names c ∧ StmtsNames b
def StmtsNames : List PStmt → Prop
  | [] => True
  | s :: ss => StmtNames s ∧ StmtsNames ss
end

/-- The text of lines, each ended by a newline. -/
def linesChars (ls : List String) : List Char := (ls.map fun l => l.toList ++ ['\n']).flatten

theorem linesChars_append (a b : List String) : linesChars (a ++ b) = linesChars a ++ linesChars b := by
  simp [linesChars]

theorem LexesAny.blank : ∀ (cs : List Char), cs.all (· = ' ') = true → LexesAny cs []
  | [], _ => LexesAny.nil
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1]
    exact (LexesAny.space (c := ' ') (by decide)).cat (LexesAny.blank cs h.2)

theorem lex_args : ∀ (args : List PExpr), (∀ a ∈ args, Names a) →
    LexesTo (String.intercalate ", " (args.map ppExpr)).toList (argToks args)
  | [], _ => by simpa [argToks] using LexesAny.nil.to
  | [a], h => by simpa [argToks] using lex_exp a (h a (by simp))
  | a :: b :: as, h => by
    have ha := lex_exp a (h a (by simp))
    have hr := lex_args (b :: as) (fun x hx => h x (List.mem_cons_of_mem a hx))
    have := ha.cat (lex_free' (c := ',') (t := .sym ",") (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (lex_sp hr)) (by simp [Delim, delim]) (by simp)
    simpa [argToks, String.intercalate_cons_cons] using this

/-- `;` and the line's end. -/
theorem lex_semi : LexesAny [';', '\n'] [.sym ";"] :=
  lex_free (c := ';') (t := .sym ";") (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (LexesAny.space (by decide))

theorem lex_kw {w : List Char} {t : Tok} (c : Char) (ws : List Char) (hw : w = c :: ws)
    (hc : startChar c = true) (hws : ws.all isWordRest = true)
    (ht : wordTok (String.ofList (c :: ws)) = some t) : LexesTo w [t] := by
  subst hw; exact lex_word hc hws ht

theorem lex_eqs {rest : List Char} {ts : List Tok} (h : LexesAny rest ts) :
    LexesAny ('=' :: ' ' :: rest) (.sym "=" :: ts) :=
  lex_thenAny (w := ['=']) (lex_group (c := '=') (cs := []) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)) h

theorem lex_brace : LexesAny ['{', '\n'] [.sym "{"] :=
  lex_free (c := '{') (t := .sym "{") (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (LexesAny.space (by decide))

theorem lex_closeLine : LexesAny ['}', '\n'] [.sym "}"] :=
  lex_free (c := '}') (t := .sym "}") (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (LexesAny.space (by decide))

theorem lex_callTail {args : List PExpr} (h : ∀ a ∈ args, Names a) :
    LexesAny ('(' :: ((String.intercalate ", " (args.map ppExpr)).toList ++ [')', ';', '\n']))
      (.sym "(" :: (argToks args ++ [.sym ")", .sym ";"])) :=
  lex_free (c := '(') (t := .sym "(") (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ((lex_args args h).catAny (lex_free (c := ')') (t := .sym ")") (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) lex_semi)
      (by simp [Delim, delim]) (by simp))

theorem lex_endSemi {v : PExpr} (h : Names v) :
    LexesAny ((ppExpr v).toList ++ [';', '\n']) (toks v ++ [.sym ";"]) :=
  (lex_exp v h).catAny lex_semi (by simp [Delim, delim]) (by simp)

mutual
/-- **A printed statement lexes to its tokens.** -/
theorem lex_stmt : ∀ (s : PStmt) (ind : String), StmtNames s → ind.toList.all (· = ' ') = true →
    LexesAny (linesChars (ppStmt ind s)) (stmtToks s)
  | .dec n v, ind, h, hi => by
    have := (LexesAny.blank _ hi).cat
      (lex_thenAny (lex_kw (t := .kw "var") 'v' ['a', 'r'] rfl (by decide) (by decide) (by decide))
        (lex_thenAny (lex_name h.1) (lex_eqs (lex_endSemi h.2))))
    simpa [ppStmt, linesChars, stmtToks] using this
  | .assign n v, ind, h, hi => by
    have := (LexesAny.blank _ hi).cat (lex_thenAny (lex_name h.1) (lex_eqs (lex_endSemi h.2)))
    simpa [ppStmt, linesChars, stmtToks] using this
  | .store a v, ind, h, hi => by
    have := (LexesAny.blank _ hi).cat
      (lex_thenAny (lex_kw (t := .kw "st") 's' ['t'] rfl (by decide) (by decide) (by decide))
        ((lex_exp a h.1).catAny (lex_free (c := ',') (t := .sym ",") (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (lex_spAny (lex_endSemi h.2)))
          (by simp [Delim, delim]) (by simp)))
    simpa [ppStmt, linesChars, stmtToks] using this
  | .storeb a v, ind, h, hi => by
    have := (LexesAny.blank _ hi).cat
      (lex_thenAny (lex_kw (t := .kw "st8") 's' ['t', '8'] rfl (by decide) (by decide) (by decide))
        ((lex_exp a h.1).catAny (lex_free (c := ',') (t := .sym ",") (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (lex_spAny (lex_endSemi h.2)))
          (by simp [Delim, delim]) (by simp)))
    simpa [ppStmt, linesChars, stmtToks] using this
  | .ffi n args, ind, h, hi => by
    have := (LexesAny.blank _ hi).cat ((lex_foreign h.1).catAny (lex_callTail h.2)
      (by simp [Delim, delim]) (by simp))
    simpa [ppStmt, linesChars, stmtToks] using this
  | .call r f args, ind, h, hi => by
    have := (LexesAny.blank _ hi).cat
      (lex_thenAny (lex_kw (t := .kw "var") 'v' ['a', 'r'] rfl (by decide) (by decide) (by decide))
        (lex_thenAny (lex_name h.1) (lex_eqs ((lex_name h.2.1).catAny (lex_callTail h.2.2)
          (by simp [Delim, delim]) (by simp)))))
    simpa [ppStmt, linesChars, stmtToks] using this
  | .ret v, ind, h, hi => by
    have := (LexesAny.blank _ hi).cat
      (lex_thenAny (lex_kw (t := .kw "return") 'r' ['e', 't', 'u', 'r', 'n'] rfl (by decide)
        (by decide) (by decide)) (lex_endSemi h))
    simpa [ppStmt, linesChars, stmtToks] using this
  | .ite c t e, ind, h, hi => by
    have hi' : (ind ++ "  ").toList.all (· = ' ') = true := by simpa using hi
    have l1 := (LexesAny.blank _ hi).cat
      (lex_thenAny (lex_kw (t := .kw "if") 'i' ['f'] rfl (by decide) (by decide) (by decide))
        ((lex_exp c h.1).catAny (lex_spAny lex_brace) (by simp [Delim, delim]) (by simp)))
    have l2 := (LexesAny.blank _ hi).cat (lex_free (c := '}') (t := .sym "}") (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (lex_spAny (lex_thenAny (lex_kw (t := .kw "else") 'e' ['l', 's', 'e'] rfl (by decide)
        (by decide) (by decide)) lex_brace)))
    have l3 := (LexesAny.blank _ hi).cat lex_closeLine
    have := ((((l1.cat (lex_stmts t (ind ++ "  ") h.2.1 hi')).cat l2).cat
      (lex_stmts e (ind ++ "  ") h.2.2 hi')).cat l3)
    simpa [ppStmt, linesChars, stmtToks] using this
  | .while c b, ind, h, hi => by
    have hi' : (ind ++ "  ").toList.all (· = ' ') = true := by simpa using hi
    have l1 := (LexesAny.blank _ hi).cat
      (lex_thenAny (lex_kw (t := .kw "while") 'w' ['h', 'i', 'l', 'e'] rfl (by decide) (by decide)
        (by decide)) ((lex_exp c h.1).catAny (lex_spAny lex_brace) (by simp [Delim, delim])
          (by simp)))
    have l3 := (LexesAny.blank _ hi).cat lex_closeLine
    have := (l1.cat (lex_stmts b (ind ++ "  ") h.2 hi')).cat l3
    simpa [ppStmt, linesChars, stmtToks] using this
theorem lex_stmts : ∀ (ss : List PStmt) (ind : String), StmtsNames ss →
    ind.toList.all (· = ' ') = true → LexesAny (linesChars (ppStmts ind ss)) (stmtsToks ss)
  | [], _, _, _ => by simpa [ppStmts, linesChars, stmtsToks] using LexesAny.nil
  | s :: ss, ind, h, hi => by
    have := (lex_stmt s ind h.1 hi).cat (lex_stmts ss ind h.2 hi)
    simpa [ppStmts, linesChars_append, stmtsToks] using this
end

def paramToks : List (Nat × String) → List Tok
  | [] => []
  | [p] => [.int p.1, .ident p.2]
  | p :: ps => .int p.1 :: .ident p.2 :: .sym "," :: paramToks ps

/-- The tokens of a printed function. -/
def funToks (f : PFun) : List Tok :=
  (if f.exported then [.kw "export"] else []) ++ .kw "fun" :: .ident f.name :: .sym "(" ::
    paramToks f.params ++ .sym ")" :: .sym "{" :: stmtsToks f.body ++ [.sym "}"]

/-- The names of the function are ones the lexer reads as names. -/
structure FunNames (f : PFun) : Prop where
  name : IsName f.name
  params : ∀ p ∈ f.params, IsName p.2
  body : StmtsNames f.body

theorem lex_params : ∀ (ps : List (Nat × String)), (∀ p ∈ ps, IsName p.2) →
    LexesTo (String.intercalate ", " (ps.map fun p => toString p.1 ++ " " ++ p.2)).toList
      (paramToks ps)
  | [], _ => by simpa [paramToks] using LexesAny.nil.to
  | [p], h => by
    have := lex_then (lex_nat p.1) (lex_name (h p (by simp)))
    simpa [paramToks] using this
  | p :: q :: ps, h => by
    have hp := lex_then (lex_nat p.1) (lex_name (h p (by simp)))
    have hr := lex_params (q :: ps) (fun x hx => h x (List.mem_cons_of_mem p hx))
    have := hp.cat (lex_free' (c := ',') (t := .sym ",") (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (lex_sp hr)) (by simp [Delim, delim]) (by simp)
    simpa [paramToks, String.intercalate_cons_cons] using this

theorem intercalate_lines : ∀ (ls : List String), ls ≠ [] →
    (String.intercalate "\n" ls ++ "\n").toList = linesChars ls
  | [], h => absurd rfl h
  | [l], _ => by simp [linesChars]
  | l :: m :: ls, _ => by
    have := intercalate_lines (m :: ls) (by simp)
    simp only [String.intercalate_cons_cons, String.toList_append] at this ⊢
    simp [linesChars] at this ⊢
    simp [this]

/-- **A printed function lexes to its tokens.** -/
theorem lex_fun (f : PFun) (h : FunNames f) : LexesAny (ppFun f).toList (funToks f) := by
  have head : LexesAny ((f.name).toList ++ '(' ::
      ((String.intercalate ", " (f.params.map fun p => toString p.1 ++ " " ++ p.2)).toList ++
        [')', ' ', '{', '\n'])) (.ident f.name :: .sym "(" :: (paramToks f.params ++
          [.sym ")", .sym "{"])) :=
    (lex_name h.name).catAny (lex_free (c := '(') (t := .sym "(") (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) ((lex_params f.params h.params).catAny
        (lex_free (c := ')') (t := .sym ")") (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (lex_spAny lex_brace)) (by simp [Delim, delim]) (by simp)))
      (by simp [Delim, delim]) (by simp)
  have hfun := lex_thenAny (lex_kw (t := .kw "fun") 'f' ['u', 'n'] rfl (by decide) (by decide)
    (by decide)) head
  have hkw : LexesAny ((if f.exported then "export fun " else "fun ").toList ++
      ((f.name).toList ++ '(' :: ((String.intercalate ", " (f.params.map fun p =>
        toString p.1 ++ " " ++ p.2)).toList ++ [')', ' ', '{', '\n'])))
      ((if f.exported then [.kw "export"] else []) ++ .kw "fun" :: .ident f.name :: .sym "(" ::
        (paramToks f.params ++ [.sym ")", .sym "{"])) := by
    cases f.exported
    · simpa using hfun
    · have := lex_thenAny (lex_kw (t := .kw "export") 'e' ['x', 'p', 'o', 'r', 't'] rfl (by decide)
        (by decide) (by decide)) hfun
      simpa using this
  have body := lex_stmts f.body "  " h.body (by decide)
  have := (hkw.cat body).cat lex_closeLine
  rw [ppFun, intercalate_lines _ (by simp)]
  simpa [linesChars, linesChars_append, funToks] using this

theorem lex_funs : ∀ (fs : List PFun), (∀ f ∈ fs, FunNames f) →
    LexesAny (String.intercalate "\n" (fs.map ppFun)).toList (fs.flatMap funToks)
  | [], _ => by simpa using LexesAny.nil
  | [f], h => by simpa using lex_fun f (h f (by simp))
  | f :: g :: fs, h => by
    have hf := lex_fun f (h f (by simp))
    have hr := lex_funs (g :: fs) (fun x hx => h x (List.mem_cons_of_mem f hx))
    have := (hf.cat (LexesAny.space (c := '\n') (by decide))).cat hr
    simp only [List.map_cons, String.intercalate_cons_cons, String.toList_append,
      List.flatMap_cons] at this ⊢
    simpa using this

/-- **The lexer reads a printed program as its tokens.** -/
theorem lex_program (fs : List PFun) (h : ∀ f ∈ fs, FunNames f) :
    lex (String.intercalate "\n" (fs.map ppFun)) = some (fs.flatMap funToks) := by
  have := lex_funs fs h []
  rw [List.append_nil] at this
  rw [lex, this]
  simp [lexChars]

/-! ## The grammar on the printer's tokens

### Each level, as the parser takes it -/

theorem pAt_zero {L : Level} {ts : List Tok} : pAt 0 L ts = none := by rw [pAt.eq_def]

theorem pAt_eq_one {k : Nat} {ts rest : List Tok} {a : Exp} (h : pAt k .cmp ts = some (a, rest))
    (hr : ∀ r, rest ≠ .sym "==" :: r) : pAt (k + 1) .eq ts = some (a, rest) := by
  rw [pAt.eq_def]; simp only [h, Option.bind_eq_bind, Option.bind_some]
  first | rfl | (split <;> simp_all)

theorem pAt_eq_two {k : Nat} {ts r r' : List Tok} {a b : Exp}
    (h : pAt k .cmp ts = some (a, .sym "==" :: r)) (h2 : pAt k .cmp r = some (b, r')) :
    pAt (k + 1) .eq ts = some (.cmp "Equal" a b, r') := by
  rw [pAt.eq_def]; simp [h, h2]

theorem pAt_cmp_one {k : Nat} {ts rest : List Tok} {a : Exp} (h : pAt k .lds ts = some (a, rest))
    (hr : ∀ s r, rest = .sym s :: r → cmpOf s = none) : pAt (k + 1) .cmp ts = some (a, rest) := by
  rw [pAt.eq_def]; simp only [h, Option.bind_eq_bind, Option.bind_some]
  first | rfl | (split <;> simp_all)

theorem pAt_cmp_two {k : Nat} {ts r r' : List Tok} {a b : Exp} {s : String} {c : String × Bool}
    (h : pAt k .lds ts = some (a, .sym s :: r)) (hc : cmpOf s = some c)
    (h2 : pAt k .lds r = some (b, r')) : pAt (k + 1) .cmp ts = some (comparison c a b, r') := by
  rw [pAt.eq_def]; simp [h, h2, hc]

theorem pAt_lds_pass {k : Nat} {ts : List Tok} (h : ts.head? ≠ some (.kw "lds")) :
    pAt (k + 1) .lds ts = pAt k .ld8 ts := by
  rw [pAt.eq_def]; simp only
  split
  · simp at h
  · simp at h
  · rfl

theorem pAt_lds {k : Nat} {ts : List Tok} :
    pAt (k + 1) .lds (.kw "lds" :: .int 1 :: ts) = (pAt k .ld8 ts).map fun r => (.load r.1, r.2) := by
  rw [pAt.eq_def]; simp only
  cases pAt k .ld8 ts <;> rfl

theorem pAt_ld8_pass {k : Nat} {ts : List Tok} (h : ts.head? ≠ some (.kw "ld8")) :
    pAt (k + 1) .ld8 ts = pAt k .or_ ts := by
  rw [pAt.eq_def]; simp only
  split
  · simp at h
  · rfl

theorem pAt_ld8 {k : Nat} {ts : List Tok} :
    pAt (k + 1) .ld8 (.kw "ld8" :: ts) = (pAt k .or_ ts).map fun r => (.loadByte r.1, r.2) := by
  rw [pAt.eq_def]; simp only
  cases pAt k .or_ ts <;> rfl

theorem pAt_shift {k : Nat} {ts : List Tok} :
    pAt (k + 1) .shift ts = (pAt k .add ts).bind fun r => shiftChain k r.1 r.2 := by
  rw [pAt.eq_def]; simp only
  cases pAt k .add ts <;> rfl

theorem pAt_chain {k : Nat} {L : Level} {ts : List Tok}
    (hL : L = .or_ ∨ L = .xor ∨ L = .and_ ∨ L = .add ∨ L = .mul) :
    pAt (k + 1) L ts = (pAt k L.next ts).bind fun r => chain k L r.1 r.2 := by
  rw [pAt.eq_def]
  rcases hL with rfl | rfl | rfl | rfl | rfl <;> simp only <;> cases pAt k _ ts <;> rfl

theorem pAt_paren {k : Nat} {ts rest : List Tok} {e : Exp} (h : pAt k .eq ts = some (e, .sym ")" :: rest)) :
    pAt (k + 1) .base (.sym "(" :: ts) = some (e, rest) := by
  rw [pAt.eq_def]; simp [h]

theorem pAt_int {k n : Nat} {rest : List Tok} :
    pAt (k + 1) .base (.int n :: rest) = some (.const (word n), rest) := by
  rw [pAt.eq_def]

theorem pAt_baseAddr {k : Nat} {rest : List Tok} :
    pAt (k + 1) .base (.kw "@base" :: rest) = some (.base, rest) := by
  rw [pAt.eq_def]; simp

theorem pAt_ident {k : Nat} {v : String} {rest : List Tok}
    (h : ∀ y r, rest ≠ .sym "<" :: .ident y :: .sym "=" :: r) :
    pAt (k + 1) .base (.ident v :: rest) = some (.var false v, rest) := by
  rw [pAt.eq_def]; simp only
  first | done | (split <;> simp_all)

theorem chain_step {k : Nat} {L : Level} {res e : Exp} {s : String} {f : Exp → Exp → Exp}
    {ts r : List Tok} (hs : step L s = some f) (h : pAt k L.next ts = some (e, r)) :
    chain (k + 1) L res (.sym s :: ts) = chain k L (f res e) r := by
  rw [chain.eq_def]; simp [hs, h]

theorem chain_stop {k : Nat} {L : Level} {res : Exp} {ts : List Tok}
    (h : ∀ s r, ts = .sym s :: r → step L s = none) : chain (k + 1) L res ts = some (res, ts) := by
  rw [chain.eq_def]
  split <;> simp_all

theorem shift_step {k n : Nat} {res : Exp} {s sh : String} {ts : List Tok}
    (hs : shiftOf s = some sh) :
    shiftChain (k + 1) res (.sym s :: .int n :: ts) = shiftChain k (.shift sh res n) ts := by
  rw [shiftChain.eq_def]; simp [hs]

theorem shift_stop {k : Nat} {res : Exp} {ts : List Tok}
    (h : ∀ s n r, ts = .sym s :: .int n :: r → shiftOf s = none) :
    shiftChain (k + 1) res ts = some (res, ts) := by
  rw [shiftChain.eq_def]
  split <;> simp_all

/-! ### What may follow an expression, and climbing the levels -/

def _root_.DN.Compiler.Parse.Level.idx : Level → Nat
  | .eq => 0 | .cmp => 1 | .lds => 2 | .ld8 => 3 | .or_ => 4 | .xor => 5 | .and_ => 6
  | .shift => 7 | .add => 8 | .mul => 9 | .base => 10

/-- The level an operator token belongs to. -/
def opIdx : Tok → Option Nat
  | .sym "==" => some 0 | .sym "<" => some 1 | .sym "<=" => some 1 | .sym "|" => some 4
  | .sym "^" => some 5 | .sym "&" => some 6 | .sym "<<" => some 7 | .sym ">>>" => some 7
  | .sym "+" => some 8 | .sym "-" => some 8 | .sym "*" => some 9 | _ => none

/-- What may follow an expression read at level `L`: no operator of `L` or a level below it, no
`=`, and no `< name =`, which `EBaseNT` would take for a structure. -/
def Follows (L : Level) : List Tok → Prop
  | [] => True
  | t :: rest => (∀ n, opIdx t = some n → n < L.idx) ∧ t ≠ .sym "=" ∧
      (t = .sym "<" → ∀ y r, rest ≠ .ident y :: .sym "=" :: r)

theorem Follows.mono {L M : Level} : ∀ {rest : List Tok}, Follows L rest → L.idx ≤ M.idx →
    Follows M rest
  | [], _, _ => trivial
  | _ :: _, h, hle => ⟨fun n hn => Nat.lt_of_lt_of_le (h.1 n hn) hle, h.2.1, h.2.2⟩

theorem Follows.noStruct {L : Level} {rest : List Tok} (h : Follows L rest) :
    ∀ y r, rest ≠ .sym "<" :: .ident y :: .sym "=" :: r := by
  intro y r hr; subst hr; exact h.2.2 rfl y r rfl

/-- A token that is no operator, no `=` and no `<` may follow anything. -/
theorem Follows.stop {L : Level} {t : Tok} {rest : List Tok} (h1 : opIdx t = none)
    (h2 : t ≠ .sym "=") (h3 : t ≠ .sym "<") : Follows L (t :: rest) :=
  ⟨fun n hn => (by rw [h1] at hn; cases hn), h2, fun h => absurd h h3⟩

theorem idx_next {L : Level} (h : L ≠ .base) : L.next.idx = L.idx + 1 := by
  cases L <;> first | rfl | exact absurd rfl h

theorem idx_inj {L M : Level} (h : L.idx = M.idx) : L = M := by
  cases L <;> cases M <;> first | rfl | (simp [Level.idx] at h)

theorem idx_le (L : Level) : L.idx ≤ 10 := by cases L <;> decide

theorem cmpOf_some {s : String} {c : String × Bool} (h : cmpOf s = some c) :
    opIdx (.sym s) = some 1 := by
  unfold cmpOf at h; split at h <;> simp_all [opIdx]

theorem shiftOf_some {s sh : String} (h : shiftOf s = some sh) : opIdx (.sym s) = some 7 := by
  unfold shiftOf at h; split at h <;> simp_all [opIdx]

theorem step_some {L : Level} {s : String} {f : Exp → Exp → Exp} (h : step L s = some f) :
    opIdx (.sym s) = some L.idx ∧ s ≠ "=" ∧ s ≠ "<" ∧ L ≠ .base := by
  unfold step at h; split at h <;> simp_all [opIdx, Level.idx]

/-- One level up: what was read at the level below is read alike when nothing that follows
belongs to this level. -/
theorem climb1 {L : Level} (hL : L ≠ .base) {k : Nat} {ts rest : List Tok} {e : Exp}
    (h : pAt k L.next ts = some (e, rest)) (hf : Follows L rest)
    (hlds : L = .lds → ts.head? ≠ some (.kw "lds")) (hld8 : L = .ld8 → ts.head? ≠ some (.kw "ld8")) :
    pAt (k + 1) L ts = some (e, rest) := by
  cases k with
  | zero => rw [pAt_zero] at h; cases h
  | succ j =>
    have stopChain : ∀ s r, rest = .sym s :: r → step L s = none := by
      intro s r hr
      cases hs : step L s with
      | none => rfl
      | some f =>
        have := (step_some hs).1; subst hr
        have := hf.1 _ this; omega
    cases L <;> simp only [Level.next] at h
    case eq =>
      refine pAt_eq_one h fun r hr => ?_
      subst hr; have := hf.1 0 rfl; simp [Level.idx] at this
    case cmp =>
      refine pAt_cmp_one h fun s r hr => ?_
      cases hc : cmpOf s with
      | none => rfl
      | some c => subst hr; have := hf.1 _ (cmpOf_some hc); simp [Level.idx] at this
    case lds => rw [pAt_lds_pass (hlds rfl)]; exact h
    case ld8 => rw [pAt_ld8_pass (hld8 rfl)]; exact h
    case shift =>
      rw [pAt_shift, h]
      refine shift_stop fun s n r hr => ?_
      cases hc : shiftOf s with
      | none => rfl
      | some c => subst hr; have := hf.1 _ (shiftOf_some hc); simp [Level.idx] at this
    case or_ => rw [pAt_chain (by simp)]; simp only [Level.next, h]; exact chain_stop stopChain
    case xor => rw [pAt_chain (by simp)]; simp only [Level.next, h]; exact chain_stop stopChain
    case and_ => rw [pAt_chain (by simp)]; simp only [Level.next, h]; exact chain_stop stopChain
    case add => rw [pAt_chain (by simp)]; simp only [Level.next, h]; exact chain_stop stopChain
    case mul => rw [pAt_chain (by simp)]; simp only [Level.next, h]; exact chain_stop stopChain
    case base => exact absurd rfl hL

/-- Up any number of levels, when the tokens do not start with a load the levels passed read. -/
theorem climb {M : Level} {k : Nat} {ts rest : List Tok} {e : Exp}
    (h : pAt k M ts = some (e, rest))
    (hhd : ts.head? ≠ some (.kw "lds") ∨ M.idx ≤ 2)
    (hhd8 : ts.head? ≠ some (.kw "ld8") ∨ M.idx ≤ 3) :
    ∀ (d : Nat) (L : Level), L.idx + d = M.idx → Follows L rest →
      pAt (k + d) L ts = some (e, rest)
  | 0, L, hd, hf => by
    rw [Nat.add_zero] at hd ⊢; rw [idx_inj hd]; exact h
  | d + 1, L, hd, hf => by
    have hL : L ≠ .base := by
      intro hb; subst hb; have := idx_le M; have : Level.base.idx = 10 := rfl; omega
    have hn := idx_next hL
    have ih := climb h hhd hhd8 d L.next (by omega) (hf.mono (by omega))
    rw [← Nat.add_assoc]
    refine climb1 hL ih hf ?_ ?_
    · intro hl; subst hl; rcases hhd with hhd | hhd
      · exact hhd
      · have : Level.lds.idx = 2 := rfl; omega
    · intro hl; subst hl; rcases hhd8 with hhd8 | hhd8
      · exact hhd8
      · have : Level.ld8.idx = 3 := rfl; omega

/-! ### The tree of a printed expression -/

def isAtom : PExpr → Bool
  | .const _ | .var _ | .base => true
  | _ => false

/-- The tokens of an expression where only an atom stands bare. -/
def toksU (e : PExpr) : List Tok := wrapT (isAtom e) (toks e)

/-- The operands of a chain the printer leaves bare: those of an associative operator. -/
def units (op : POp) : PExpr → List PExpr
  | .binop o l r => if o = op ∧ isAssoc op = true then units op l ++ units op r else [.binop o l r]
  | e => [e]

/-- Operands, each printed as `toksU` does, between an operator's symbol. -/
def toksJoin (s : String) : List PExpr → List Tok
  | [] => []
  | u :: us => toksU u ++ us.flatMap fun u => .sym s :: toksU u

theorem units_ne_nil (op : POp) : ∀ e, units op e ≠ []
  | .binop o l r => by
    unfold units; split
    · exact fun h => units_ne_nil op l (List.append_eq_nil_iff.mp h).1
    · simp
  | .base | .const _ | .var _ | .loadw _ _ | .loadb _ | .shr _ _ | .shl _ _ => by simp [units]

theorem toksJoin_append (s : String) :
    ∀ (xs ys : List PExpr), xs ≠ [] → ys ≠ [] →
      toksJoin s (xs ++ ys) = toksJoin s xs ++ .sym s :: toksJoin s ys
  | [], _, h, _ => absurd rfl h
  | _, [], _, h => absurd rfl h
  | x :: xs, y :: ys, _, _ => by simp [toksJoin]

theorem operand_toks (op : POp) : ∀ x,
    wrapT (Precedence.operandBare op x) (toks x) = toksJoin (opSym op) (units op x)
  | .binop o a b => by
    by_cases h : o = op ∧ isAssoc op = true
    · obtain ⟨rfl, ha⟩ := h
      have hb : Precedence.operandBare o (.binop o a b) = true := by
        simp [Precedence.operandBare, ha]
      rw [hb, units, if_pos ⟨rfl, ha⟩, toksJoin_append _ _ _ (units_ne_nil _ _) (units_ne_nil _ _),
        ← operand_toks o a, ← operand_toks o b]
      simp [wrapT, toks]
    · have hb : Precedence.operandBare op (.binop o a b) = false := by
        simp only [Precedence.operandBare, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
        by_cases hc : isAssoc op = true
        · exact Or.inr fun he => h ⟨he.symm, hc⟩
        · exact Or.inl (by simpa using hc)
      rw [hb, units, if_neg h]
      simp [toksJoin, toksU, isAtom]
  | .base | .const _ | .var _ => by simp [Precedence.operandBare, units, toksJoin, toksU, isAtom]
  | .loadw _ _ | .loadb _ | .shr _ _ | .shl _ _ => by
    simp [Precedence.operandBare, units, toksJoin, toksU, isAtom]

theorem toks_binop (op : POp) (l r : PExpr) :
    toks (.binop op l r) = toksJoin (opSym op) (units op l ++ units op r) := by
  rw [toksJoin_append _ _ _ (units_ne_nil _ _) (units_ne_nil _ _), ← operand_toks, ← operand_toks]
  rfl

/-- The operands a chain's tree of `o` holds. -/
def opsOf (o : String) : Exp → List Exp
  | .op b es => if b = o then es else [.op b es]
  | e => [e]

/-- The operands of a product, which nests to the left. -/
def mulOps : Exp → List Exp
  | .mul [x, y] => mulOps x ++ [y]
  | e => [e]

def mulTree : List Exp → Exp
  | [] => .const 0
  | t :: ts => ts.foldl (fun r e => .mul [r, e]) t

def distance : PExpr → Nat
  | .const n => n
  | _ => 0

/-- **The tree the parser builds of a printed expression**, its names not yet made local. -/
def tree : PExpr → Exp
  | .base => .base
  | .const n => .const (word n)
  | .var s => .var false s
  | .binop .add l r => .op "Add" (opsOf "Add" (tree l) ++ opsOf "Add" (tree r))
  | .binop .xor l r => .op "Xor" (opsOf "Xor" (tree l) ++ opsOf "Xor" (tree r))
  | .binop .or_ l r => .op "Or" (opsOf "Or" (tree l) ++ opsOf "Or" (tree r))
  | .binop .and_ l r => joined "And" (tree l) (tree r)
  | .binop .sub l r => .op "Sub" [tree l, tree r]
  | .binop .mul l r => mulTree (mulOps (tree l) ++ mulOps (tree r))
  | .binop .lt l r => .cmp "Less" (tree l) (tree r)
  | .binop .le l r => .cmp "NotLess" (tree r) (tree l)
  | .binop .eq l r => .cmp "Equal" (tree l) (tree r)
  | .loadw _ a => .load (tree a)
  | .loadb a => .loadByte (tree a)
  | .shr l r => .shift "Lsr" (tree l) (distance r)
  | .shl l r => .shift "Lsl" (tree l) (distance r)

/-- The name of an associative operator's chain. -/
def chainName : POp → String
  | .add => "Add" | .xor => "Xor" | .or_ => "Or" | _ => ""

theorem joined_op {o : String} (ho : o ≠ "Sub") (es : List Exp) (e : Exp) :
    joined o (.op o es) e = .op o (es ++ [e]) := by
  simp [joined, ho]

theorem joined_fresh {o : String} {res : Exp} (h : ∀ es, res ≠ .op o es) (e : Exp) :
    joined o res e = .op o [res, e] := by
  unfold joined; split
  · rename_i b es
    have hb : b ≠ o := fun hb => h es (by rw [hb])
    simp [hb]
  · rfl

theorem fold_joined {o : String} (ho : o ≠ "Sub") :
    ∀ (ts es : List Exp), ts.foldl (joined o) (.op o es) = .op o (es ++ ts)
  | [], es => by simp
  | t :: ts, es => by
    simp only [List.foldl_cons, joined_op ho, fold_joined ho ts]; simp

theorem joined_isOp (o : String) (res e : Exp) : ∃ es, joined o res e = .op o es := by
  unfold joined; split
  · rename_i b es; split
    · exact ⟨_, rfl⟩
    · rename_i h; simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h
      exact ⟨_, by rw [show b = o from Classical.not_not.mp h.1]⟩
  · exact ⟨_, rfl⟩

theorem mulOps_ne_nil : ∀ e, mulOps e ≠ []
  | .mul [x, _] => by simp [mulOps]
  | .const _ | .var _ _ | .base | .op _ _ | .cmp _ _ _ | .shift _ _ _ | .load _ | .loadByte _ => by
    simp [mulOps]
  | .mul [] | .mul [_] | .mul (_ :: _ :: _ :: _) => by simp [mulOps]

theorem foldl_mul_isMul : ∀ (ts : List Exp) (t : Exp), ts ≠ [] →
    ∃ a b, ts.foldl (fun r e => .mul [r, e]) t = .mul [a, b]
  | [], _, h => absurd rfl h
  | [x], t, _ => ⟨t, x, rfl⟩
  | x :: y :: ts, t, _ => foldl_mul_isMul (y :: ts) (.mul [t, x]) (by simp)

theorem tree_mul_isMul (l r : PExpr) : ∃ a b, tree (.binop .mul l r) = .mul [a, b] := by
  simp only [tree]
  cases hl : mulOps (tree l) with
  | nil => exact absurd hl (mulOps_ne_nil _)
  | cons t ts =>
    cases hr : mulOps (tree r) with
    | nil => exact absurd hr (mulOps_ne_nil _)
    | cons u us => exact foldl_mul_isMul _ t (by simp)

/-- A tree of `o` is that of a chain of the matching operator. -/
theorem tree_op_name {op : POp} (hop : op = .add ∨ op = .xor ∨ op = .or_) :
    ∀ x, (∃ es, tree x = .op (chainName op) es) → ∃ l r, x = .binop op l r
  | .binop o l r, ⟨es, h⟩ => by
    cases o
    case mul =>
      obtain ⟨a, b, hm⟩ := tree_mul_isMul l r; rw [hm] at h; cases h
    case and_ =>
      obtain ⟨es', hj⟩ := joined_isOp "And" (tree l) (tree r)
      simp only [tree, hj] at h; rcases hop with rfl | rfl | rfl <;> simp [chainName] at h
    all_goals rcases hop with rfl | rfl | rfl <;> first | exact ⟨l, r, rfl⟩ | simp [tree, chainName] at h
  | .base, ⟨_, h⟩ | .const _, ⟨_, h⟩ | .var _, ⟨_, h⟩ | .loadw _ _, ⟨_, h⟩ | .loadb _, ⟨_, h⟩
  | .shr _ _, ⟨_, h⟩ | .shl _ _, ⟨_, h⟩ => by simp [tree] at h

theorem tree_isMul : ∀ x, (∃ a b, tree x = .mul [a, b]) → ∃ l r, x = .binop .mul l r
  | .binop o l r, ⟨a, b, h⟩ => by
    cases o
    case mul => exact ⟨l, r, rfl⟩
    case and_ =>
      obtain ⟨es', hj⟩ := joined_isOp "And" (tree l) (tree r)
      simp only [tree, hj] at h; cases h
    all_goals simp [tree] at h
  | .base, ⟨_, _, h⟩ | .const _, ⟨_, _, h⟩ | .var _, ⟨_, _, h⟩ | .loadw _ _, ⟨_, _, h⟩
  | .loadb _, ⟨_, _, h⟩ | .shr _ _, ⟨_, _, h⟩ | .shl _ _, ⟨_, _, h⟩ => by simp [tree] at h

theorem isAssoc_chain {op : POp} (hop : op = .add ∨ op = .xor ∨ op = .or_) : isAssoc op = true := by
  rcases hop with rfl | rfl | rfl <;> rfl

/-- What a unit of a chain is not: a chain of the same operator. -/
theorem units_mem {op : POp} (ha : isAssoc op = true) :
    ∀ x u, u ∈ units op x → ∀ l r, u ≠ .binop op l r
  | .binop o a b, u, hu, l, r, he => by
    unfold units at hu; split at hu
    · rcases List.mem_append.mp hu with h | h
      · exact units_mem ha a u h l r he
      · exact units_mem ha b u h l r he
    · rename_i hn; simp at hu; subst hu; cases he; exact hn ⟨rfl, ha⟩
  | .base, u, hu, l, r, he | .const _, u, hu, l, r, he | .var _, u, hu, l, r, he
  | .loadw _ _, u, hu, l, r, he | .loadb _, u, hu, l, r, he | .shr _ _, u, hu, l, r, he
  | .shl _ _, u, hu, l, r, he => by simp [units] at hu; subst hu; cases he

theorem units_size {op : POp} : ∀ x u, u ∈ units op x → sizeOf u ≤ sizeOf x
  | .binop o a b, u, hu => by
    unfold units at hu; split at hu
    · rcases List.mem_append.mp hu with h | h
      · have := units_size a u h; simp; omega
      · have := units_size b u h; simp; omega
    · simp at hu; subst hu; exact Nat.le_refl _
  | .base, u, hu | .const _, u, hu | .var _, u, hu | .loadw _ _, u, hu | .loadb _, u, hu
  | .shr _ _, u, hu | .shl _ _, u, hu => by simp [units] at hu; subst hu; exact Nat.le_refl _

theorem tree_chain {op : POp} (hop : op = .add ∨ op = .xor ∨ op = .or_) (l r : PExpr) :
    tree (.binop op l r) = .op (chainName op) (opsOf (chainName op) (tree l) ++
      opsOf (chainName op) (tree r)) := by
  rcases hop with rfl | rfl | rfl <;> rfl

theorem opsOf_tree {op : POp} (hop : op = .add ∨ op = .xor ∨ op = .or_) :
    ∀ x, opsOf (chainName op) (tree x) = (units op x).map tree
  | .binop o a b => by
    by_cases h : o = op
    · subst h
      rw [tree_chain hop, units, if_pos ⟨rfl, isAssoc_chain hop⟩, List.map_append,
        ← opsOf_tree hop a, ← opsOf_tree hop b]
      simp [opsOf]
    · have hn : ∀ es, tree (.binop o a b) ≠ .op (chainName op) es := by
        intro es he
        obtain ⟨l, r, hx⟩ := tree_op_name hop _ ⟨es, he⟩
        cases hx; exact h rfl
      have hu : units op (.binop o a b) = [.binop o a b] := by
        rw [units, if_neg fun hh => h hh.1]
      rw [hu, List.map_cons, List.map_nil]
      generalize tree (.binop o a b) = t at hn ⊢
      cases t with
      | op b' es => simp only [opsOf]; rw [if_neg]; intro hb; subst hb; exact hn es rfl
      | _ => rfl
  | .base | .const _ | .var _ | .loadw _ _ | .loadb _ | .shr _ _ | .shl _ _ => by
    simp [units, tree, opsOf]

theorem mulOps_fold : ∀ (ts : List Exp) (r : Exp),
    mulOps (ts.foldl (fun r e => .mul [r, e]) r) = mulOps r ++ ts
  | [], r => by simp
  | t :: ts, r => by simp only [List.foldl_cons, mulOps_fold ts]; simp [mulOps]

theorem mulOps_tree : ∀ x, mulOps (tree x) = (units .mul x).map tree
  | .binop o a b => by
    by_cases h : o = .mul
    · subst h
      have hu := units_ne_nil .mul a
      cases hua : units .mul a with
      | nil => exact absurd hua hu
      | cons u us =>
        have hnm : ∀ l r, u ≠ .binop .mul l r :=
          units_mem (op := .mul) rfl a u (by rw [hua]; simp)
        have hmu : mulOps (tree u) = [tree u] := by
          cases ht : tree u with
          | mul es =>
            match es, ht with
            | [x, y], ht => obtain ⟨l, r, hx⟩ := tree_isMul u ⟨x, y, ht⟩; exact absurd hx (hnm l r)
            | [], _ | [_], _ | _ :: _ :: _ :: _, _ => simp [mulOps]
          | _ => simp [mulOps]
        simp only [tree, mulOps_tree a, mulOps_tree b, hua, units, List.map_cons,
          List.cons_append, mulTree, mulOps_fold, hmu]
        simp [isAssoc]
    · have hn : ∀ x y, tree (.binop o a b) ≠ .mul [x, y] := by
        intro x y he
        obtain ⟨l, r, hx⟩ := tree_isMul _ ⟨x, y, he⟩
        cases hx; exact h rfl
      rw [units, if_neg fun hh => h hh.1, List.map_cons, List.map_nil]
      generalize tree (.binop o a b) = t at hn ⊢
      cases t with
      | mul es =>
        match es, hn with
        | [x, y], hn => exact absurd rfl (hn x y)
        | [], _ | [_], _ | _ :: _ :: _ :: _, _ => rfl
      | _ => rfl
  | .base | .const _ | .var _ | .loadw _ _ | .loadb _ | .shr _ _ | .shl _ _ => by
    simp [units, tree, mulOps]

/-! ### Chains -/

/-- The operator and operand after the first of a chain. -/
def restToks (s : String) (us : List PExpr) : List Tok := us.flatMap fun u => .sym s :: toksU u

theorem toksJoin_cons (s : String) (u : PExpr) (us : List PExpr) :
    toksJoin s (u :: us) = toksU u ++ restToks s us := rfl

theorem rest_toks_cons (s : String) (u : PExpr) (us : List PExpr) :
    restToks s (u :: us) = .sym s :: (toksU u ++ restToks s us) := by simp [restToks]

/-- **A chain's operators and operands**, each operand read a level below, as the parser takes
them. -/
theorem chain_units {L : Level} {s : String} {f : Exp → Exp → Exp} (hs : step L s = some f)
    (us : List PExpr)
    (hu : ∀ u ∈ us, ∀ (rest : List Tok), Follows L.next rest → ∀ (k : Nat),
      12 * (toksU u).length + 12 ≤ k → pAt k L.next (toksU u ++ rest) = some (tree u, rest)) :
    ∀ (res : Exp) (rest : List Tok), Follows L rest → ∀ k, 12 * (restToks s us).length + 1 ≤ k →
      chain k L res (restToks s us ++ rest) = some (us.foldl (fun r u => f r (tree u)) res, rest) := by
  obtain ⟨hidx, hs1, hs2, hL⟩ := step_some hs
  have hn := idx_next hL
  induction us with
  | nil =>
    intro res rest hf k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    refine chain_stop fun s' r hr => ?_
    cases hs' : step L s' with
    | none => rfl
    | some f' => subst hr; have := hf.1 _ (step_some hs').1; omega
  | cons u us ih =>
    intro res rest hf k hk
    have hlen : (restToks s (u :: us)).length = 1 + (toksU u).length + (restToks s us).length := by
      rw [rest_toks_cons]; simp; omega
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hf' : Follows L.next (restToks s us ++ rest) := by
      cases us with
      | nil => exact hf.mono (by omega)
      | cons v vs =>
        simp only [restToks, List.flatMap_cons, List.cons_append]
        exact ⟨fun n h => by rw [hidx] at h; cases h; omega, by simpa using hs1,
          fun h => absurd (Tok.sym.inj h) hs2⟩
    have hp := hu u (by simp) _ hf' j (by omega)
    have := chain_step (res := res) hs hp
    rw [rest_toks_cons, List.cons_append, List.append_assoc, this, List.foldl_cons]
    exact ih (fun v hv => hu v (by simp [hv])) _ rest hf j (by omega)

theorem fold_chain {o : String} (ho : o ≠ "Sub") {t : Exp} (ht : ∀ es, t ≠ .op o es)
    (u : PExpr) (us : List PExpr) :
    (u :: us).foldl (fun r v => joined o r (tree v)) t = .op o (t :: (u :: us).map tree) := by
  simp only [List.foldl_cons, joined_fresh ht]
  have := fold_joined ho (us.map tree) [t, tree u]
  rw [List.foldl_map] at this
  rw [this]; simp

theorem fold_mul (t : Exp) (us : List PExpr) :
    us.foldl (fun r v => .mul [r, tree v]) t = mulTree (t :: us.map tree) := by
  simp only [mulTree]
  rw [List.foldl_map]

/-! ### Every printed expression the gate accepts reads as its tree -/

/-- The gate's shapes: loads of one word, shifts by a literal. -/
def Shape : PExpr → Prop
  | .binop _ l r => Shape l ∧ Shape r
  | .loadw sh a => sh = 1 ∧ Shape a
  | .loadb a => Shape a
  | .shr l r | .shl l r => (∃ n, r = .const n) ∧ Shape l
  | .base | .const _ | .var _ => True

/-- The level an expression's head belongs to. -/
def native : PExpr → Level
  | .binop .add _ _ | .binop .sub _ _ => .add
  | .binop .mul _ _ => .mul
  | .binop .and_ _ _ => .and_
  | .binop .xor _ _ => .xor
  | .binop .or_ _ _ => .or_
  | .binop .lt _ _ | .binop .le _ _ => .cmp
  | .binop .eq _ _ => .eq
  | .loadw _ _ => .lds
  | .loadb _ => .ld8
  | .shr _ _ | .shl _ _ => .shift
  | .base | .const _ | .var _ => .base

/-- `e`, printed, is read as its tree at its own level and every one above, with enough fuel. -/
def Reads (e : PExpr) : Prop :=
  ∀ (L : Level), L.idx ≤ (native e).idx → ∀ rest, Follows L rest → ∀ k,
    12 * (toks e).length + 12 ≤ k → pAt k L (toks e ++ rest) = some (tree e, rest)

/-- …and printed as an operand where only atoms stand bare, at every level. -/
def ReadsU (e : PExpr) : Prop :=
  ∀ (L : Level) rest, Follows L rest → ∀ k, 12 * (toksU e).length + 12 ≤ k →
    pAt k L (toksU e ++ rest) = some (tree e, rest)

theorem toksU_head (u : PExpr) (rest : List Tok) :
    (toksU u ++ rest).head? ≠ some (.kw "lds") ∧ (toksU u ++ rest).head? ≠ some (.kw "ld8") := by
  unfold toksU wrapT
  cases h : isAtom u
  · simp
  · cases u <;> simp_all [isAtom, toks]

/-- A count of fuel: `k` is what reading at the level `M` takes and the climb to `L`. -/
theorem fuel_split {k a : Nat} (L M : Level) (hk : a + 1 + (M.idx - L.idx) ≤ k) :
    ∃ j, k = j + 1 + (M.idx - L.idx) ∧ a ≤ j := ⟨k - 1 - (M.idx - L.idx), by omega, by omega⟩

theorem paren_reads {e : PExpr} (h : Reads e) : ∀ (L : Level) rest, Follows L rest → ∀ k,
    12 * (toks e).length + 36 ≤ k →
      pAt k L (.sym "(" :: (toks e ++ .sym ")" :: rest)) = some (tree e, rest) := by
  intro L rest hf k hk
  obtain ⟨j, rfl, hj⟩ := fuel_split (k := k) (a := 12 * (toks e).length + 12) L .base
    (by have := idx_le L; have : Level.base.idx = 10 := rfl; omega)
  have hin := h .eq (Nat.zero_le _) (.sym ")" :: rest) (Follows.stop rfl (by decide) (by decide)) j hj
  exact climb (pAt_paren hin) (Or.inl (by simp)) (Or.inl (by simp)) _ L
    (by have := idx_le L; have : Level.base.idx = 10 := rfl; omega) hf

theorem unit_reads {e : PExpr} (h : Reads e) : ReadsU e := by
  intro L rest hf k hk
  unfold toksU wrapT at hk ⊢
  cases ha : isAtom e
  · simp only [ha, Bool.false_eq_true, ↓reduceIte, List.cons_append, List.append_assoc] at hk ⊢
    exact paren_reads h L rest hf k (by simp at hk; omega)
  · simp only [ha, ↓reduceIte] at hk ⊢
    have hn : native e = .base := by cases e <;> simp_all [isAtom, native]
    exact h L (by rw [hn]; exact idx_le L) rest hf k hk

theorem step_level {L : Level} {s : String} {f : Exp → Exp → Exp} (h : step L s = some f) :
    L = .or_ ∨ L = .xor ∨ L = .and_ ∨ L = .add ∨ L = .mul := by
  unfold step at h; split at h <;> simp_all

theorem rest_toks_len {s : String} {us : List PExpr} (h : us ≠ []) : 2 ≤ (restToks s us).length := by
  cases us with
  | nil => exact absurd rfl h
  | cons u us =>
    rw [rest_toks_cons]
    have : (toksU u).length ≥ 1 := by
      unfold toksU wrapT; cases isAtom u
      · simp
      · cases u <;> simp [toks] <;> omega
    simp; omega

/-- After the first operand of a chain, its operator comes, which no level below reads. -/
theorem follows_rest_toks {L : Level} {s : String} {f : Exp → Exp → Exp} (hs : step L s = some f)
    {us : List PExpr} (h : us ≠ []) (rest : List Tok) : Follows L.next (restToks s us ++ rest) := by
  obtain ⟨hidx, hs1, hs2, hL⟩ := step_some hs
  have hn := idx_next hL
  cases us with
  | nil => exact absurd rfl h
  | cons v vs =>
    rw [rest_toks_cons, List.cons_append]
    exact ⟨fun n h => by rw [hidx] at h; cases h; omega, by simpa using hs1,
      fun h => absurd (Tok.sym.inj h) hs2⟩

/-- **A printed chain reads as the fold of its operands' trees**, at its level and above. -/
theorem reads_chain {op : POp} {C : Level} {s : String} {f : Exp → Exp → Exp} {l r : PExpr}
    (hC : native (.binop op l r) = C) (hs : step C s = some f) (hsym : opSym op = s)
    (hu : ∀ u ∈ units op l ++ units op r, ReadsU u)
    (hfold : ∀ u us, units op l ++ units op r = u :: us →
      us.foldl (fun r v => f r (tree v)) (tree u) = tree (.binop op l r)) :
    Reads (.binop op l r) := by
  intro L hL rest hf k hk
  rw [hC] at hL
  rw [toks_binop, hsym] at hk ⊢
  cases hus : units op l ++ units op r with
  | nil => exact absurd hus (by simp [units_ne_nil])
  | cons u us =>
    have hne : us ≠ [] := by
      intro he; subst he
      have := units_ne_nil op r
      cases hl : units op l with
      | nil => exact units_ne_nil op l hl
      | cons a as => rw [hl] at hus; simp at hus; exact this (by simp_all)
    rw [hus, toksJoin_cons] at hk
    rw [toksJoin_cons]
    have h2 := rest_toks_len (s := s) hne
    have hCle : C.idx ≤ 9 := by rcases step_level hs with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨j, rfl, hj⟩ := fuel_split (k := k)
      (a := 12 * (toksU u).length + 12 * (restToks s us).length + 2) L C (by simp at hk; omega)
    have hp := hu u (by rw [hus]; simp) C.next (restToks s us ++ rest) (follows_rest_toks hs hne rest)
      j (by omega)
    have hc := chain_units hs us (fun v hv => hu v (by rw [hus]; simp [hv]) C.next) (tree u) rest
      (hf.mono hL) j (by omega)
    have hpc : pAt (j + 1) C (toksU u ++ restToks s us ++ rest) = some (tree (.binop op l r), rest) := by
      rw [pAt_chain (step_level hs), List.append_assoc, hp]
      simp only [Option.bind_some]
      rw [hc, hfold u us hus]
    obtain ⟨h1, h2⟩ := toksU_head u (restToks s us ++ rest)
    rw [List.append_assoc] at hpc ⊢
    exact climb hpc (Or.inl h1) (Or.inl h2) _ L (by omega) hf

theorem units_nonassoc {op : POp} (h : isAssoc op = false) (x : PExpr) : units op x = [x] := by
  cases x <;> simp [units, h]

theorem units_shape {op : POp} : ∀ x u, u ∈ units op x → Shape x → Shape u
  | .binop o a b, u, hu, hs => by
    unfold units at hu; split at hu
    · rcases List.mem_append.mp hu with h | h
      · exact units_shape a u h hs.1
      · exact units_shape b u h hs.2
    · simp at hu; subst hu; exact hs
  | .base, u, hu, hs | .const _, u, hu, hs | .var _, u, hu, hs | .loadw _ _, u, hu, hs
  | .loadb _, u, hu, hs | .shr _ _, u, hu, hs | .shl _ _, u, hu, hs => by
    simp [units] at hu; subst hu; exact hs

theorem tree_sub_len : ∀ x es, tree x = .op "Sub" es → es.length = 2
  | .binop o l r, es, h => by
    cases o
    case sub => simp [tree] at h; rw [← h]; rfl
    case mul => obtain ⟨a, b, hm⟩ := tree_mul_isMul l r; rw [hm] at h; cases h
    case and_ =>
      obtain ⟨es', hj⟩ := joined_isOp "And" (tree l) (tree r)
      simp only [tree, hj] at h; simp at h
    all_goals simp [tree] at h
  | .base, _, h | .const _, _, h | .var _, _, h | .loadw _ _, _, h | .loadb _, _, h
  | .shr _ _, _, h | .shl _ _, _, h => by simp [tree] at h

theorem joined_sub (x : PExpr) (t : Exp) : joined "Sub" (tree x) t = .op "Sub" [tree x, t] := by
  unfold joined; split
  · rename_i b es heq
    by_cases hb : b = "Sub"
    · subst hb; simp [tree_sub_len x es heq]
    · simp [hb]
  · rfl

theorem atom_reads {e : PExpr} (ha : isAtom e = true) : Reads e := by
  intro L _ rest hf k hk
  have hn : native e = .base := by cases e <;> simp_all [isAtom, native]
  obtain ⟨j, rfl, _⟩ := fuel_split (k := k) (a := 0) L .base
    (by have := idx_le L; have : Level.base.idx = 10 := rfl; cases e <;> simp_all [isAtom, toks] <;> omega)
  have hb : pAt (j + 1) .base (toks e ++ rest) = some (tree e, rest) := by
    cases e <;> simp only [isAtom, toks, tree, Bool.false_eq_true] at ha ⊢
    · exact pAt_baseAddr
    · exact pAt_int
    · exact pAt_ident hf.noStruct
  have hh : (toks e ++ rest).head? ≠ some (.kw "lds") ∧ (toks e ++ rest).head? ≠ some (.kw "ld8") := by
    cases e <;> simp_all [isAtom, toks]
  exact climb hb (Or.inl hh.1) (Or.inl hh.2) _ L
    (by have := idx_le L; have : Level.base.idx = 10 := rfl; omega) hf

theorem follows_op {L : Level} {s : String} {rest : List Tok} {r : PExpr} (hf : Follows L rest)
    {n : Nat} (hn : opIdx (.sym s) = some n) (hlt : n < L.idx) (hs : s ≠ "=") :
    Follows L (.sym s :: (toksU r ++ rest)) := by
  refine ⟨fun m hm => by rw [hn] at hm; cases hm; exact hlt, by simpa using hs, fun _ y r' he => ?_⟩
  unfold toksU wrapT at he
  cases ha : isAtom r <;> simp only [ha, Bool.false_eq_true, ↓reduceIte] at he
  · simp at he
  · cases r with
    | var x =>
      simp only [toks, List.singleton_append, List.cons.injEq] at he
      obtain ⟨_, hrest⟩ := he; subst hrest; exact hf.2.1 rfl
    | const _ => simp [toks] at he
    | base => simp [toks] at he
    | _ => simp [isAtom] at ha

theorem toks_nonassoc {op : POp} (ha : isAssoc op = false) (l r : PExpr) :
    toks (.binop op l r) = toksU l ++ .sym (opSym op) :: toksU r := by
  rw [toks_binop, units_nonassoc ha, units_nonassoc ha]
  simp [toksJoin]

/-- A comparison: its operands at `ELoadNT`, each a unit. -/
theorem reads_cmp {op : POp} {l r : PExpr} {s : String} {c : String × Bool}
    (hop : op = .lt ∨ op = .le) (hsym : opSym op = s) (hc : cmpOf s = some c)
    (ht : comparison c (tree l) (tree r) = tree (.binop op l r)) (hl : ReadsU l) (hr : ReadsU r) :
    Reads (.binop op l r) := by
  have ha : isAssoc op = false := by rcases hop with rfl | rfl <;> rfl
  have hn : native (.binop op l r) = .cmp := by rcases hop with rfl | rfl <;> rfl
  intro L hL rest hf k hk
  rw [hn] at hL
  rw [toks_nonassoc ha, hsym] at hk ⊢
  have hlen : (toksU l ++ .sym s :: toksU r).length = (toksU l).length + 1 + (toksU r).length := by
    simp; omega
  rw [hlen] at hk
  rw [List.append_assoc, List.cons_append]
  have hidx := cmpOf_some hc
  have hs : s ≠ "=" := by intro he; subst he; simp [opIdx] at hidx
  have i1 : Level.cmp.idx = 1 := rfl
  have i2 : Level.lds.idx = 2 := rfl
  obtain ⟨j, rfl, hj⟩ := fuel_split (k := k)
    (a := 12 * (toksU l).length + 12 * (toksU r).length + 12) L .cmp (by omega)
  have hfl : Follows .lds rest := hf.mono (by omega)
  have h1 := hl .lds (.sym s :: (toksU r ++ rest)) (follows_op hfl hidx (by omega) hs) j (by omega)
  have h2 := hr .lds rest hfl j (by omega)
  have hpc := pAt_cmp_two h1 hc h2
  rw [ht] at hpc
  obtain ⟨hh1, hh2⟩ := toksU_head l (.sym s :: (toksU r ++ rest))
  exact climb hpc (Or.inl hh1) (Or.inl hh2) _ L (by omega) hf

theorem reads_eq {l r : PExpr} (hl : ReadsU l) (hr : ReadsU r) : Reads (.binop .eq l r) := by
  intro L hL rest hf k hk
  simp only [native] at hL
  rw [toks_nonassoc rfl] at hk ⊢
  have hlen : (toksU l ++ .sym (opSym .eq) :: toksU r).length =
      (toksU l).length + 1 + (toksU r).length := by simp; omega
  rw [hlen] at hk
  rw [List.append_assoc, List.cons_append]
  have hL0 : L = .eq := idx_inj (by have : Level.eq.idx = 0 := rfl; omega)
  subst hL0
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hfc : Follows .cmp rest := hf.mono (by decide)
  have h1 := hl .cmp (.sym "==" :: (toksU r ++ rest)) (follows_op hfc (n := 0) rfl (by decide)
    (by decide)) j (by omega)
  have h2 := hr .cmp rest hfc j (by omega)
  exact pAt_eq_two h1 h2

theorem addressBare_eq (a : PExpr) : Precedence.addressBare a = isAtom a := by
  cases a <;> rfl

theorem reads_lds {a : PExpr} (ha : ReadsU a) : Reads (.loadw 1 a) := by
  intro L hL rest hf k hk
  simp only [native] at hL
  simp only [toks, addressBare_eq, show wrapT (isAtom a) (toks a) = toksU a from rfl,
    List.length_cons] at hk ⊢
  have i2 : Level.lds.idx = 2 := rfl
  obtain ⟨j, rfl, hj⟩ := fuel_split (k := k) (a := 12 * (toksU a).length + 12) L .lds (by omega)
  have hp := ha .ld8 rest (hf.mono (by have : Level.ld8.idx = 3 := rfl; omega)) j hj
  have hb : pAt (j + 1) .lds (.kw "lds" :: .int 1 :: (toksU a ++ rest)) = some (tree (.loadw 1 a), rest) := by
    rw [pAt_lds, hp]; rfl
  exact climb hb (Or.inr (by decide)) (Or.inr (by decide)) _ L (by omega) hf

theorem reads_ld8 {a : PExpr} (ha : ReadsU a) : Reads (.loadb a) := by
  intro L hL rest hf k hk
  simp only [native] at hL
  simp only [toks, addressBare_eq, show wrapT (isAtom a) (toks a) = toksU a from rfl,
    List.length_cons] at hk ⊢
  have i3 : Level.ld8.idx = 3 := rfl
  obtain ⟨j, rfl, hj⟩ := fuel_split (k := k) (a := 12 * (toksU a).length + 12) L .ld8 (by omega)
  have hp := ha .or_ rest (hf.mono (by have : Level.or_.idx = 4 := rfl; omega)) j hj
  have hb : pAt (j + 1) .ld8 (.kw "ld8" :: (toksU a ++ rest)) = some (tree (.loadb a), rest) := by
    rw [pAt_ld8, hp]; rfl
  exact climb hb (Or.inl (by simp)) (Or.inr (by decide)) _ L (by omega) hf

/-- A shift: the left parenthesized, read at `EAddNT`, then the symbol and a number. -/
theorem reads_shift {l : PExpr} {n : Nat} {s sh : String} {e : PExpr} (hs : shiftOf s = some sh)
    (htoks : toks e = .sym "(" :: (toks l ++ [.sym ")", .sym s, .int n]))
    (htree : tree e = .shift sh (tree l) n) (hn : native e = .shift) (hl : Reads l) : Reads e := by
  intro L hL rest hf k hk
  rw [hn] at hL
  rw [htoks, htree] at *
  simp only [List.length_cons, List.length_append] at hk
  have i7 : Level.shift.idx = 7 := rfl
  obtain ⟨j, rfl, hj⟩ := fuel_split (k := k) (a := 12 * (toks l).length + 37) L .shift (by omega)
  have hfa : Follows .add (.sym s :: .int n :: rest) :=
    ⟨fun m hm => by rw [shiftOf_some hs] at hm; cases hm; decide,
      by intro h; cases h; simp [shiftOf] at hs,
      by intro h; cases h; simp [shiftOf] at hs⟩
  have hp := paren_reads hl .add _ hfa j (by omega)
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  have hb : pAt (i + 2 + 1) .shift (.sym "(" :: (toks l ++ [.sym ")", .sym s, .int n]) ++ rest) =
      some (.shift sh (tree l) n, rest) := by
    rw [pAt_shift]
    simp only [List.cons_append, List.append_assoc, List.cons_append, List.nil_append] at hp ⊢
    rw [hp]; simp only [Option.bind_some]
    rw [shift_step hs]
    refine shift_stop fun s' m r hr => ?_
    cases hs' : shiftOf s' with
    | none => rfl
    | some _ => subst hr; have := hf.1 _ (shiftOf_some hs'); omega
  exact climb hb (Or.inl (by simp)) (Or.inl (by simp)) _ L (by omega) hf

theorem units_tail {op : POp} {l r u : PExpr} {us : List PExpr} (h : units op l ++ units op r = u :: us) :
    ∃ v vs, us = v :: vs := by
  cases us with
  | cons v vs => exact ⟨v, vs, rfl⟩
  | nil =>
    cases hl : units op l with
    | nil => exact absurd hl (units_ne_nil _ _)
    | cons a as =>
      rw [hl] at h; simp at h
      exact absurd h.2.2 (units_ne_nil _ _)

theorem fold_assoc {op : POp} (hop : op = .add ∨ op = .xor ∨ op = .or_) {l r u : PExpr}
    {us : List PExpr} (h : units op l ++ units op r = u :: us) :
    us.foldl (fun t v => joined (chainName op) t (tree v)) (tree u) = tree (.binop op l r) := by
  obtain ⟨v, vs, rfl⟩ := units_tail h
  have hmem : u ∈ units op l ++ units op r := by rw [h]; simp
  have hnot : ∀ es, tree u ≠ .op (chainName op) es := by
    intro es he
    obtain ⟨a, b, hu⟩ := tree_op_name hop u ⟨es, he⟩
    rcases List.mem_append.mp hmem with hm | hm
    · exact units_mem (isAssoc_chain hop) l u hm a b hu
    · exact units_mem (isAssoc_chain hop) r u hm a b hu
  have hname : chainName op ≠ "Sub" := by rcases hop with rfl | rfl | rfl <;> decide
  rw [fold_chain hname hnot v vs, tree_chain hop, opsOf_tree hop, opsOf_tree hop, ← List.map_append, h]
  rfl

theorem fold_mulChain {l r u : PExpr} {us : List PExpr} (h : units .mul l ++ units .mul r = u :: us) :
    us.foldl (fun t v => .mul [t, tree v]) (tree u) = tree (.binop .mul l r) := by
  rw [fold_mul]
  simp only [tree, mulOps_tree, ← List.map_append, h, List.map_cons]

/-- **Every expression the gate's shapes allow reads, printed, as its tree.** -/
theorem reads_all : ∀ (n : Nat) (e : PExpr), sizeOf e ≤ n → Shape e → Reads e
  | 0, e, hs, _ => by cases e <;> simp at hs
  | n + 1, e, hsz, hsh => by
    have ih : ∀ x, sizeOf x ≤ n → Shape x → Reads x := reads_all n
    match e, hsz, hsh with
    | .base, _, _ => exact atom_reads rfl
    | .const _, _, _ => exact atom_reads rfl
    | .var _, _, _ => exact atom_reads rfl
    | .binop op l r, hsz, hsh =>
      have hsl : sizeOf l ≤ n := by simp at hsz; omega
      have hsr : sizeOf r ≤ n := by simp at hsz; omega
      have hU : ∀ u ∈ units op l ++ units op r, ReadsU u := by
        intro u hu
        rcases List.mem_append.mp hu with hm | hm
        · exact unit_reads (ih u (Nat.le_trans (units_size l u hm) hsl) (units_shape l u hm hsh.1))
        · exact unit_reads (ih u (Nat.le_trans (units_size r u hm) hsr) (units_shape r u hm hsh.2))
      have hl := unit_reads (ih l hsl hsh.1)
      have hr := unit_reads (ih r hsr hsh.2)
      cases op with
      | add => exact reads_chain rfl rfl rfl hU fun u us h => fold_assoc (op := .add) (by simp) h
      | xor => exact reads_chain rfl rfl rfl hU fun u us h => fold_assoc (op := .xor) (by simp) h
      | or_ => exact reads_chain rfl rfl rfl hU fun u us h => fold_assoc (op := .or_) (by simp) h
      | mul => exact reads_chain rfl rfl rfl hU fun u us h => fold_mulChain h
      | and_ =>
        refine reads_chain rfl rfl rfl hU fun u us h => ?_
        rw [units_nonassoc rfl, units_nonassoc rfl] at h
        simp at h; obtain ⟨rfl, rfl⟩ := h; rfl
      | sub =>
        refine reads_chain rfl rfl rfl hU fun u us h => ?_
        rw [units_nonassoc rfl, units_nonassoc rfl] at h
        simp at h; obtain ⟨rfl, rfl⟩ := h
        simp only [List.foldl_cons, List.foldl_nil, joined_sub]; rfl
      | lt => exact reads_cmp (Or.inl rfl) rfl rfl rfl hl hr
      | le => exact reads_cmp (Or.inr rfl) rfl rfl rfl hl hr
      | eq => exact reads_eq hl hr
    | .loadw sh a, hsz, hsh =>
      obtain ⟨rfl, ha⟩ := hsh
      exact reads_lds (unit_reads (ih a (by simp at hsz; omega) ha))
    | .loadb a, hsz, hsh => exact reads_ld8 (unit_reads (ih a (by simp at hsz; omega) hsh))
    | .shr l r, hsz, hsh =>
      obtain ⟨⟨m, rfl⟩, hl⟩ := hsh
      exact reads_shift (s := ">>>") (n := m) rfl (by simp [toks]) rfl rfl (ih l (by simp at hsz; omega) hl)
    | .shl l r, hsz, hsh =>
      obtain ⟨⟨m, rfl⟩, hl⟩ := hsh
      exact reads_shift (s := "<<") (n := m) rfl (by simp [toks]) rfl rfl (ih l (by simp at hsz; omega) hl)

theorem reads (e : PExpr) (h : Shape e) : Reads e := reads_all _ e (Nat.le_refl _) h

/-! ### Statements, as the parser takes them -/

def seqOpt (s : Prog) : Option Prog → Prog
  | some q => .seq s q
  | none => s
theorem pProg_stmt {k : Nat} {t : Tok} {ts ts' rest : List Tok} {s : Prog} {r : Option Prog}
    (hhead : t ≠ .kw "if" ∧ t ≠ .kw "while" ∧ t ≠ .kw "var" ∧ t ≠ .sym "}" ∧ t ≠ .sym "{")
    (h : pStmt k (t :: ts) = some (s, .sym ";" :: ts')) (hr : pProg k ts' = some (r, rest)) :
    pProg (k + 1) (t :: ts) = some (some (seqOpt s r), rest) := by
  rw [pProg.eq_def]
  split
  · omega
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · simp_all
  · next _ _ k' hk _ _ _ _ _ =>
    obtain rfl : k = k' := by omega
    simp only [h, Option.bind_eq_bind, Option.bind_some, hr]
    cases r <;> rfl
theorem pTry_prog {k : Nat} {t : Tok} {ts rest : List Tok} {p : Option Prog} (h : t ≠ .sym "}")
    (hp : pProg k (t :: ts) = some (p, rest)) : pTry (k + 1) (t :: ts) = some (p.getD .skip, rest) := by
  rw [pTry.eq_def]; split <;> simp_all

theorem pProg_close {k : Nat} {ts : List Tok} : pProg (k + 1) (.sym "}" :: ts) = some (none, ts) := by
  rw [pProg.eq_def]; rfl

theorem pTry_close {k : Nat} {ts : List Tok} : pTry (k + 1) (.sym "}" :: ts) = some (.skip, ts) := by
  rw [pTry.eq_def]; rfl

theorem pProg_block {k : Nat} {t : Tok} {ts ts' rest : List Tok} {b : Prog} {r : Option Prog}
    (ht : t = .kw "if" ∨ t = .kw "while") (h : pBlock k (t :: ts) = some (b, ts'))
    (hr : pProg k ts' = some (r, rest)) :
    pProg (k + 1) (t :: ts) = some (some (seqOpt b r), rest) := by
  rcases ht with rfl | rfl
  all_goals
    rw [pProg.eq_def]
    simp only [h, Option.bind_eq_bind, Option.bind_some, hr]
    cases r <;> rfl

theorem pProg_dec {k : Nat} {v : String} {ts ts' rest : List Tok} {e : Exp} {p : Prog}
    (hnc : ∀ f r, ts ≠ .ident f :: .sym "(" :: r) (he : pExp k ts = some (e, .sym ";" :: ts'))
    (hp : pTry k ts' = some (p, rest)) :
    pProg (k + 1) (.kw "var" :: .ident v :: .sym "=" :: ts) = some (some (.dec v e p), rest) := by
  rw [pProg.eq_def]
  simp only [pShaped, Option.bind_eq_bind, Option.bind_some]
  simp [he, hp]

theorem pProg_call {k : Nat} {v f : String} {args ts rest : List Tok} {es : List Exp} {p : Prog}
    (hf : f ≠ "__add_with_carry__") (ha : pArgs k args = some (es, .sym ")" :: .sym ";" :: ts))
    (hp : pTry k ts = some (p, rest)) :
    pProg (k + 1) (.kw "var" :: .ident v :: .sym "=" :: .ident f :: .sym "(" :: args) =
      some (some (.decCall v f es p), rest) := by
  rw [pProg.eq_def]
  simp [pShaped, hf, ha, hp]

theorem pBlock_if {k : Nat} {ts ts1 ts2 rest : List Tok} {e : Exp} {p q : Prog}
    (he : pExp k ts = some (e, .sym "{" :: ts1)) (hp : pTry k ts1 = some (p, .kw "else" :: .sym "{" :: ts2))
    (hq : pTry k ts2 = some (q, rest)) : pBlock (k + 1) (.kw "if" :: ts) = some (.ite e p q, rest) := by
  rw [pBlock.eq_def]; simp [he, hp, hq]

theorem pBlock_while {k : Nat} {ts ts1 rest : List Tok} {e : Exp} {p : Prog}
    (he : pExp k ts = some (e, .sym "{" :: ts1)) (hp : pTry k ts1 = some (p, rest)) :
    pBlock (k + 1) (.kw "while" :: ts) = some (.while e p, rest) := by
  rw [pBlock.eq_def]; simp [he, hp]

theorem pStmt_assign {k : Nat} {v : String} {ts rest : List Tok} {e : Exp} (hc : callAhead ts = false)
    (he : pExp k ts = some (e, rest)) :
    pStmt k (.ident v :: .sym "=" :: ts) = some (.assign false v e, rest) := by
  simp [pStmt, hc, he]

theorem pStmt_ret {k : Nat} {ts rest : List Tok} {e : Exp} (hc : callAhead ts = false)
    (he : pExp k ts = some (e, rest)) : pStmt k (.kw "return" :: ts) = some (.ret e, rest) := by
  simp [pStmt, hc, he]

theorem pStmt_store {k : Nat} {w : String} {ts ts1 rest : List Tok} {a e : Exp}
    (hw : w = "st" ∨ w = "st8") (ha : pExp k ts = some (a, .sym "," :: ts1))
    (he : pExp k ts1 = some (e, rest)) :
    pStmt k (.kw w :: ts) = some (if w = "st" then .store a e else .storeByte a e, rest) := by
  rcases hw with rfl | rfl <;> simp [pStmt, ha, he]

theorem pStmt_ffi {k : Nat} {n : String} {ts t1 t2 t3 rest : List Tok} {a b c d : Exp}
    (ha : pExp k ts = some (a, .sym "," :: t1)) (hb : pExp k t1 = some (b, .sym "," :: t2))
    (hc : pExp k t2 = some (c, .sym "," :: t3)) (hd : pExp k t3 = some (d, .sym ")" :: rest)) :
    pStmt k (.foreign n :: .sym "(" :: ts) = some (.extCall n a b c d, rest) := by
  simp [pStmt, ha, hb, hc, hd]

theorem more_comma {k j : Nat} {es : List Exp} {ts r : List Tok} {e : Exp} (h : pExp k ts = some (e, r)) :
    pArgs.more k (j + 1) es (.sym "," :: ts) = pArgs.more k j (es ++ [e]) r := by
  rw [pArgs.more.eq_def]; simp [h]

theorem more_stop {k j : Nat} {es : List Exp} {ts : List Tok} (h : ∀ r, ts ≠ .sym "," :: r) :
    pArgs.more k (j + 1) es ts = some (es, ts) := by
  rw [pArgs.more.eq_def]; split <;> simp_all

theorem pArgs_nil {k : Nat} {ts : List Tok} : pArgs k (.sym ")" :: ts) = some ([], .sym ")" :: ts) := by
  simp [pArgs]

theorem pArgs_cons {k : Nat} {ts ts1 : List Tok} {e : Exp} (hh : ∀ r, ts ≠ .sym ")" :: r)
    (he : pExp k ts = some (e, ts1)) : pArgs k ts = pArgs.more k (ts1.length + 1) [e] ts1 := by
  unfold pArgs; split
  · simp_all
  · simp [he]

theorem pShaped_one {v : String} {ts : List Tok} : pShaped (.int 1 :: .ident v :: ts) = some (v, ts) := by
  simp [pShaped]

theorem pShaped_name {v : String} {t : Tok} {ts : List Tok} (ht : ∀ w, t ≠ .ident w) :
    pShaped (.ident v :: t :: ts) = some (v, t :: ts) := by
  unfold pShaped; split <;> simp_all

/-! ### Every printed statement reads as its tree -/

mutual
/-- The tree of a statement that ends its block. -/
def stmtTree : PStmt → Prog
  | .dec n v => .dec n (tree v) .skip
  | .assign n v => .assign false n (tree v)
  | .store a v => .store (tree a) (tree v)
  | .storeb a v => .storeByte (tree a) (tree v)
  | .ffi n [a, b, c, d] => .extCall n (tree a) (tree b) (tree c) (tree d)
  | .ffi _ _ => .skip
  | .call r f as => .decCall r f (as.map tree) .skip
  | .ret v => .ret (tree v)
  | .ite c t e => .ite (tree c) (blockTree t) (blockTree e)
  | .while c b => .while (tree c) (blockTree b)
/-- **The tree of a block's statements**, nested as `lowerStmtsFold` nests them. -/
def blockTree : List PStmt → Prog
  | [] => .skip
  | [s] => stmtTree s
  | .dec n v :: rest => .dec n (tree v) (blockTree rest)
  | .call r f as :: rest => .decCall r f (as.map tree) (blockTree rest)
  | s :: rest => .seq (stmtTree s) (blockTree rest)
end

def progOf (ss : List PStmt) : Option Prog := if ss = [] then none else some (blockTree ss)

mutual
/-- The gate's shapes, in a statement: an external call of four arguments, no call the parser
takes for a primitive. -/
def SShape : PStmt → Prop
  | .dec _ v | .assign _ v | .ret v => Shape v
  | .store a v | .storeb a v => Shape a ∧ Shape v
  | .ffi _ args => args.length = 4 ∧ ∀ a ∈ args, Shape a
  | .call _ f args => f ≠ "__add_with_carry__" ∧ ∀ a ∈ args, Shape a
  | .ite c t e => Shape c ∧ SShapes t ∧ SShapes e
  | .while c b => Shape c ∧ SShapes b
def SShapes : List PStmt → Prop
  | [] => True
  | s :: ss => SShape s ∧ SShapes ss
end

/-- A token after an expression that no level reads. -/
def Term (t : Tok) : Prop := t = .sym ";" ∨ t = .sym "," ∨ t = .sym ")" ∨ t = .sym "{"

theorem Term.follows {t : Tok} (h : Term t) (L : Level) (rest : List Tok) : Follows L (t :: rest) := by
  rcases h with rfl | rfl | rfl | rfl <;> exact Follows.stop rfl (by decide) (by decide)

theorem exp_reads {e : PExpr} (h : Shape e) {t : Tok} (ht : Term t) (rest : List Tok) {k : Nat}
    (hk : 12 * (toks e).length + 12 ≤ k) : pExp k (toks e ++ t :: rest) = some (tree e, t :: rest) :=
  reads e h .eq (Nat.zero_le _) _ (ht.follows .eq rest) k hk

/-- What a printed expression starts with: never a call. -/
theorem toks_noCall : ∀ (e : PExpr) (rest : List Tok), (∀ r, rest ≠ .sym "(" :: r) →
    ∀ f r, toks e ++ rest ≠ .ident f :: .sym "(" :: r
  | .var x, rest, h, f, r, he => by simp [toks] at he; exact h r he.2
  | .binop op l r', rest, h, f, r, he => by
    simp only [toks, List.append_assoc, List.cons_append] at he
    unfold wrapT at he
    split at he
    · exact toks_noCall l _ (fun _ hh => by cases op <;> simp [opSym] at hh) f r he
    · simp at he
  | .base, _, _, _, _, he | .const _, _, _, _, _, he | .loadw _ _, _, _, _, _, he
  | .loadb _, _, _, _, _, he | .shr _ _, _, _, _, _, he | .shl _ _, _, _, _, _, he => by
    simp [toks] at he

theorem toks_head_star : ∀ (e : PExpr) (rest : List Tok), ∀ r, toks e ++ rest ≠ .sym "*" :: r
  | .binop op l r', rest, r, he => by
    simp only [toks, List.append_assoc, List.cons_append] at he
    unfold wrapT at he
    split at he
    · exact toks_head_star l _ r he
    · simp at he
  | .base, _, _, he | .const _, _, _, he | .var _, _, _, he | .loadw _ _, _, _, he
  | .loadb _, _, _, he | .shr _ _, _, _, he | .shl _ _, _, _, he => by simp [toks] at he

theorem callAhead_toks (e : PExpr) {t : Tok} (ht : Term t) (rest : List Tok) :
    callAhead (toks e ++ t :: rest) = false := by
  unfold callAhead; split
  · rename_i f r heq
    exact absurd heq (toks_noCall e _
      (fun r hr => by rcases ht with rfl | rfl | rfl | rfl <;> simp at hr) f r)
  · rename_i r heq; exact absurd heq (toks_head_star e _ r)
  · rfl

theorem toks_head_close : ∀ (e : PExpr) (rest : List Tok), ∀ r, toks e ++ rest ≠ .sym ")" :: r
  | .binop op l r', rest, r, he => by
    simp only [toks, List.append_assoc, List.cons_append] at he
    unfold wrapT at he
    split at he
    · exact toks_head_close l _ r he
    · simp at he
  | .base, _, _, he | .const _, _, _, he | .var _, _, _, he | .loadw _ _, _, _, he
  | .loadb _, _, _, he | .shr _ _, _, _, he | .shl _ _, _, _, he => by simp [toks] at he

theorem toks_len (e : PExpr) : 1 ≤ (toks e).length := by
  cases e <;> simp [toks] <;> omega

def commaToks (as : List PExpr) : List Tok := as.flatMap fun b => .sym "," :: toks b

theorem argToks_cons : ∀ (a : PExpr) (as : List PExpr), argToks (a :: as) = toks a ++ commaToks as
  | a, [] => by simp [argToks, commaToks]
  | a, b :: bs => by
    show toks a ++ .sym "," :: argToks (b :: bs) = _
    rw [argToks_cons b bs]; simp [commaToks]

theorem commaToks_len (as : List PExpr) : 2 * as.length ≤ (commaToks as).length := by
  induction as with
  | nil => simp [commaToks]
  | cons b bs ih =>
    have := toks_len b
    simp only [commaToks, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

theorem more_reads {k : Nat} : ∀ (as : List PExpr), (∀ a ∈ as, Shape a) → ∀ (es : List Exp)
    (rest : List Tok) (j : Nat), as.length + 1 ≤ j → 12 * (commaToks as).length + 12 ≤ k →
    pArgs.more k j es (commaToks as ++ .sym ")" :: rest) = some (es ++ as.map tree, .sym ")" :: rest)
  | [], _, es, rest, j, hj, _ => by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp at hj; omega⟩
    simp only [commaToks, List.flatMap_nil, List.nil_append, List.map_nil, List.append_nil]
    exact more_stop (by simp)
  | b :: bs, h, es, rest, j, hj, hk => by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp at hj; omega⟩
    have hlen : (commaToks (b :: bs)).length = 1 + (toks b).length + (commaToks bs).length := by
      simp [commaToks]; omega
    have he : pExp k (toks b ++ (commaToks bs ++ .sym ")" :: rest)) =
        some (tree b, commaToks bs ++ .sym ")" :: rest) := by
      cases bs with
      | nil => exact exp_reads (h b (by simp)) (t := .sym ")") (by simp [Term]) rest (by omega)
      | cons c cs =>
        simp only [commaToks, List.flatMap_cons, List.cons_append, List.append_assoc]
        exact exp_reads (h b (by simp)) (t := .sym ",") (by simp [Term]) _ (by omega)
    simp only [commaToks, List.flatMap_cons, List.cons_append, List.append_assoc] at he ⊢
    rw [more_comma he]
    have := more_reads (k := k) bs (fun a ha => h a (by simp [ha])) (es ++ [tree b]) rest i
      (by simp at hj; omega) (by omega)
    simp only [commaToks] at this
    rw [this]; simp

theorem args_read {k : Nat} (as : List PExpr) (h : ∀ a ∈ as, Shape a) (rest : List Tok)
    (hk : 12 * (argToks as).length + 12 ≤ k) :
    pArgs k (argToks as ++ .sym ")" :: rest) = some (as.map tree, .sym ")" :: rest) := by
  cases as with
  | nil => exact pArgs_nil
  | cons a bs =>
    rw [argToks_cons] at hk ⊢
    have hlen := commaToks_len bs
    have he : pExp k (toks a ++ (commaToks bs ++ .sym ")" :: rest)) =
        some (tree a, commaToks bs ++ .sym ")" :: rest) := by
      cases bs with
      | nil => exact exp_reads (h a (by simp)) (t := .sym ")") (by simp [Term]) rest (by simp at hk; omega)
      | cons c cs =>
        simp only [commaToks, List.flatMap_cons, List.cons_append, List.append_assoc]
        exact exp_reads (h a (by simp)) (t := .sym ",") (by simp [Term]) _ (by simp at hk; omega)
    rw [List.append_assoc, pArgs_cons (toks_head_close a _) he]
    have := more_reads (k := k) bs (fun x hx => h x (by simp [hx])) [tree a] rest
      ((commaToks bs ++ .sym ")" :: rest).length + 1) (by simp; omega) (by simp at hk; omega)
    rw [this]; rfl

theorem seqOpt_block {s : PStmt} (hd : ∀ n v, s ≠ .dec n v) (hc : ∀ r f as, s ≠ .call r f as)
    (ss : List PStmt) : seqOpt (stmtTree s) (progOf ss) = blockTree (s :: ss) := by
  cases ss with
  | nil => simp [progOf, seqOpt, blockTree]
  | cons t ts =>
    simp only [progOf, reduceCtorEq, ↓reduceIte, seqOpt]
    cases s <;> first | rfl | (exfalso; exact hd _ _ rfl) | (exfalso; exact hc _ _ _ rfl)

theorem finish_simple {s : PStmt} (hd : ∀ n v, s ≠ .dec n v) (hc : ∀ r f as, s ≠ .call r f as)
    (ss : List PStmt) (rest : List Tok) :
    some (some (seqOpt (stmtTree s) (progOf ss)), rest) = some (progOf (s :: ss), rest) := by
  rw [seqOpt_block hd hc]; simp [progOf]

theorem stmtToks_head (s : PStmt) (rest : List Tok) : ∀ r, stmtToks s ++ rest ≠ .sym "}" :: r := by
  intro r h; cases s <;> simp [stmtToks] at h

theorem try_of_prog {k : Nat} {ss : List PStmt} {rest : List Tok}
    (h : pProg k (stmtsToks ss ++ .sym "}" :: rest) = some (progOf ss, rest)) :
    pTry (k + 1) (stmtsToks ss ++ .sym "}" :: rest) = some (blockTree ss, rest) := by
  cases ss with
  | nil => exact pTry_close
  | cons s ss =>
    simp only [stmtsToks, List.append_assoc] at h ⊢
    cases hs : stmtToks s ++ (stmtsToks ss ++ .sym "}" :: rest) with
    | nil => cases s <;> simp [stmtToks] at hs
    | cons t ts =>
      rw [hs] at h
      have ht : t ≠ .sym "}" := fun he => stmtToks_head s _ ts (by rw [hs, he])
      rw [pTry_prog ht h]; simp [progOf]

theorem stmtToks_len (s : PStmt) : 2 ≤ (stmtToks s).length := by
  cases s <;> simp [stmtToks] <;> omega

theorem stmtsToks_cons (s : PStmt) (ss : List PStmt) :
    stmtsToks (s :: ss) = stmtToks s ++ stmtsToks ss := rfl

mutual
/-- **The statements of a printed block, up to its `}`, read as their tree.** -/
theorem stmts_read : ∀ (ss : List PStmt) (rest : List Tok) (k : Nat), SShapes ss →
    12 * (stmtsToks ss).length + 12 ≤ k →
      pProg k (stmtsToks ss ++ .sym "}" :: rest) = some (progOf ss, rest)
  | [], rest, k, _, hk => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp [stmtsToks] at hk; omega⟩
    exact pProg_close
  | s :: ss, rest, k, hsh, hk => by
    obtain ⟨hs, hss⟩ := hsh
    rw [stmtsToks_cons] at hk ⊢
    have h2 := stmtToks_len s
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by simp at hk; omega⟩
    have ih := stmts_read ss rest j hss (by simp at hk; omega)
    rw [List.append_assoc]
    cases s with
    | ite c t e =>
      have hb := block_read (.ite c t e) (stmtsToks ss ++ .sym "}" :: rest) j hs (by simp)
        (by simp at hk; omega)
      simp only [stmtToks, List.cons_append] at hb ⊢
      rw [pProg_block (Or.inl rfl) hb ih, seqOpt_block (by simp) (by simp)]; simp [progOf]
    | «while» c b =>
      have hb := block_read (.while c b) (stmtsToks ss ++ .sym "}" :: rest) j hs (by simp)
        (by simp at hk; omega)
      simp only [stmtToks, List.cons_append] at hb ⊢
      rw [pProg_block (Or.inr rfl) hb ih, seqOpt_block (by simp) (by simp)]; simp [progOf]
    | dec n v =>
      simp only [stmtToks, List.length_cons, List.length_append] at hk
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hp := try_of_prog (stmts_read ss rest i hss (by omega))
      have he := exp_reads hs (t := .sym ";") (by simp [Term]) (stmtsToks ss ++ .sym "}" :: rest)
        (k := i + 1) (by omega)
      simp only [stmtToks, List.cons_append, List.append_assoc, List.nil_append]
      rw [pProg_dec (toks_noCall v _ (by simp)) he hp]
      cases ss <;> rfl
    | call r f as =>
      simp only [stmtToks, List.length_cons, List.length_append] at hk
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hp := try_of_prog (stmts_read ss rest i hss (by simp at hk; omega))
      have ha := args_read (k := i + 1) as hs.2 (.sym ";" :: (stmtsToks ss ++ .sym "}" :: rest))
        (by simp at hk; omega)
      simp only [stmtToks, List.cons_append, List.append_assoc]
      rw [pProg_call hs.1 (by simpa using ha) hp]
      cases ss <;> rfl
    | assign n v =>
      simp only [stmtToks, List.length_cons, List.length_append] at hk
      have he := exp_reads hs (t := .sym ";") (by simp [Term]) (stmtsToks ss ++ .sym "}" :: rest)
        (k := j) (by simp at hk; omega)
      have hst := pStmt_assign (v := n) (callAhead_toks v (t := .sym ";") (by simp [Term]) _) he
      simp only [stmtToks, List.cons_append, List.append_assoc, List.nil_append] at hst ⊢
      rw [pProg_stmt (by simp) hst ih]
      exact finish_simple (s := .assign n v) (by simp) (by simp) ss rest
    | ret v =>
      simp only [stmtToks, List.length_cons, List.length_append] at hk
      have he := exp_reads hs (t := .sym ";") (by simp [Term]) (stmtsToks ss ++ .sym "}" :: rest)
        (k := j) (by simp at hk; omega)
      have hst := pStmt_ret (callAhead_toks v (t := .sym ";") (by simp [Term]) _) he
      simp only [stmtToks, List.cons_append, List.append_assoc, List.nil_append] at hst ⊢
      rw [pProg_stmt (by simp) hst ih]
      exact finish_simple (s := .ret v) (by simp) (by simp) ss rest
    | store a v =>
      simp only [stmtToks, List.length_cons, List.length_append] at hk
      have hv := exp_reads hs.2 (t := .sym ";") (by simp [Term]) (stmtsToks ss ++ .sym "}" :: rest)
        (k := j) (by simp at hk; omega)
      have ha := exp_reads hs.1 (t := .sym ",") (by simp [Term])
        (toks v ++ .sym ";" :: (stmtsToks ss ++ .sym "}" :: rest)) (k := j) (by simp at hk; omega)
      have hst := pStmt_store (w := "st") (Or.inl rfl) ha hv
      simp only [stmtToks, List.cons_append, List.append_assoc, List.nil_append,
        ↓reduceIte] at hst ⊢
      rw [pProg_stmt (by simp) hst ih]
      exact finish_simple (s := .store a v) (by simp) (by simp) ss rest
    | storeb a v =>
      simp only [stmtToks, List.length_cons, List.length_append] at hk
      have hv := exp_reads hs.2 (t := .sym ";") (by simp [Term]) (stmtsToks ss ++ .sym "}" :: rest)
        (k := j) (by simp at hk; omega)
      have ha := exp_reads hs.1 (t := .sym ",") (by simp [Term])
        (toks v ++ .sym ";" :: (stmtsToks ss ++ .sym "}" :: rest)) (k := j) (by simp at hk; omega)
      have hst := pStmt_store (w := "st8") (Or.inr rfl) ha hv
      simp only [stmtToks, List.cons_append, List.append_assoc, List.nil_append,
        show ("st8" = "st") = False by decide, ↓reduceIte] at hst ⊢
      rw [pProg_stmt (by simp) hst ih]
      exact finish_simple (s := .storeb a v) (by simp) (by simp) ss rest
    | ffi n args =>
      obtain ⟨hlen, hargs⟩ := hs
      match args, hlen, hargs with
      | [a, b, c, d], _, hargs =>
        simp only [stmtToks, argToks, List.length_cons, List.length_append] at hk
        have m : ∀ x, x ∈ [a, b, c, d] → Shape x := hargs
        let tail := .sym ";" :: (stmtsToks ss ++ .sym "}" :: rest)
        have hd := exp_reads (m d (by simp)) (t := .sym ")") (by simp [Term]) tail (k := j)
          (by simp at hk; omega)
        have hc := exp_reads (m c (by simp)) (t := .sym ",") (by simp [Term])
          (toks d ++ .sym ")" :: tail) (k := j) (by simp at hk; omega)
        have hb := exp_reads (m b (by simp)) (t := .sym ",") (by simp [Term])
          (toks c ++ .sym "," :: (toks d ++ .sym ")" :: tail)) (k := j) (by simp at hk; omega)
        have ha := exp_reads (m a (by simp)) (t := .sym ",") (by simp [Term])
          (toks b ++ .sym "," :: (toks c ++ .sym "," :: (toks d ++ .sym ")" :: tail))) (k := j)
          (by simp at hk; omega)
        have hst := pStmt_ffi (n := n) ha hb hc hd
        simp only [stmtToks, argToks, List.cons_append, List.append_assoc, List.nil_append]
        rw [pProg_stmt (by simp) hst ih]
        exact finish_simple (s := .ffi n [a, b, c, d]) (by simp) (by simp) ss rest
/-- …and so does a printed `if` or `while`. -/
theorem block_read : ∀ (s : PStmt) (rest : List Tok) (k : Nat), SShape s →
    (∃ c t e, s = .ite c t e) ∨ (∃ c b, s = .while c b) → 12 * (stmtToks s).length ≤ k →
      pBlock k (stmtToks s ++ rest) = some (stmtTree s, rest)
  | .ite c t e, rest, k, ⟨hc, ht, he⟩, _, hk => by
    simp only [stmtToks, List.length_cons, List.length_append] at hk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by simp at hk; omega⟩
    have he' := try_of_prog (stmts_read e rest i he (by simp at hk; omega))
    have ht' := try_of_prog (stmts_read t (.kw "else" :: .sym "{" :: (stmtsToks e ++ .sym "}" :: rest))
      i ht (by simp at hk; omega))
    have hcond := exp_reads hc (t := .sym "{") (by simp [Term])
      (stmtsToks t ++ .sym "}" :: .kw "else" :: .sym "{" :: (stmtsToks e ++ .sym "}" :: rest))
      (k := i + 1) (by simp at hk; omega)
    simp only [stmtToks, List.cons_append, List.append_assoc, List.nil_append]
    exact pBlock_if hcond ht' he'
  | .while c b, rest, k, ⟨hc, hb⟩, _, hk => by
    simp only [stmtToks, List.length_cons, List.length_append] at hk
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 2 := ⟨k - 2, by simp at hk; omega⟩
    have hb' := try_of_prog (stmts_read b rest i hb (by simp at hk; omega))
    have hcond := exp_reads hc (t := .sym "{") (by simp [Term]) (stmtsToks b ++ .sym "}" :: rest)
      (k := i + 1) (by simp at hk; omega)
    simp only [stmtToks, List.cons_append, List.append_assoc, List.nil_append]
    exact pBlock_while hcond hb'
  | .dec _ _, _, _, _, h, _ | .assign _ _, _, _, _, h, _ | .store _ _, _, _, _, h, _
  | .storeb _ _, _, _, _, h, _ | .ffi _ _, _, _, _, h, _ | .call _ _ _, _, _, _, h, _
  | .ret _, _, _, _, h, _ => by simp at h
end

/-! ### Functions and programs -/

/-- **What the parser gives of a printed function**: its names, and its body's tree with the
names its parameters and declarations bind made local. -/
def funTree (f : PFun) : Func :=
  { name := f.name, exported := f.exported, params := f.params.map (·.2),
    body := localProg (f.params.map (·.2)) (blockTree f.body) }

/-- The gate's shapes, in a function: parameters of one word. -/
structure FunShape (f : PFun) : Prop where
  params : ∀ p ∈ f.params, p.1 = 1
  body : SShapes f.body

theorem pMore_comma {j : Nat} {ps : List String} {v : String} {ts : List Tok} :
    pParams.more (j + 1) ps (.sym "," :: .int 1 :: .ident v :: ts) = pParams.more j (ps ++ [v]) ts := by
  rw [pParams.more.eq_def]; simp [pShaped]

theorem pMore_close {j : Nat} {ps : List String} {ts : List Tok} :
    pParams.more (j + 1) ps (.sym ")" :: ts) = some (ps, .sym ")" :: ts) := by
  rw [pParams.more.eq_def]; split <;> simp_all

theorem pFunc_plain {k : Nat} {n : String} {ts ts' rest : List Tok} {ps : List String} {b : Prog}
    (hp : pParams ts = some (ps, .sym ")" :: .sym "{" :: ts')) (hb : pTry k ts' = some (b, rest)) :
    pFunc k (.kw "fun" :: .ident n :: .sym "(" :: ts) =
      some ({ name := n, exported := false, params := ps, body := localProg ps b }, rest) := by
  simp [pFunc, pShaped, hp, hb]
theorem pFunc_export {k : Nat} {n : String} {ts ts' rest : List Tok} {ps : List String} {b : Prog}
    (hp : pParams ts = some (ps, .sym ")" :: .sym "{" :: ts')) (hb : pTry k ts' = some (b, rest)) :
    pFunc k (.kw "export" :: .kw "fun" :: .ident n :: .sym "(" :: ts) =
      some ({ name := n, exported := true, params := ps, body := localProg ps b }, rest) := by
  simp [pFunc, pShaped, hp, hb]
theorem pFuncs_cons {k j : Nat} {ts : List Tok} (h : ts ≠ []) :
    pFuncs k (j + 1) ts = (pFunc k ts).bind fun r => (pFuncs k j r.2).map (r.1 :: ·) := by
  cases ts with
  | nil => exact absurd rfl h
  | cons t ts' =>
    rw [pFuncs.eq_def]; simp only [Option.bind_eq_bind]
    cases pFunc k (t :: ts') with
    | none => rfl
    | some r => simp only [Option.bind_some]; cases pFuncs k j r.2 <;> rfl

theorem commaParams_len (ps : List (Nat × String)) :
    (ps.flatMap fun p => [Tok.sym ",", .int p.1, .ident p.2]).length = 3 * ps.length := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢; simp at ih ⊢; omega

theorem paramToks_len (ps : List (Nat × String)) : 2 * ps.length ≤ (paramToks ps).length + 1 := by
  induction ps with
  | nil => simp [paramToks]
  | cons p ps ih =>
    cases ps with
    | nil => simp [paramToks]
    | cons q qs => simp only [paramToks, List.length_cons] at ih ⊢; omega

theorem more_params : ∀ (ps : List (Nat × String)), (∀ p ∈ ps, p.1 = 1) → ∀ (acc : List String)
    (rest : List Tok) (j : Nat), ps.length + 1 ≤ j →
    pParams.more j acc ((ps.flatMap fun p => [.sym ",", .int p.1, .ident p.2]) ++ .sym ")" :: rest) =
      some (acc ++ ps.map (·.2), .sym ")" :: rest)
  | [], _, acc, rest, j, hj => by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp at hj; omega⟩
    simpa using pMore_close
  | p :: ps, h, acc, rest, j, hj => by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp at hj; omega⟩
    obtain ⟨n, v⟩ := p
    have hn : n = 1 := h (n, v) (by simp)
    subst hn
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    rw [pMore_comma, more_params ps (fun q hq => h q (by simp [hq])) _ rest i (by simp at hj; omega)]
    simp

theorem paramToks_cons (p : Nat × String) (ps : List (Nat × String)) :
    paramToks (p :: ps) = .int p.1 :: .ident p.2 :: ps.flatMap fun q => [.sym ",", .int q.1, .ident q.2] := by
  induction ps generalizing p with
  | nil => simp [paramToks]
  | cons q qs ih => simp only [paramToks, ih q]; simp

theorem params_read (ps : List (Nat × String)) (h : ∀ p ∈ ps, p.1 = 1) (rest : List Tok) :
    pParams (paramToks ps ++ .sym ")" :: rest) = some (ps.map (·.2), .sym ")" :: rest) := by
  cases ps with
  | nil => simp [paramToks, pParams]
  | cons p ps =>
    obtain ⟨n, v⟩ := p
    have hn : n = 1 := h (n, v) (by simp)
    subst hn
    rw [paramToks_cons]
    simp only [List.cons_append, pParams, pShaped, Option.bind_eq_bind, Option.bind_some]
    rw [more_params ps (fun q hq => h q (by simp [hq])) [v] rest _
      (by simp only [List.length_append, List.length_cons, commaParams_len]; omega)]
    simp

theorem funToks_len (f : PFun) : (stmtsToks f.body).length + 6 ≤ (funToks f).length := by
  simp only [funToks, List.length_append, List.length_cons]; omega

theorem fun_read (f : PFun) (h : FunShape f) (rest : List Tok) (k : Nat)
    (hk : 12 * (stmtsToks f.body).length + 13 ≤ k) :
    pFunc k (funToks f ++ rest) = some (funTree f, rest) := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
  have hb := try_of_prog (stmts_read f.body rest i h.body (by omega))
  have hp := params_read f.params h.params (.sym "{" :: (stmtsToks f.body ++ .sym "}" :: rest))
  simp only [funToks, List.append_assoc, List.cons_append, List.nil_append]
  cases hx : f.exported
  · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
    rw [pFunc_plain hp hb]; simp [funTree, hx]
  · simp only [↓reduceIte, List.singleton_append]
    rw [pFunc_export hp hb]; simp [funTree, hx]

theorem funs_read (k : Nat) : ∀ (fs : List PFun), (∀ f ∈ fs, FunShape f) →
    (∀ f ∈ fs, 12 * (stmtsToks f.body).length + 13 ≤ k) → ∀ j, fs.length ≤ j →
      pFuncs k j (fs.flatMap funToks) = some (fs.map funTree)
  | [], _, _, j, _ => by cases j <;> simp [pFuncs]
  | f :: fs, hs, hk, j, hj => by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp at hj; omega⟩
    rw [List.flatMap_cons, pFuncs_cons (by simp [funToks]),
      fun_read f (hs f (by simp)) _ k (hk f (by simp))]
    simp only [Option.bind_some]
    rw [funs_read k fs (fun g hg => hs g (by simp [hg])) (fun g hg => hk g (by simp [hg])) i
      (by simp at hj; omega)]
    rfl

theorem funs_len : ∀ (fs : List PFun), fs.length ≤ (fs.flatMap funToks).length
  | [] => by simp
  | g :: gs => by
    have := funToks_len g; have := funs_len gs
    simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega

theorem body_le (fs : List PFun) : ∀ f ∈ fs, (stmtsToks f.body).length ≤ (fs.flatMap funToks).length := by
  intro f hf
  have h1 := funToks_len f
  have h2 : (funToks f).length ≤ (fs.flatMap funToks).length := by
    induction fs with
    | nil => cases hf
    | cons g gs ih =>
      rcases List.mem_cons.mp hf with rfl | hm
      · simp
      · have := ih hm; simp only [List.flatMap_cons, List.length_append]; omega
  omega

/-- **The parser reads a printed program as the trees of its functions.** -/
theorem program_reads (fs : List PFun) (hn : ∀ f ∈ fs, FunNames f) (hs : ∀ f ∈ fs, FunShape f) :
    program (String.intercalate "\n" (fs.map ppFun)) = some (fs.map funTree) := by
  rw [program, lex_program fs hn]
  simp only [Option.bind_eq_bind, Option.bind_some]
  refine funs_read _ fs hs (fun f hf => ?_) _ ?_
  · have := body_le fs f hf; omega
  · have := funs_len fs; omega

/-! ## The trees, read in the model

A tree of the parser read as an expression of `DN.Compiler.Semantics`: an operator over a list of
operands folded from the left. Its canonical form is the lowering's, so it evaluates as the lowering
does (`Canon.canon_eval`). -/

def binopOf : String → Binop
  | "And" => .and_ | "Xor" => .xor | "Or" => .or_ | "Sub" => .sub | _ => .add

def cmpOfName : String → Cmp
  | "Less" => .less | "NotLess" => .notLess | _ => .equal

mutual
/-- **A tree read in the model**, its names' locality aside: an operator over its operands folded
from the left, by the names `binopOf` and `cmpOfName` read. Any other operator name reads as `Add`,
any other comparison as `Equal`, a shift but `Lsr` as `Lsl`, and an operator of no operands or a
product of other than two as `0`. So this tells apart only the names `tree` gives; that they are
CakeML's, the parser lane holds against HOL4. -/
def plain : Exp → PancakeExp
  | .const w => .const (BitVec.ofNat 64 w)
  | .var _ x => .var x
  | .base => .base
  | .op o (e :: es) => plainFold (binopOf o) (plain e) es
  | .op _ [] => .const 0
  | .mul [a, b] => .mul (plain a) (plain b)
  | .mul _ => .const 0
  | .cmp c a b => .cmp (cmpOfName c) (plain a) (plain b)
  | .shift s e n =>
    if s = "Lsr" then .shiftR (plain e) (.const (BitVec.ofNat 64 n))
    else .shiftL (plain e) (.const (BitVec.ofNat 64 n))
  | .load e => .loadWord (plain e)
  | .loadByte e => .loadByte (plain e)
def plainFold (b : Binop) (acc : PancakeExp) : List Exp → PancakeExp
  | [] => acc
  | e :: es => plainFold b (.op b acc (plain e)) es
end

/-! ### Chains, by their operands -/

open DN.Compiler.Canon (canon opChain mulChain)

/-- The operands of a chain of `o`, as far down as it goes. -/
def leaves (o : Binop) : PancakeExp → List PancakeExp
  | .op o' l r => if o' = o then leaves o l ++ leaves o r else [.op o' l r]
  | e => [e]

/-- A chain of `o` nested to the right, as the canonical form has it. -/
def Chainy (o : Binop) : PancakeExp → Prop
  | .op o' l r => o' = o → (∀ a b, l ≠ .op o a b) ∧ Chainy o r
  | _ => True

/-- The operator chains the canonical form nests to the right. -/
def Assoc (o : Binop) : Prop := o = .add ∨ o = .and_ ∨ o = .xor ∨ o = .or_

theorem leaves_ne_nil (o : Binop) : ∀ e, leaves o e ≠ []
  | .op o' l r => by
    unfold leaves; split
    · exact fun h => leaves_ne_nil o l (List.append_eq_nil_iff.mp h).1
    · simp
  | .const _ | .var _ | .base | .mul _ _ | .cmp _ _ _ | .loadByte _ | .loadWord _ | .shiftR _ _
  | .shiftL _ _ => by simp [leaves]

theorem leaves_opChain (o : Binop) : ∀ x y, leaves o (opChain o x y) = leaves o x ++ leaves o y
  | .op o' a b, y => by
    by_cases h : o' = o
    · subst h; simp only [opChain, if_pos, leaves, leaves_opChain o' b y]; simp
    · simp [opChain, h, leaves]
  | .const _, _ | .var _, _ | .base, _ | .mul _ _, _ | .cmp _ _ _, _ | .loadByte _, _
  | .loadWord _, _ | .shiftR _ _, _ | .shiftL _ _, _ => by simp [opChain, leaves]

theorem chainy_opChain (o : Binop) : ∀ x y, Chainy o x → Chainy o y → Chainy o (opChain o x y)
  | .op o' a b, y, hx, hy => by
    by_cases h : o' = o
    · subst h
      simp only [opChain, if_pos]
      exact fun _ => ⟨(hx rfl).1, chainy_opChain o' b y (hx rfl).2 hy⟩
    · simp only [opChain, h, if_false]
      exact fun _ => ⟨fun a' b' he => (by cases he; exact h rfl), hy⟩
  | .const _, _, _, hy | .var _, _, _, hy | .base, _, _, hy | .mul _ _, _, _, hy
  | .cmp _ _ _, _, _, hy | .loadByte _, _, _, hy | .loadWord _, _, _, hy | .shiftR _ _, _, _, hy
  | .shiftL _ _, _, _, hy => by
    simp only [opChain]; exact fun _ => ⟨fun a b he => (by cases he), hy⟩

theorem opChain_isOp (o : Binop) : ∀ x y, ∃ a b, opChain o x y = .op o a b
  | .op o' _ _, _ => by
    by_cases h : o' = o
    · subst h; simp only [opChain, if_pos]; exact ⟨_, _, rfl⟩
    · simp only [opChain, h, if_false]; exact ⟨_, _, rfl⟩
  | .const _, _ | .var _, _ | .base, _ | .mul _ _, _ | .cmp _ _ _, _ | .loadByte _, _
  | .loadWord _, _ | .shiftR _ _, _ | .shiftL _ _, _ => ⟨_, _, rfl⟩

theorem mulChain_isMul : ∀ x y, ∃ a b, mulChain x y = .mul a b
  | .mul _ _, _ => ⟨_, _, rfl⟩
  | .op _ _ _, _ | .const _, _ | .var _, _ | .base, _ | .cmp _ _ _, _ | .loadByte _, _
  | .loadWord _, _ | .shiftR _ _, _ | .shiftL _ _, _ => ⟨_, _, rfl⟩

theorem chainy_of_opChain {o o' : Binop} {x y : PancakeExp} (hx : Chainy o x) (hy : Chainy o y) :
    Chainy o (opChain o' x y) := by
  by_cases h : o' = o
  · subst h; exact chainy_opChain _ _ _ hx hy
  · obtain ⟨a, b, hab⟩ := opChain_isOp o' x y
    rw [hab]; simp only [Chainy]; intro he; exact absurd he h

theorem chainy_canon {o : Binop} (ho : Assoc o) : ∀ e, Chainy o (canon e)
  | .op o' l r => by
    have hl := chainy_canon ho l
    have hr := chainy_canon ho r
    cases o'
    case sub =>
      simp only [canon, Chainy]; intro h; subst h; rcases ho with h | h | h | h <;> cases h
    all_goals simp only [canon]; exact chainy_of_opChain hl hr
  | .mul l r => by
    simp only [canon]; obtain ⟨a, b, h⟩ := mulChain_isMul (canon l) (canon r); rw [h]; trivial
  | .const _ | .var _ | .base | .cmp _ _ _ | .loadByte _ | .loadWord _ | .shiftR _ _
  | .shiftL _ _ => by simp [canon, Chainy]

theorem leaves_single {o : Binop} {z : PancakeExp} (h : ∀ a b, z ≠ .op o a b) : leaves o z = [z] := by
  cases z with
  | op o' a b => simp only [leaves]; rw [if_neg]; intro he; subst he; exact h a b rfl
  | _ => rfl

theorem leaves_op (o : Binop) (a b : PancakeExp) : leaves o (.op o a b) = leaves o a ++ leaves o b := by
  simp [leaves]

theorem leaves_op_len (o : Binop) (a b : PancakeExp) : 2 ≤ (leaves o (.op o a b)).length := by
  rw [leaves_op, List.length_append]
  have h1 := leaves_ne_nil o a; have h2 := leaves_ne_nil o b
  have := List.length_pos_iff.mpr h1; have := List.length_pos_iff.mpr h2; omega

theorem chainy_ext {o : Binop} : ∀ z w, Chainy o z → Chainy o w → leaves o z = leaves o w → z = w
  | .op o' a b, w, hz, hw, h => by
    by_cases ho : o' = o
    · subst ho
      obtain ⟨ha, hb⟩ := hz rfl
      rw [leaves_op, leaves_single ha] at h
      by_cases hw' : ∃ c d, w = .op o' c d
      · obtain ⟨c, d, rfl⟩ := hw'
        obtain ⟨hc, hd⟩ := hw rfl
        rw [leaves_op, leaves_single hc, List.singleton_append, List.singleton_append,
          List.cons.injEq] at h
        rw [h.1, chainy_ext b d hb hd h.2]
      · rw [leaves_single (fun c d he => hw' ⟨c, d, he⟩), List.singleton_append, List.cons.injEq] at h
        exact absurd h.2 (leaves_ne_nil _ _)
    · have hz1 : ∀ c d, PancakeExp.op o' a b ≠ .op o c d := fun c d he => by cases he; exact ho rfl
      exact ext_single hz1 hw h
  | .const _, w, _, hw, h | .var _, w, _, hw, h | .base, w, _, hw, h | .mul _ _, w, _, hw, h
  | .cmp _ _ _, w, _, hw, h | .loadByte _, w, _, hw, h | .loadWord _, w, _, hw, h
  | .shiftR _ _, w, _, hw, h | .shiftL _ _, w, _, hw, h =>
    ext_single (fun c d he => by cases he) hw h
where
  ext_single {z w : PancakeExp} (hz : ∀ c d, z ≠ .op o c d) (_ : Chainy o w)
      (h : leaves o z = leaves o w) : z = w := by
    rw [leaves_single hz] at h
    by_cases hw' : ∃ c d, w = .op o c d
    · obtain ⟨c, d, rfl⟩ := hw'
      have := leaves_op_len o c d; rw [← h] at this; simp at this
    · rw [leaves_single (fun c d he => hw' ⟨c, d, he⟩)] at h; simpa using h

/-! ### Products, by their factors -/

def mleaves : PancakeExp → List PancakeExp
  | .mul l r => mleaves l ++ mleaves r
  | e => [e]

def MChainy : PancakeExp → Prop
  | .mul l r => (∀ a b, l ≠ .mul a b) ∧ MChainy r
  | _ => True

theorem mleaves_ne_nil : ∀ e, mleaves e ≠ []
  | .mul l r => by simp only [mleaves]; exact fun h => mleaves_ne_nil l (List.append_eq_nil_iff.mp h).1
  | .op _ _ _ | .const _ | .var _ | .base | .cmp _ _ _ | .loadByte _ | .loadWord _ | .shiftR _ _
  | .shiftL _ _ => by simp [mleaves]

theorem mleaves_mulChain : ∀ x y, mleaves (mulChain x y) = mleaves x ++ mleaves y
  | .mul a b, y => by simp only [mulChain, mleaves, mleaves_mulChain b y]; simp
  | .op _ _ _, _ | .const _, _ | .var _, _ | .base, _ | .cmp _ _ _, _ | .loadByte _, _
  | .loadWord _, _ | .shiftR _ _, _ | .shiftL _ _, _ => by simp [mulChain, mleaves]

theorem mchainy_mulChain : ∀ x y, MChainy x → MChainy y → MChainy (mulChain x y)
  | .mul a b, y, hx, hy => by
    simp only [mulChain, MChainy] at hx ⊢; exact ⟨hx.1, mchainy_mulChain b y hx.2 hy⟩
  | .op _ _ _, _, _, hy | .const _, _, _, hy | .var _, _, _, hy | .base, _, _, hy
  | .cmp _ _ _, _, _, hy | .loadByte _, _, _, hy | .loadWord _, _, _, hy | .shiftR _ _, _, _, hy
  | .shiftL _ _, _, _, hy => by simp only [mulChain, MChainy]; exact ⟨fun a b he => (by cases he), hy⟩

theorem mchainy_canon : ∀ e, MChainy (canon e)
  | .mul l r => by simp only [canon]; exact mchainy_mulChain _ _ (mchainy_canon l) (mchainy_canon r)
  | .op o l r => by
    cases o
    case sub => simp [canon, MChainy]
    all_goals simp only [canon]; obtain ⟨a, b, h⟩ := opChain_isOp _ (canon l) (canon r); rw [h]; trivial
  | .const _ | .var _ | .base | .cmp _ _ _ | .loadByte _ | .loadWord _ | .shiftR _ _
  | .shiftL _ _ => by simp [canon, MChainy]

theorem mleaves_single {z : PancakeExp} (h : ∀ a b, z ≠ .mul a b) : mleaves z = [z] := by
  cases z with
  | mul a b => exact absurd rfl (h a b)
  | _ => rfl

theorem mchainy_ext : ∀ z w, MChainy z → MChainy w → mleaves z = mleaves w → z = w
  | .mul a b, w, hz, hw, h => by
    obtain ⟨ha, hb⟩ := hz
    simp only [mleaves, mleaves_single ha, List.singleton_append] at h
    cases w with
    | mul c d =>
      obtain ⟨hc, hd⟩ := hw
      simp only [mleaves, mleaves_single hc, List.singleton_append, List.cons.injEq] at h
      rw [h.1, mchainy_ext b d hb hd h.2]
    | _ => simp only [mleaves, List.cons.injEq] at h; exact absurd h.2 (mleaves_ne_nil _)
  | .op _ _ _, w, _, hw, h | .const _, w, _, hw, h | .var _, w, _, hw, h | .base, w, _, hw, h
  | .cmp _ _ _, w, _, hw, h | .loadByte _, w, _, hw, h | .loadWord _, w, _, hw, h
  | .shiftR _ _, w, _, hw, h | .shiftL _ _, w, _, hw, h => by
    cases w with
    | mul c d =>
      obtain ⟨hc, _⟩ := hw
      simp only [mleaves, mleaves_single hc, List.singleton_append, List.cons.injEq] at h
      exact absurd h.2.symm (mleaves_ne_nil _)
    | _ => first | rfl | (simp [mleaves] at h; done) | simpa [mleaves] using h

/-! ### The trees of chains, read and canonical -/

theorem canon_assoc {o : Binop} (ho : Assoc o) (x y : PancakeExp) :
    canon (.op o x y) = opChain o (canon x) (canon y) := by
  rcases ho with rfl | rfl | rfl | rfl <;> rfl

/-- What a chain's operands give. -/
def flatL (o : Binop) (ts : List Exp) : List PancakeExp := ts.flatMap fun t => leaves o (canon (plain t))

theorem leaves_fold {o : Binop} (ho : Assoc o) : ∀ (es : List Exp) (acc : PancakeExp),
    leaves o (canon (plainFold o acc es)) = leaves o (canon acc) ++ flatL o es
  | [], acc => by simp [plainFold, flatL]
  | e :: es, acc => by
    rw [plainFold, leaves_fold ho es, canon_assoc ho, leaves_opChain]
    simp [flatL]

theorem binopOf_name {o : Binop} (ho : Assoc o) {name : String} (hn : binopOf name = o)
    (e : Exp) (es : List Exp) : leaves o (canon (plain (.op name (e :: es)))) = flatL o (e :: es) := by
  simp only [plain, hn, leaves_fold ho]; simp [flatL]

theorem tree_ops_ne : ∀ (x : PExpr) (o : String) (es : List Exp), tree x = .op o es → es ≠ []
  | .binop op l r, o, es, h => by
    cases op
    case mul => obtain ⟨a, b, hm⟩ := tree_mul_isMul l r; rw [hm] at h; cases h
    case and_ =>
      simp only [tree] at h; unfold joined at h
      split at h
      · split at h <;> (simp at h; obtain ⟨_, rfl⟩ := h; simp)
      · simp at h; obtain ⟨_, rfl⟩ := h; simp
    case sub => simp [tree] at h; rw [← h.2]; simp
    case lt | le | eq => simp [tree] at h
    all_goals
      simp [tree] at h; rw [← h.2]
      cases hl : tree l <;> simp [opsOf]
      split
      · rename_i o' es' _; have := tree_ops_ne l o' es' hl; simp [this]
      · simp
  | .base, _, _, h | .const _, _, _, h | .var _, _, _, h | .loadw _ _, _, _, h | .loadb _, _, _, h
  | .shr _ _, _, _, h | .shl _ _, _, _, h => by simp [tree] at h

theorem flatL_opsOf {o : Binop} (ho : Assoc o) {name : String} (hn : binopOf name = o) (x : PExpr) :
    flatL o (opsOf name (tree x)) = leaves o (canon (plain (tree x))) := by
  unfold opsOf
  split
  · rename_i b es heq
    split
    · rename_i hb; subst hb
      cases es with
      | nil => exact absurd rfl (tree_ops_ne x _ _ heq)
      | cons e es => rw [heq, binopOf_name ho hn]
    · rw [heq]; simp [flatL]
  · simp [flatL]

theorem leaves_joined {x y : PExpr} :
    leaves .and_ (canon (plain (joined "And" (tree x) (tree y)))) =
      leaves .and_ (canon (plain (tree x))) ++ leaves .and_ (canon (plain (tree y))) := by
  have ho : Assoc .and_ := by simp [Assoc]
  unfold joined
  split
  · rename_i b es heq
    split
    · rw [binopOf_name ho rfl]; simp [flatL]
    · rename_i hb
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Classical.not_not] at hb
      obtain ⟨hb1, _⟩ := hb
      subst hb1
      cases es with
      | nil => exact absurd rfl (tree_ops_ne x _ _ heq)
      | cons e es =>
        rw [List.cons_append, binopOf_name ho (name := "And") rfl, heq,
          binopOf_name ho (name := "And") rfl]
        simp [flatL]
  · rw [binopOf_name ho rfl]; simp [flatL]

def flatM (ts : List Exp) : List PancakeExp := ts.flatMap fun t => mleaves (canon (plain t))

theorem mleaves_fold : ∀ (es : List Exp) (acc : Exp),
    mleaves (canon (plain (es.foldl (fun r e => .mul [r, e]) acc))) = mleaves (canon (plain acc)) ++ flatM es
  | [], acc => by simp [flatM]
  | e :: es, acc => by
    rw [List.foldl_cons, mleaves_fold es]
    simp [plain, canon, mleaves_mulChain, flatM]

theorem flatM_mulOps : ∀ t : Exp, flatM (mulOps t) = mleaves (canon (plain t))
  | .mul [x, y] => by
    rw [mulOps, show flatM (mulOps x ++ [y]) = flatM (mulOps x) ++ flatM [y] by simp [flatM],
      flatM_mulOps x]
    simp [flatM, plain, canon, mleaves_mulChain]
  | .mul [] | .mul [_] | .mul (_ :: _ :: _ :: _) | .const _ | .var _ _ | .base | .op _ _
  | .cmp _ _ _ | .shift _ _ _ | .load _ | .loadByte _ => by simp [mulOps, flatM]

theorem ofNat_word (n : Nat) : BitVec.ofNat 64 (word n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp [word]

/-- **A printed expression's tree, read in the model, has the lowering's canonical form.** -/
theorem canon_tree : ∀ (e : PExpr), Shape e → ∀ q, Lower.lowerExp e = some q →
    canon (plain (tree e)) = canon q
  | .base, _, q, h => by simp [Lower.lowerExp] at h; subst h; rfl
  | .const n, _, q, h => by
    simp [Lower.lowerExp] at h; subst h; simp [tree, plain, canon, ofNat_word]
  | .var x, _, q, h => by simp [Lower.lowerExp] at h; subst h; rfl
  | .binop op l r, hs, q, h => by
    simp only [Lower.lowerExp] at h
    cases hl : Lower.lowerExp l with
    | none => rw [hl] at h; cases h
    | some a =>
      cases hr : Lower.lowerExp r with
      | none => rw [hl, hr] at h; cases h
      | some b =>
        rw [hl, hr] at h
        have il := canon_tree l hs.1 a hl
        have ir := canon_tree r hs.2 b hr
        have chain : ∀ (o : Binop) (name : String), Assoc o → binopOf name = o →
            q = .op o a b → tree (.binop op l r) = .op name (opsOf name (tree l) ++ opsOf name (tree r)) →
            canon (plain (tree (.binop op l r))) = canon q := by
          intro o name ho hn hq ht
          subst hq
          rw [ht]
          have hne : opsOf name (tree l) ++ opsOf name (tree r) ≠ [] := by
            unfold opsOf; split
            · split
              · rename_i es heq _; simp [tree_ops_ne l _ es heq]
              · simp
            · simp
          refine chainy_ext _ _ (chainy_canon ho _) (chainy_canon ho _) ?_
          cases hes : opsOf name (tree l) ++ opsOf name (tree r) with
          | nil => exact absurd hes hne
          | cons t ts =>
            rw [binopOf_name ho hn, ← hes, canon_assoc ho, leaves_opChain]
            simp only [flatL, List.flatMap_append]
            rw [← flatL, ← flatL, flatL_opsOf ho hn, flatL_opsOf ho hn, il, ir]
        cases op with
        | add => simp only at h; cases h; exact chain .add "Add" (by simp [Assoc]) rfl rfl rfl
        | xor => simp only at h; cases h; exact chain .xor "Xor" (by simp [Assoc]) rfl rfl rfl
        | or_ => simp only at h; cases h; exact chain .or_ "Or" (by simp [Assoc]) rfl rfl rfl
        | and_ =>
          simp only at h; cases h
          have ho : Assoc .and_ := by simp [Assoc]
          refine chainy_ext _ _ (chainy_canon ho _) (chainy_canon ho _) ?_
          simp only [tree]
          rw [leaves_joined, il, ir, canon_assoc ho, leaves_opChain]
        | sub => simp only at h; cases h; simp [tree, plain, plainFold, binopOf, canon, il, ir]
        | mul =>
          simp only at h; cases h
          refine mchainy_ext _ _ (mchainy_canon _) (mchainy_canon _) ?_
          simp only [tree]
          cases hm : mulOps (tree l) ++ mulOps (tree r) with
          | nil =>
            have := mulOps_ne_nil (tree l); simp_all
          | cons t ts =>
            have h1 : mleaves (canon (plain t)) ++ flatM ts = flatM (t :: ts) := by simp [flatM]
            rw [mulTree, mleaves_fold, h1, ← hm]
            have h2 : flatM (mulOps (tree l) ++ mulOps (tree r)) =
                flatM (mulOps (tree l)) ++ flatM (mulOps (tree r)) := by simp [flatM]
            rw [h2, flatM_mulOps, flatM_mulOps, il, ir]
            simp [canon, mleaves_mulChain]
        | lt => simp only at h; cases h; simp [tree, plain, cmpOfName, canon, il, ir]
        | le => simp only at h; cases h; simp [tree, plain, cmpOfName, canon, il, ir]
        | eq => simp only at h; cases h; simp [tree, plain, cmpOfName, canon, il, ir]
  | .loadw sh a, hs, q, h => by
    obtain ⟨rfl, ha⟩ := hs
    simp only [Lower.lowerExp] at h
    cases hl : Lower.lowerExp a with
    | none => rw [hl] at h; cases h
    | some a' => rw [hl] at h; cases h; simp [tree, plain, canon, canon_tree a ha a' hl]
  | .loadb a, hs, q, h => by
    simp only [Lower.lowerExp] at h
    cases hl : Lower.lowerExp a with
    | none => rw [hl] at h; cases h
    | some a' => rw [hl] at h; cases h; simp [tree, plain, canon, canon_tree a hs a' hl]
  | .shr l r, hs, q, h => by
    obtain ⟨⟨n, rfl⟩, hl'⟩ := hs
    simp only [Lower.lowerExp] at h
    cases hl : Lower.lowerExp l with
    | none => rw [hl] at h; cases h
    | some a => rw [hl] at h; cases h; simp [tree, plain, canon, distance, canon_tree l hl' a hl]
  | .shl l r, hs, q, h => by
    obtain ⟨⟨n, rfl⟩, hl'⟩ := hs
    simp only [Lower.lowerExp] at h
    cases hl : Lower.lowerExp l with
    | none => rw [hl] at h; cases h
    | some a => rw [hl] at h; cases h; simp [tree, plain, canon, distance, canon_tree l hl' a hl]

/-! ### Statements, read and canonical -/

/-- A statement's tree read in the model, its names' locality aside. -/
def plainProg : Prog → PancakeProg
  | .skip => .skip
  | .dec v e p => .dec v (plain e) (plainProg p)
  | .assign _ v e => .assign v (plain e)
  | .store a e => .store (plain a) (plain e)
  | .storeByte a e => .storeByte (plain a) (plain e)
  | .seq p q => .seq (plainProg p) (plainProg q)
  | .ite e p q => .cond (plain e) (plainProg p) (plainProg q)
  | .while e p => .while_ (plain e) (plainProg p)
  | .ret e => .ret (plain e)
  | .extCall n a b c d => .extCall n (plain a) (plain b) (plain c) (plain d)
  | .decCall v f es p => .decCall v f (es.map plain) (plainProg p)

/-- A program with every expression in canonical form. -/
def canonProg : PancakeProg → PancakeProg
  | .skip => .skip
  | .dec v e c => .dec v (canon e) (canonProg c)
  | .assign v e => .assign v (canon e)
  | .store a e => .store (canon a) (canon e)
  | .extCall n a b c d => .extCall n (canon a) (canon b) (canon c) (canon d)
  | .seq p q => .seq (canonProg p) (canonProg q)
  | .cond e p q => .cond (canon e) (canonProg p) (canonProg q)
  | .while_ e c => .while_ (canon e) (canonProg c)
  | .ret e => .ret (canon e)
  | .storeByte a e => .storeByte (canon a) (canon e)
  | .decCall r f as c => .decCall r f (as.map canon) (canonProg c)

theorem canon_args : ∀ (as : List PExpr), (∀ a ∈ as, Shape a) → ∀ bs, Lower.lowerArgs as = some bs →
    ((as.map tree).map plain).map canon = bs.map canon
  | [], _, bs, h => by simp [Lower.lowerArgs] at h; subst h; rfl
  | a :: as, hs, bs, h => by
    simp only [Lower.lowerArgs] at h
    cases ha : Lower.lowerExp a with
    | none => rw [ha] at h; cases h
    | some a' =>
      cases has : Lower.lowerArgs as with
      | none => rw [ha, has] at h; cases h
      | some as' =>
        rw [ha, has] at h; cases h
        simp only [List.map_cons]
        rw [canon_tree a (hs a (by simp)) a' ha,
          canon_args as (fun x hx => hs x (by simp [hx])) as' has]

/-- A block's first statement and the rest, given what each of them gives. -/
theorem block_case (s : PStmt) (ss : List PStmt)
    (ihs : ∀ b, Lower.lowerStmt1 s = some b → canonProg (plainProg (stmtTree s)) = canonProg b)
    (ihb : ∀ b, Lower.lowerStmtsFold ss = some b → canonProg (plainProg (blockTree ss)) = canonProg b)
    (hs : SShapes (s :: ss)) (b : PancakeProg) (h : Lower.lowerStmtsFold (s :: ss) = some b) :
    canonProg (plainProg (blockTree (s :: ss))) = canonProg b := by
  cases ss with
  | nil => rw [Lower.lowerStmtsFold] at h; simp only [blockTree]; exact ihs b h
  | cons s' ss' =>
    have generic : ∀ {bx br}, Lower.lowerStmt1 s = some bx → Lower.lowerStmtsFold (s' :: ss') = some br →
        b = .seq bx br → blockTree (s :: s' :: ss') = .seq (stmtTree s) (blockTree (s' :: ss')) →
        canonProg (plainProg (blockTree (s :: s' :: ss'))) = canonProg b := by
      intro bx br h1 h2 h3 h4
      rw [h4, h3]; simp only [plainProg, canonProg]; rw [ihs bx h1, ihb br h2]
    cases s
    case dec n v =>
      simp only [Lower.lowerStmtsFold] at h
      cases hv : Lower.lowerExp v <;> cases hr : Lower.lowerStmtsFold (s' :: ss') <;>
        simp only [hv, hr, reduceCtorEq] at h
      cases h
      simp [blockTree, plainProg, canonProg, canon_tree v hs.1 _ hv, ihb _ hr]
    case call r f as =>
      simp only [Lower.lowerStmtsFold] at h
      cases has : Lower.lowerArgs as <;> cases hr : Lower.lowerStmtsFold (s' :: ss') <;>
        simp only [has, hr, reduceCtorEq] at h
      cases h
      have := canon_args as hs.1.2 _ has
      simp only [List.map_map] at this
      simp [blockTree, plainProg, canonProg, this, ihb _ hr]
    all_goals
      simp only [Lower.lowerStmtsFold] at h
      split at h
      · rename_i bx br h1 h2; cases h; exact generic h1 h2 rfl rfl
      · cases h

mutual
theorem canon_stmt : ∀ (s : PStmt), SShape s → ∀ b, Lower.lowerStmt1 s = some b →
    canonProg (plainProg (stmtTree s)) = canonProg b
  | .dec n v, hs, b, h => by
    simp only [Lower.lowerStmt1] at h
    cases hv : Lower.lowerExp v with
    | none => rw [hv] at h; cases h
    | some v' => rw [hv] at h; cases h; simp [stmtTree, plainProg, canonProg, canon_tree v hs v' hv]
  | .assign n v, hs, b, h => by
    simp only [Lower.lowerStmt1] at h
    cases hv : Lower.lowerExp v with
    | none => rw [hv] at h; cases h
    | some v' => rw [hv] at h; cases h; simp [stmtTree, plainProg, canonProg, canon_tree v hs v' hv]
  | .ret v, hs, b, h => by
    simp only [Lower.lowerStmt1] at h
    cases hv : Lower.lowerExp v with
    | none => rw [hv] at h; cases h
    | some v' => rw [hv] at h; cases h; simp [stmtTree, plainProg, canonProg, canon_tree v hs v' hv]
  | .store a v, hs, b, h => by
    simp only [Lower.lowerStmt1] at h
    cases ha : Lower.lowerExp a with
    | none => rw [ha] at h; cases h
    | some a' =>
      cases hv : Lower.lowerExp v with
      | none => rw [ha, hv] at h; cases h
      | some v' =>
        rw [ha, hv] at h; cases h
        simp [stmtTree, plainProg, canonProg, canon_tree a hs.1 a' ha, canon_tree v hs.2 v' hv]
  | .storeb a v, hs, b, h => by
    simp only [Lower.lowerStmt1] at h
    cases ha : Lower.lowerExp a with
    | none => rw [ha] at h; cases h
    | some a' =>
      cases hv : Lower.lowerExp v with
      | none => rw [ha, hv] at h; cases h
      | some v' =>
        rw [ha, hv] at h; cases h
        simp [stmtTree, plainProg, canonProg, canon_tree a hs.1 a' ha, canon_tree v hs.2 v' hv]
  | .ffi n args, hs, b, h => by
    obtain ⟨hlen, hargs⟩ := hs
    match args, hlen, hargs, h with
    | [c, cl, a, al], _, hargs, h =>
      simp only [Lower.lowerStmt1] at h
      cases h1 : Lower.lowerExp c <;> cases h2 : Lower.lowerExp cl <;> cases h3 : Lower.lowerExp a <;>
        cases h4 : Lower.lowerExp al <;> simp only [h1, h2, h3, h4, reduceCtorEq] at h
      cases h
      simp [stmtTree, plainProg, canonProg, canon_tree c (hargs c (by simp)) _ h1,
        canon_tree cl (hargs cl (by simp)) _ h2, canon_tree a (hargs a (by simp)) _ h3,
        canon_tree al (hargs al (by simp)) _ h4]
  | .call r f as, hs, b, h => by
    simp only [Lower.lowerStmt1] at h
    cases has : Lower.lowerArgs as with
    | none => rw [has] at h; cases h
    | some as' =>
      rw [has] at h; cases h
      simp only [stmtTree, plainProg, canonProg, List.map_map]
      have := canon_args as hs.2 as' has
      simp only [List.map_map] at this
      rw [this]
  | .ite c t e, hs, b, h => by
    simp only [Lower.lowerStmt1] at h
    cases hc : Lower.lowerExp c <;> cases ht : Lower.lowerStmtsFold t <;>
      cases he : Lower.lowerStmtsFold e <;> simp only [hc, ht, he, reduceCtorEq] at h
    cases h
    simp [stmtTree, plainProg, canonProg, canon_tree c hs.1 _ hc, canon_block t hs.2.1 _ ht,
      canon_block e hs.2.2 _ he]
  | .while c bd, hs, b, h => by
    simp only [Lower.lowerStmt1] at h
    cases hc : Lower.lowerExp c <;> cases hb : Lower.lowerStmtsFold bd <;>
      simp only [hc, hb, reduceCtorEq] at h
    cases h
    simp [stmtTree, plainProg, canonProg, canon_tree c hs.1 _ hc, canon_block bd hs.2 _ hb]
theorem canon_block : ∀ (ss : List PStmt), SShapes ss → ∀ b, Lower.lowerStmtsFold ss = some b →
    canonProg (plainProg (blockTree ss)) = canonProg b
  | [], _, b, h => by simp [Lower.lowerStmtsFold] at h; subst h; rfl
  | s :: ss, hs, b, h => block_case s ss (canon_stmt s hs.1) (canon_block ss hs.2) hs b h
end

/-! ### The parser's localisation: every name local, nothing else changed -/

mutual
/-- Every name of the tree is local. -/
def LocalE : Exp → Prop
  | .var l _ => l = true
  | .op _ es | .mul es => LocalL es
  | .cmp _ a b => LocalE a ∧ LocalE b
  | .shift _ e _ | .load e | .loadByte e => LocalE e
  | .const _ | .base => True
def LocalL : List Exp → Prop
  | [] => True
  | e :: es => LocalE e ∧ LocalL es
end

/-- Every name of the statement's tree, and every assigned one, is local. -/
def LocalP : Prog → Prop
  | .dec _ e p => LocalE e ∧ LocalP p
  | .assign l _ e => l = true ∧ LocalE e
  | .store a e | .storeByte a e => LocalE a ∧ LocalE e
  | .seq p q => LocalP p ∧ LocalP q
  | .ite e p q => LocalE e ∧ LocalP p ∧ LocalP q
  | .while e p => LocalE e ∧ LocalP p
  | .ret e => LocalE e
  | .extCall _ a b c d => LocalE a ∧ LocalE b ∧ LocalE c ∧ LocalE d
  | .decCall _ _ es p => LocalL es ∧ LocalP p
  | .skip => True

mutual
/-- Every name of the tree satisfies `P`. -/
def TVars (P : String → Prop) : Exp → Prop
  | .var _ x => P x
  | .op _ es | .mul es => TVarsL P es
  | .cmp _ a b => TVars P a ∧ TVars P b
  | .shift _ e _ | .load e | .loadByte e => TVars P e
  | .const _ | .base => True
def TVarsL (P : String → Prop) : List Exp → Prop
  | [] => True
  | e :: es => TVars P e ∧ TVarsL P es
end

/-- Every name of the expression satisfies `P`. -/
def PVars (P : String → Prop) : PExpr → Prop
  | .var x => P x
  | .binop _ l r | .shr l r | .shl l r => PVars P l ∧ PVars P r
  | .loadw _ a | .loadb a => PVars P a
  | .base | .const _ => True

theorem tvarsL_append {P : String → Prop} : ∀ (xs ys : List Exp), TVarsL P xs → TVarsL P ys →
    TVarsL P (xs ++ ys)
  | [], _, _, h => h
  | _ :: xs, ys, h1, h2 => ⟨h1.1, tvarsL_append xs ys h1.2 h2⟩

theorem tvars_opsOf {P : String → Prop} (o : String) (t : Exp) (h : TVars P t) :
    TVarsL P (opsOf o t) := by
  unfold opsOf; split
  · split
    · rename_i es _ _; simpa [TVars] using h
    · exact ⟨h, trivial⟩
  · exact ⟨h, trivial⟩

theorem tvars_joined {P : String → Prop} (o : String) (x y : Exp) (hx : TVars P x) (hy : TVars P y) :
    TVars P (joined o x y) := by
  unfold joined; split
  · split
    · exact ⟨hx, hy, trivial⟩
    · rename_i es _ _; simp only [TVars] at hx ⊢; exact tvarsL_append _ _ hx ⟨hy, trivial⟩
  · exact ⟨hx, hy, trivial⟩

theorem tvars_mulOps {P : String → Prop} : ∀ t : Exp, TVars P t → TVarsL P (mulOps t)
  | .mul [x, y], h => by
    simp only [TVars, TVarsL] at h
    simp only [mulOps]; exact tvarsL_append _ _ (tvars_mulOps x h.1) ⟨h.2.1, trivial⟩
  | .mul [], h | .mul [_], h | .mul (_ :: _ :: _ :: _), h | .const _, h | .var _ _, h | .base, h
  | .op _ _, h | .cmp _ _ _, h | .shift _ _ _, h | .load _, h | .loadByte _, h => by
    simp only [mulOps]; exact ⟨h, trivial⟩

theorem tvars_foldMul {P : String → Prop} : ∀ (ts : List Exp) (t : Exp), TVars P t → TVarsL P ts →
    TVars P (ts.foldl (fun r e => .mul [r, e]) t)
  | [], _, h, _ => h
  | _ :: es, _, h, hs => tvars_foldMul es _ ⟨h, hs.1, trivial⟩ hs.2

theorem tvars_tree {P : String → Prop} : ∀ e, PVars P e → TVars P (tree e)
  | .base, _ | .const _, _ => trivial
  | .var _, h => h
  | .binop op l r, h => by
    have hl := tvars_tree l h.1
    have hr := tvars_tree r h.2
    cases op
    case and_ => exact tvars_joined _ _ _ hl hr
    case sub => exact ⟨hl, hr, trivial⟩
    case mul =>
      simp only [tree]
      have hm := tvarsL_append _ _ (tvars_mulOps _ hl) (tvars_mulOps _ hr)
      cases hs : mulOps (tree l) ++ mulOps (tree r) with
      | nil => trivial
      | cons t ts => rw [hs] at hm; exact tvars_foldMul ts t hm.1 hm.2
    case lt | eq => exact ⟨hl, hr⟩
    case le => exact ⟨hr, hl⟩
    all_goals exact tvarsL_append _ _ (tvars_opsOf _ _ hl) (tvars_opsOf _ _ hr)
  | .loadw _ a, h | .loadb a, h => tvars_tree a h
  | .shr l _, h | .shl l _, h => tvars_tree l h.1

mutual
theorem local_exp (ls : List String) : ∀ t, TVars (fun x => ls.contains x = true) t →
    LocalE (localExp ls t)
  | .var g x, h => by
    simp only [TVars] at h; simp only [localExp, LocalE, h, Bool.or_true]
  | .op _ es, h => local_exps ls es h
  | .mul es, h => local_exps ls es h
  | .cmp _ a b, h => ⟨local_exp ls a h.1, local_exp ls b h.2⟩
  | .shift _ e _, h | .load e, h | .loadByte e, h => local_exp ls e h
  | .const _, _ | .base, _ => trivial
theorem local_exps (ls : List String) : ∀ es, TVarsL (fun x => ls.contains x = true) es →
    LocalL (localExps ls es)
  | [], _ => trivial
  | e :: es, h => ⟨local_exp ls e h.1, local_exps ls es h.2⟩
end

mutual
theorem plain_local (ls : List String) : ∀ e, plain (localExp ls e) = plain e
  | .var _ _ => rfl
  | .op _ [] => rfl
  | .op o (e :: es) => by
    simp only [localExp, localExps, plain]
    rw [plain_local ls e, plainFold_local ls es]
  | .mul [a, b] => by simp only [localExp, localExps, plain, plain_local ls a, plain_local ls b]
  | .mul [] => rfl
  | .mul [a] => by simp only [localExp, localExps, plain]
  | .mul (a :: b :: c :: es) => by simp only [localExp, localExps, plain]
  | .cmp _ a b => by simp only [localExp, plain, plain_local ls a, plain_local ls b]
  | .shift _ e _ => by simp only [localExp, plain, plain_local ls e]
  | .load e => by simp only [localExp, plain, plain_local ls e]
  | .loadByte e => by simp only [localExp, plain, plain_local ls e]
  | .const _ | .base => rfl
theorem plainFold_local (ls : List String) : ∀ (es : List Exp) {b : Binop} {acc : PancakeExp},
    plainFold b acc (localExps ls es) = plainFold b acc es
  | [] => rfl
  | e :: es => by
    simp only [localExps, plainFold]
    rw [plain_local ls e, plainFold_local ls es]
end

theorem plainProg_local (ls : List String) : ∀ p, plainProg (localProg ls p) = plainProg p
  | .skip => rfl
  | .dec v e p => by simp only [localProg, plainProg, plain_local, plainProg_local]
  | .assign _ v e => by simp only [localProg, plainProg, plain_local]
  | .store a e => by simp only [localProg, plainProg, plain_local]
  | .storeByte a e => by simp only [localProg, plainProg, plain_local]
  | .seq p q => by simp only [localProg, plainProg, plainProg_local]
  | .ite e p q => by simp only [localProg, plainProg, plain_local, plainProg_local]
  | .while e p => by simp only [localProg, plainProg, plain_local, plainProg_local]
  | .ret e => by simp only [localProg, plainProg, plain_local]
  | .extCall n a b c d => by simp only [localProg, plainProg, plain_local]
  | .decCall v f es p => by
    simp only [localProg, plainProg, plainProg_local]
    congr 1
    induction es with
    | nil => rfl
    | cons e es ih => simp only [localExps, List.map_cons, plain_local, ih]

/-! ## What the gate accepts -/

theorem kw_reserved : ∀ w ∈ (Keywords.byRevision.lookup "ed31510b3b0d0523283b68ef7066882526d77df9").getD [],
    w ∈ Checked.reserved := by decide

theorem kw_at : ∀ w ∈ (Keywords.byRevision.lookup "ed31510b3b0d0523283b68ef7066882526d77df9").getD [],
    w.toList.head? ≠ some '@' := by decide

theorem letters_start {c : Char}
    (h : (('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_') = true) :
    startChar c = true ∧ c ≠ '@' := by
  have h' : (isAlpha c || decide (c = '_')) = true := h
  refine ⟨by simp [startChar, h'], ?_⟩
  intro he; subst he; revert h; decide

theorem letters_rest {c : Char}
    (h : ((('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_') || ('0' ≤ c && c ≤ '9')) = true) :
    isWordRest c = true := by
  simp only [isWordRest, isAlpha, isDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, code_le, eq_code, Char.reduceToNat] at h ⊢
  omega

/-- An identifier the gate takes the lexer reads as a name. -/
theorem isName_of_identifier {s : String} (h : Checked.identifier s = true) : IsName s := by
  unfold Checked.identifier at h
  cases hs : s.toList with
  | nil => rw [hs] at h; cases h
  | cons c cs =>
    rw [hs] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨hc, hcs⟩, hr⟩ := h
    obtain ⟨hst, hat⟩ := letters_start hc
    refine ⟨⟨c, cs, hs, hst, hat, ?_⟩, ?_⟩
    · simp only [List.all_eq_true] at hcs ⊢; exact fun x hx => letters_rest (hcs x hx)
    · cases hk : keywords.contains s with
      | false => rfl
      | true =>
        exfalso
        simp only [keywords, List.contains_iff_mem, List.mem_append] at hk
        rcases hk with hk | hk
        · have := kw_reserved s hk
          rw [List.contains_iff_mem.mpr this] at hr; cases hr
        · simp at hk
          rcases hk with rfl | rfl | rfl <;> simp at hs <;> exact hat hs.1.symm

/-- An external the gate takes the lexer reads after `@` as one name. -/
theorem isForeign_of_external {n : String} (h1 : Checked.identifier n = true)
    (h2 : Checked.inNamespace n = true) : IsForeign n := by
  have hn := isName_of_identifier h1
  obtain ⟨c, ws, hs, hc, _, hws⟩ := hn.word
  have hcw : isWordRest c = true := by
    simp only [startChar, Bool.or_eq_true, decide_eq_true_eq] at hc
    simp only [isWordRest, Bool.or_eq_true, decide_eq_true_eq]
    rcases hc with (hc | hc) | hc
    · exact Or.inl (Or.inl hc)
    · exact Or.inr hc
    · exact absurd hc ‹_›
  refine ⟨⟨c, ws, hs, by simp [hcw, hws]⟩, ?_⟩
  cases hk : keywords.contains ("@" ++ n) with
  | false => rfl
  | true =>
    exfalso
    simp only [keywords, List.contains_iff_mem, List.mem_append] at hk
    rcases hk with hk | hk
    · exact kw_at _ hk (by simp)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with h | h | h <;>
        (have := congrArg String.toList h; simp at this
         simp only [Checked.inNamespace, Checked.exportPrefix, this] at h2
         revert h2; decide)

theorem pvars_mono {P Q : String → Prop} {e : PExpr} (h : PVars P e) (hpq : ∀ x, P x → Q x) :
    PVars Q e := by
  induction e with
  | var x => exact hpq x h
  | binop _ l r ihl ihr | shr l r ihl ihr | shl l r ihl ihr => exact ⟨ihl h.1, ihr h.2⟩
  | loadw _ a iha | loadb a iha => exact iha h
  | base | const _ => trivial

/-- Names in scope are ones the lexer reads as names. -/
def ScopeNames (scope : List String) : Prop := ∀ x, scope.contains x = true → IsName x

/-- **An expression the gate accepts**: its names lex as names, its shapes are the gate's, and
every name is in scope. -/
theorem gate_exp {p : Checked.Profile} {scope : List String} (hsc : ScopeNames scope) :
    ∀ e, Checked.expression p scope e = .ok () →
      Names e ∧ Shape e ∧ PVars (fun x => scope.contains x = true) e
  | .const _, _ => ⟨trivial, trivial, trivial⟩
  | .base, _ => ⟨trivial, trivial, trivial⟩
  | .var x, h => by
    simp only [Checked.expression] at h
    split at h
    · rename_i hx; exact ⟨hsc x hx, trivial, hx⟩
    · cases h
  | .binop _ l r, h => by
    obtain ⟨hl, hr⟩ := Checked.seq_ok h
    obtain ⟨a1, a2, a3⟩ := gate_exp hsc l hl
    obtain ⟨b1, b2, b3⟩ := gate_exp hsc r hr
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩, ⟨a3, b3⟩⟩
  | .loadw sh a, h => by
    simp only [Checked.expression] at h
    split at h
    · rename_i hs
      obtain ⟨a1, a2, a3⟩ := gate_exp hsc a h
      exact ⟨a1, ⟨by simpa using hs, a2⟩, a3⟩
    · cases h
  | .loadb a, h => gate_exp hsc a h
  | .shr l r, h | .shl l r, h => by
    simp only [Checked.expression] at h
    split at h
    · split at h
      · obtain ⟨a1, a2, a3⟩ := gate_exp hsc l h
        exact ⟨⟨a1, trivial⟩, ⟨⟨_, rfl⟩, a2⟩, ⟨a3, trivial⟩⟩
      · cases h
    · cases h

theorem lookup_mem {f : String} : ∀ {l : List (String × Nat)} {k : Nat}, l.lookup f = some k → (f, k) ∈ l
  | [], _, h => by simp at h
  | (g, v) :: l, k, h => by
    by_cases hg : f = g
    · subst hg; simp at h; subst h; simp
    · have : (f == g) = false := by simpa using hg
      simp only [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem gate_args {p : Checked.Profile} {scope : List String} (hsc : ScopeNames scope) :
    ∀ args, Checked.expressions p scope args = .ok () →
      ∀ a ∈ args, Names a ∧ Shape a ∧ PVars (fun x => scope.contains x = true) a
  | [], _, a, ha => by cases ha
  | b :: bs, h, a, ha => by
    simp only [Checked.expressions] at h
    obtain ⟨hb, hbs⟩ := Checked.seq_ok h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact gate_exp hsc a hb
    · exact gate_args hsc bs hbs a ha

theorem local_args {scope ls : List String} (hsub : ∀ x, scope.contains x = true → ls.contains x = true) :
    ∀ args : List PExpr, (∀ a ∈ args, PVars (fun x => scope.contains x = true) a) →
      LocalL (localExps ls (args.map tree))
  | [], _ => trivial
  | a :: as, h => ⟨local_exp _ _ (tvars_tree _ (pvars_mono (h a (by simp)) hsub)),
      local_args hsub as fun b hb => h b (by simp [hb])⟩

/-- What a statement, and a block, the gate accepts are: their names lex as names, their shapes
are the gate's, and the parser's localisation makes every name local. -/
theorem gate_stmts (p : Checked.Profile) (hfun : ∀ g ∈ p.functions, Checked.identifier g.1 = true) :
    (∀ (scope : List String) (s : PStmt), Checked.statement p scope s = .ok () → ScopeNames scope →
        StmtNames s ∧ SShape s ∧ ∀ ls : List String, (∀ x, scope.contains x = true → ls.contains x = true) →
          LocalP (localProg ls (stmtTree s))) ∧
    (∀ (scope : List String) (ss : List PStmt), Checked.statements p scope ss = .ok () →
        ScopeNames scope → StmtsNames ss ∧ SShapes ss ∧
          ∀ ls : List String, (∀ x, scope.contains x = true → ls.contains x = true) →
            LocalP (localProg ls (blockTree ss))) := by
  have lexp : ∀ {scope ls : List String} {e : PExpr}, PVars (fun x => scope.contains x = true) e →
      (∀ x, scope.contains x = true → ls.contains x = true) → LocalE (localExp ls (tree e)) :=
    fun hv hsub => local_exp _ _ (tvars_tree _ (pvars_mono hv hsub))
  apply Checked.statement.mutual_induct p
  · intro scope x e hid h; simp [Checked.statement, hid] at h
  · intro scope x e hid hin h
    simp only [Checked.statement, if_neg hid, if_pos hin] at h; simp at h
  · intro scope x e hid hin h hsc
    simp only [Checked.statement, if_neg hid, if_neg hin] at h
    obtain ⟨a1, a2, a3⟩ := gate_exp hsc e h
    refine ⟨⟨isName_of_identifier (by simpa using hid), a1⟩, a2, fun ls hsub => ?_⟩
    exact ⟨lexp a3 hsub, trivial⟩
  · intro scope x e hin h hsc
    simp only [Checked.statement, if_pos hin] at h
    obtain ⟨a1, a2, a3⟩ := gate_exp hsc e h
    refine ⟨⟨hsc x hin, a1⟩, a2, fun ls hsub => ?_⟩
    simp only [stmtTree, localProg, LocalP, hsub x hin, Bool.or_true]
    exact ⟨trivial, lexp a3 hsub⟩
  · intro scope x e hin h; simp only [Checked.statement, if_neg hin] at h; simp at h
  · intro scope a b h hsc
    simp only [Checked.statement] at h
    obtain ⟨ha, hb⟩ := Checked.seq_ok h
    obtain ⟨a1, a2, a3⟩ := gate_exp hsc a ha
    obtain ⟨b1, b2, b3⟩ := gate_exp hsc b hb
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩, fun ls hsub => ⟨lexp a3 hsub, lexp b3 hsub⟩⟩
  · intro scope a b h hsc
    simp only [Checked.statement] at h
    obtain ⟨ha, hb⟩ := Checked.seq_ok h
    obtain ⟨a1, a2, a3⟩ := gate_exp hsc a ha
    obtain ⟨b1, b2, b3⟩ := gate_exp hsc b hb
    exact ⟨⟨a1, b1⟩, ⟨a2, b2⟩, fun ls hsub => ⟨lexp a3 hsub, lexp b3 hsub⟩⟩
  · intro scope e h hsc
    simp only [Checked.statement] at h
    obtain ⟨a1, a2, a3⟩ := gate_exp hsc e h
    exact ⟨a1, a2, fun ls hsub => lexp a3 hsub⟩
  · intro scope e a b iha ihb h hsc
    simp only [Checked.statement] at h
    obtain ⟨he, hrest⟩ := Checked.seq_ok h
    obtain ⟨ha, hb⟩ := Checked.seq_ok hrest
    obtain ⟨c1, c2, c3⟩ := gate_exp hsc e he
    obtain ⟨a1, a2, a3⟩ := iha ha hsc
    obtain ⟨b1, b2, b3⟩ := ihb hb hsc
    exact ⟨⟨c1, a1, b1⟩, ⟨c2, a2, b2⟩, fun ls hsub => ⟨lexp c3 hsub, a3 ls hsub, b3 ls hsub⟩⟩
  · intro scope e b ihb h hsc
    simp only [Checked.statement] at h
    obtain ⟨he, hb⟩ := Checked.seq_ok h
    obtain ⟨c1, c2, c3⟩ := gate_exp hsc e he
    obtain ⟨b1, b2, b3⟩ := ihb hb hsc
    exact ⟨⟨c1, b1⟩, ⟨c2, b2⟩, fun ls hsub => ⟨lexp c3 hsub, b3 ls hsub⟩⟩
  · intro scope name c cl a al hin h hsc
    simp only [Checked.statement, if_pos hin] at h
    simp only [Bool.and_eq_true] at hin
    obtain ⟨⟨_, hid⟩, hns⟩ := hin
    obtain ⟨hc, h1⟩ := Checked.seq_ok h
    obtain ⟨hcl, h2⟩ := Checked.seq_ok h1
    obtain ⟨ha, hal⟩ := Checked.seq_ok h2
    obtain ⟨c1, c2, c3⟩ := gate_exp hsc c hc
    obtain ⟨d1, d2, d3⟩ := gate_exp hsc cl hcl
    obtain ⟨e1, e2, e3⟩ := gate_exp hsc a ha
    obtain ⟨f1, f2, f3⟩ := gate_exp hsc al hal
    refine ⟨⟨isForeign_of_external hid hns, ?_⟩, ⟨rfl, ?_⟩, fun ls hsub => ?_⟩
    · intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · intro x hx; simp at hx; rcases hx with rfl | rfl | rfl | rfl <;> assumption
    · exact ⟨lexp c3 hsub, lexp d3 hsub, lexp e3 hsub, lexp f3 hsub⟩
  · intro scope name c cl a al hin h
    simp only [Checked.statement, if_neg hin] at h; simp at h
  · intro scope name args hshape _ h
    exact absurd h (Checked.ffi_other_rejected hshape)
  · intro scope name args hshape _ h
    exact absurd h (Checked.ffi_other_rejected hshape)
  · intro scope r fn args h hsc
    simp only [Checked.statement] at h
    unfold Checked.callCheck at h
    cases hk : p.functions.lookup fn with
    | none => rw [hk] at h; cases h
    | some k =>
      rw [hk] at h
      simp only at h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      rename_i hr
      split at h
      · cases h
      have hargs := gate_args hsc args h
      have hf := hfun (fn, k) (lookup_mem hk)
      have hrid : Checked.identifier r = true := by simpa using hr
      refine ⟨⟨isName_of_identifier hrid, isName_of_identifier hf, fun a ha => (hargs a ha).1⟩,
        ⟨fun (he : fn = "__add_with_carry__") => by
          rw [he] at hf; exact absurd (show Checked.identifier "__add_with_carry__" = true from hf)
            (by decide), fun a ha => (hargs a ha).2.1⟩,
        fun ls hsub => ⟨local_args hsub args fun a ha => (hargs a ha).2.2, trivial⟩⟩
  · intro scope _ _; exact ⟨trivial, trivial, fun _ _ => trivial⟩
  · intro scope s rest ihs ihrest h hsc
    simp only [Checked.statements] at h
    obtain ⟨hs, hrest⟩ := Checked.seq_ok h
    split at hrest
    · cases hrest
    obtain ⟨s1, s2, s3⟩ := ihs hs hsc
    have grow : ∀ (x : String) (ls : List String), (∀ y, scope.contains y = true → ls.contains y = true) →
        ∀ y, (x :: scope).contains y = true → (x :: ls).contains y = true := by
      intro x ls hsub y hy
      simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at hy ⊢
      rcases hy with h | h
      · exact Or.inl h
      · exact Or.inr (hsub y h)
    have growN : ∀ x, IsName x → ScopeNames (x :: scope) := by
      intro x hx y hy
      simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at hy
      rcases hy with rfl | hy
      · exact hx
      · exact hsc y hy
    match s, s1, s2, s3, ihrest, hrest with
    | .dec n v, s1, s2, s3, ihrest, hrest =>
      obtain ⟨r1, r2, r3⟩ := ihrest hrest (growN n s1.1)
      refine ⟨⟨s1, r1⟩, ⟨s2, r2⟩, fun ls hsub => ?_⟩
      cases rest with
      | nil => simpa [blockTree] using s3 ls hsub
      | cons t ts =>
        simp only [blockTree, localProg, LocalP]
        exact ⟨(s3 ls hsub).1, r3 (n :: ls) (grow n ls hsub)⟩
    | .call r f as, s1, s2, s3, ihrest, hrest =>
      obtain ⟨r1, r2, r3⟩ := ihrest hrest (growN r s1.1)
      refine ⟨⟨s1, r1⟩, ⟨s2, r2⟩, fun ls hsub => ?_⟩
      cases rest with
      | nil => simpa [blockTree] using s3 ls hsub
      | cons t ts =>
        simp only [blockTree, localProg, LocalP]
        exact ⟨(s3 ls hsub).1, r3 (r :: ls) (grow r ls hsub)⟩
    | .assign _ _, s1, s2, s3, ihrest, hrest | .store _ _, s1, s2, s3, ihrest, hrest
    | .storeb _ _, s1, s2, s3, ihrest, hrest | .ffi _ _, s1, s2, s3, ihrest, hrest
    | .ret _, s1, s2, s3, ihrest, hrest | .ite _ _ _, s1, s2, s3, ihrest, hrest
    | .while _ _, s1, s2, s3, ihrest, hrest =>
      obtain ⟨r1, r2, r3⟩ := ihrest hrest hsc
      refine ⟨⟨s1, r1⟩, ⟨s2, r2⟩, fun ls hsub => ?_⟩
      cases rest with
      | nil => simpa [blockTree] using s3 ls hsub
      | cons t ts =>
        simp only [blockTree, localProg, LocalP]
        exact ⟨s3 ls hsub, r3 ls hsub⟩

/-! ### Functions the gate accepts -/

/-- A function the gate's rules take: its name an identifier, its body checked in the scope its
parameters open, by a profile whose functions are named by identifiers. -/
structure Taken (f : PFun) : Prop where
  name : Checked.identifier f.name = true
  body : ∃ (p : Checked.Profile) (scope : List String),
    (∀ g ∈ p.functions, Checked.identifier g.1 = true) ∧
      Checked.paramScope f.params [] = .ok scope ∧ Checked.statements p scope f.body = .ok ()

/-- **What a printed function's tree is**: its name, export and parameters, every name of its
body local, and its body, read in the model, in the canonical form of its lowering. -/
structure ReadsAs (F : Func) (f : PFun) : Prop where
  name : F.name = f.name
  exported : F.exported = f.exported
  params : F.params = f.params.map (·.2)
  locals : LocalP F.body
  body : ∃ b, Lower.lowerStmtsFold f.body = some b ∧ canonProg (plainProg F.body) = canonProg b

theorem paramScope_ok : ∀ (ps : List (Nat × String)) (acc scope : List String),
    Checked.paramScope ps acc = .ok scope →
      (∀ q ∈ ps, q.1 = 1 ∧ Checked.identifier q.2 = true) ∧
        ∀ x, scope.contains x = true → acc.contains x = true ∨ (ps.map (·.2)).contains x = true
  | [], acc, scope, h => by
    simp only [Checked.paramScope, Except.ok.injEq] at h; subst h
    exact ⟨fun q hq => (by cases hq), fun x hx => Or.inl hx⟩
  | (sh, n) :: rest, acc, scope, h => by
    simp only [Checked.paramScope] at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    rename_i hsh hid _
    obtain ⟨h1, h2⟩ := paramScope_ok rest (n :: acc) scope h
    refine ⟨fun q hq => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨by simpa using hsh, by simpa using hid⟩
      · exact h1 q hq
    · rcases h2 x hx with h | h
      · simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with rfl | h
        · right; simp
        · left; exact h
      · right; simp only [List.map_cons, List.contains_cons, Bool.or_eq_true]; exact Or.inr h

/-- **A function the gate takes reads as its tree.** -/
theorem taken_reads {f : PFun} (h : Taken f) : FunNames f ∧ FunShape f ∧ ReadsAs (funTree f) f := by
  obtain ⟨p, scope, hfun, hps, hb⟩ := h.body
  obtain ⟨hp1, hp2⟩ := paramScope_ok f.params [] scope hps
  have hsub : ∀ x, scope.contains x = true → (f.params.map (·.2)).contains x = true := fun x hx =>
    (hp2 x hx).resolve_left (by simp)
  have hsc : ScopeNames scope := by
    intro x hx
    have := hsub x hx
    simp only [List.contains_iff_mem, List.mem_map] at this
    obtain ⟨q, hq, rfl⟩ := this
    exact isName_of_identifier (hp1 q hq).2
  obtain ⟨n1, n2, n3⟩ := (gate_stmts p hfun).2 scope f.body hb hsc
  have hl := Checked.statements_lower hb
  cases hlb : Lower.lowerStmtsFold f.body with
  | none => rw [hlb] at hl; cases hl
  | some b =>
    refine ⟨⟨isName_of_identifier h.name, fun q hq => isName_of_identifier (hp1 q hq).2, n1⟩,
      ⟨fun q hq => (hp1 q hq).1, n2⟩, ⟨rfl, rfl, rfl, n3 _ hsub, b, hlb, ?_⟩⟩
    simp only [funTree]
    rw [plainProg_local, canon_block f.body n2 b hlb]

/-- Functions the gate takes, printed in turn, read as their trees. -/
theorem taken_program (fs : List PFun) (h : ∀ f ∈ fs, Taken f) :
    program (String.intercalate "\n" (fs.map ppFun)) = some (fs.map funTree) ∧
      ∀ f ∈ fs, ReadsAs (funTree f) f :=
  ⟨program_reads fs (fun f hf => (taken_reads (h f hf)).1) (fun f hf => (taken_reads (h f hf)).2.1),
    fun f hf => (taken_reads (h f hf)).2.2⟩

theorem checkEach_taken {p : Checked.Profile} (hfun : ∀ g ∈ p.functions, Checked.identifier g.1 = true) :
    ∀ (funs : List PFun) (before : List String), Checked.checkEach p before funs = .ok () →
      ∀ g ∈ funs, ∃ (p' : Checked.Profile) (scope : List String),
        (∀ g ∈ p'.functions, Checked.identifier g.1 = true) ∧
          Checked.paramScope g.params [] = .ok scope ∧ Checked.statements p' scope g.body = .ok ()
  | [], _, _, g, hg => by cases hg
  | f :: fs, before, h, g, hg => by
    simp only [Checked.checkEach, bind, Except.bind] at h
    cases hp : Checked.paramScope f.params [] with
    | error e => simp [hp] at h
    | ok sc =>
      cases hs : Checked.statements { p with callable := some before } sc f.body with
      | error e => simp [hp, hs] at h
      | ok u =>
        cases he : Checked.exitsL f.body
        · simp [hp, hs, he] at h
        · simp only [hp, hs, he, if_true, pure, Except.pure] at h
          rcases List.mem_cons.mp hg with rfl | hg
          · exact ⟨{ p with callable := some before }, sc, hfun, hp, by cases u; exact hs⟩
          · exact checkEach_taken hfun fs _ h g hg

theorem checkFunctions_taken {p : Checked.Profile} {entry : String} {funs : List PFun}
    (hfun : ∀ g ∈ p.functions, Checked.identifier g.1 = true)
    (h : Checked.checkFunctions p entry funs = .ok ()) : ∀ g ∈ funs, Taken g := by
  unfold Checked.checkFunctions at h
  simp only [bind, Except.bind] at h
  split at h
  · rename_i hn
    intro g hg
    simp only [Bool.and_eq_true, List.all_eq_true] at hn
    exact ⟨(hn.1 g hg).1.1,
      checkEach_taken hfun funs [] h g hg⟩
  · cases h

/-! ## Every program the gate prints -/

theorem checkFunctions_names {p : Checked.Profile} {entry : String} {funs : List PFun}
    (h : Checked.checkFunctions p entry funs = .ok ()) : ∀ g ∈ funs, Checked.identifier g.name = true := by
  unfold Checked.checkFunctions at h
  simp only [bind, Except.bind] at h
  split at h
  · rename_i hn
    simp only [Bool.and_eq_true, List.all_eq_true] at hn
    exact fun g hg => (hn.1 g hg).1.1
  · cases h

theorem names_functions {funs : List PFun} (h : ∀ g ∈ funs, Checked.identifier g.name = true) :
    ∀ g ∈ funs.map (fun f => (f.name, f.params.length)), Checked.identifier g.1 = true := by
  intro g hg
  simp only [List.mem_map] at hg
  obtain ⟨f, hf, rfl⟩ := hg
  exact h f hf

theorem emitProgram_taken {externals : List String} {funs : List PFun} {main : PFun} {src : String}
    (h : Checked.emitProgram externals funs main = .ok src) :
    src = String.intercalate "\n" ((funs ++ [main]).map ppFun) ∧ ∀ g ∈ funs ++ [main], Taken g := by
  refine ⟨Checked.emitProgram_prints h, ?_⟩
  obtain ⟨_, hname, hparams⟩ := Checked.emitProgram_entry h
  simp only [Checked.emitProgram, bind, Except.bind] at h
  split at h
  · simp only [pure, Except.pure] at h
    split at h
    · cases h
    · rename_i u hc
      cases u
      have hfun := names_functions (checkFunctions_names hc)
      split at h
      · cases h
      · rename_i u hm
        cases u
        intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · exact checkFunctions_taken hfun hc g hg
        · simp at hg; subst hg
          exact ⟨by rw [hname]; decide, _, [], hfun, by rw [hparams]; rfl, hm⟩
  · cases h

theorem emitWith_taken {funs : List PFun} {f : PFun} {src : String}
    (h : Checked.emitWith funs f = .ok src) :
    src = String.intercalate "\n" ((funs ++ [f]).map ppFun) ∧ ∀ g ∈ funs ++ [f], Taken g := by
  simp only [Checked.emitWith, bind, Except.bind] at h
  split at h
  · try simp only [pure, Except.pure] at h
    split at h
    · rename_i hid
      try simp only [pure, Except.pure] at h
      split at h
      · try simp only [pure, Except.pure] at h
        split at h
        · try simp only [pure, Except.pure] at h
          split at h
          · cases h
          · rename_i u hc
            cases u
            have hfun := names_functions (checkFunctions_names hc)
            split at h
            · cases h
            · rename_i scope hps
              split at h
              · cases h
              · rename_i u hb
                cases u
                split at h
                · simp only [Except.ok.injEq] at h
                  refine ⟨h.symm, fun g hg => ?_⟩
                  rcases List.mem_append.mp hg with hg | hg
                  · exact checkFunctions_taken hfun hc g hg
                  · simp at hg; subst hg
                    exact ⟨by simpa using hid, _, scope, hfun, hps, hb⟩
                · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem emit_taken {f : PFun} {src : String} (h : Checked.emit f = .ok src) :
    src = ppFun f ∧ Taken f := by
  simp only [Checked.emit, bind, Except.bind] at h
  split at h
  · try simp only [pure, Except.pure] at h
    split at h
    · rename_i hid
      try simp only [pure, Except.pure] at h
      split at h
      · try simp only [pure, Except.pure] at h
        split at h
        · try simp only [pure, Except.pure] at h
          split at h
          · cases h
          · rename_i scope hps
            split at h
            · cases h
            · rename_i u hb
              cases u
              split at h
              · simp only [Except.ok.injEq] at h
                exact ⟨h.symm, by simpa using hid, _, scope, fun g hg => (by cases hg), hps, hb⟩
              · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem emitMain_taken {externals : List String} {f : PFun} {src : String}
    (h : Checked.emitMain externals f = .ok src) : src = ppFun f ∧ Taken f := by
  refine ⟨Checked.emitMain_prints h, ?_⟩
  obtain ⟨_, hname, hparams⟩ := Checked.emitMain_entry h
  simp only [Checked.emitMain, bind, Except.bind] at h
  split at h
  · try simp only [pure, Except.pure] at h
    split at h
    · cases h
    · rename_i u hb
      cases u
      exact ⟨by rw [hname]; decide, _, [], fun g hg => (by cases hg), by rw [hparams]; rfl, hb⟩
  · cases h

/-- **CakeML's parser, as `Parse` writes it, reads every whole program the gate prints as the
program it lowers to**: a function a function, each with its name, export and parameters, every
name of its body local, and its body, read in the model, in the canonical form of its lowering,
which `Canon.canon_eval` shows identifies only expressions that evaluate alike. -/
theorem emitProgram_reads {externals : List String} {funs : List PFun} {main : PFun} {src : String}
    (h : Checked.emitProgram externals funs main = .ok src) :
    program src = some ((funs ++ [main]).map funTree) ∧
      ∀ f ∈ funs ++ [main], ReadsAs (funTree f) f := by
  obtain ⟨rfl, ht⟩ := emitProgram_taken h
  exact taken_program _ ht

/-- …and every exported function with the functions it calls… -/
theorem emitWith_reads {funs : List PFun} {f : PFun} {src : String}
    (h : Checked.emitWith funs f = .ok src) :
    program src = some ((funs ++ [f]).map funTree) ∧ ∀ g ∈ funs ++ [f], ReadsAs (funTree g) g := by
  obtain ⟨rfl, ht⟩ := emitWith_taken h
  exact taken_program _ ht

/-- …every exported function alone… -/
theorem emit_reads {f : PFun} {src : String} (h : Checked.emit f = .ok src) :
    program src = some [funTree f] ∧ ReadsAs (funTree f) f := by
  obtain ⟨rfl, ht⟩ := emit_taken h
  have := taken_program [f] (fun g hg => by simp at hg; subst hg; exact ht)
  simp only [List.map_cons, List.map_nil, String.intercalate_singleton] at this
  exact ⟨this.1, this.2 f (by simp)⟩

/-- …and every whole program without functions. -/
theorem emitMain_reads {externals : List String} {f : PFun} {src : String}
    (h : Checked.emitMain externals f = .ok src) :
    program src = some [funTree f] ∧ ReadsAs (funTree f) f := by
  obtain ⟨rfl, ht⟩ := emitMain_taken h
  have := taken_program [f] (fun g hg => by simp at hg; subst hg; exact ht)
  simp only [List.map_cons, List.map_nil, String.intercalate_singleton] at this
  exact ⟨this.1, this.2 f (by simp)⟩

/-! ## The premises are met

A function the gate accepts, `dn_probe(1 a) { return a + 1; }`, and each premise above shown of it,
of its parts or of the text around them. -/

def probeBody : PExpr := .binop .add (.var "a") (.const 1)

def probe : PFun := { name := "dn_probe", exported := true, params := [(1, "a")], body := [.ret probeBody] }

theorem probe_taken : Taken probe :=
  ⟨by decide, Checked.exportedProfile, ["a"], fun g hg => (by cases hg), by rfl, by rfl⟩

theorem probe_reads : FunNames probe ∧ FunShape probe ∧ ReadsAs (funTree probe) probe :=
  taken_reads probe_taken

theorem probe_parts : IsName "a" ∧ ScopeNames ["a"] ∧ Names probeBody ∧ Shape probeBody ∧
    SShape (.ret probeBody) ∧ SShapes probe.body ∧ PVars (fun x => ["a"].contains x = true) probeBody ∧
    IsForeign "dn_probe_io" := by
  have ha := isName_of_identifier (s := "a") (by decide)
  refine ⟨ha, fun x hx => ?_, ⟨ha, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩,
    ⟨⟨trivial, trivial⟩, trivial⟩, ⟨rfl, trivial⟩, isForeign_of_external (by decide) (by decide)⟩
  simp at hx; subst hx; exact ha

theorem probe_lexes : Delim [';'] ∧ LexesTo (ppExpr probeBody).toList (toks probeBody) :=
  ⟨show delim ';' = true by decide, lex_exp probeBody ⟨(probe_parts).1, trivial⟩⟩

theorem probe_follows : Term (.sym ";") ∧ Follows .eq [.sym ";"] ∧ Assoc .add ∧
    Chainy .add (canon (plain (tree probeBody))) ∧ MChainy (canon (plain (tree probeBody))) :=
  ⟨Or.inl rfl, Follows.stop rfl (by decide) (by decide), Or.inl rfl, chainy_canon (Or.inl rfl) _,
    mchainy_canon _⟩

theorem probe_body_reads : Reads probeBody ∧ ReadsU probeBody :=
  ⟨reads probeBody ⟨trivial, trivial⟩, unit_reads (reads probeBody ⟨trivial, trivial⟩)⟩

theorem probe_stmt : StmtNames (.ret probeBody) ∧ StmtsNames probe.body ∧
    TVars (fun x => x = "a") (tree probeBody) ∧ TVarsL (fun x => x = "a") [tree probeBody] :=
  ⟨⟨probe_parts.1, trivial⟩, ⟨⟨probe_parts.1, trivial⟩, trivial⟩, tvars_tree _ ⟨rfl, trivial⟩,
    ⟨tvars_tree _ ⟨rfl, trivial⟩, trivial⟩⟩

/-- The gate prints the function, and its text reads as lowered. -/
theorem probe_emit_reads : Checked.emit probe = .ok (ppFun probe) ∧
    program (ppFun probe) = some [funTree probe] ∧ ReadsAs (funTree probe) probe :=
  have h : Checked.emit probe = .ok (ppFun probe) := by rfl
  ⟨h, emit_reads h⟩

end DN.Compiler.ParseCorrect
