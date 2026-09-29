-- SPDX-License-Identifier: AGPL-3.0-or-later

/-!
# DN.News.FrameSpec

How the server cuts its input into command lines and multi-line blocks, written from the rules
of docs/decisions/0003-nntp-slice.md ("How input is framed") over the whole stream, with nothing of
the code that does it.

A stream of command lines is its lines, each ended by an LF, followed by what has not reached an
LF yet (`Lines`). What a line is follows from its bytes before the LF alone (`classify`): a
command when a CR stands right before the LF and nowhere else, it holds no NUL, and it is no
longer than `lim` octets with its line end; too long when it is longer, of which the first `lim`
bytes are kept; malformed otherwise.

A block, which starts at the beginning of a line, is its lines, each ended by CRLF, up to the
first line that is a single dot (`Block`). It is refused when a line holds a CR, an LF or a NUL,
too large when what it holds after undoing the dot-stuffing does not fit in `cap` bytes, and
accepted otherwise (`blockResult`). Every stream is a block followed by the rest, or a block that
has not ended yet (`block_or_open`).
-/

namespace DN.News.FrameSpec

abbrev Byte := BitVec 8

def LF : Byte := 10#8
def CR : Byte := 13#8
def NUL : Byte := 0#8
def DOT : Byte := 46#8

/-! ## Command lines -/

inductive Kind | command | malformed | overlong
  deriving DecidableEq, Repr

/-- A line as the server sees it: what it is, and the bytes it keeps of it. -/
structure Line where
  kind : Kind
  kept : List Byte
  deriving DecidableEq, Repr

/-- What the line whose bytes before its LF are `body` is, for lines of at most `lim` octets. -/
def classify (lim : Nat) (body : List Byte) : Line :=
  if lim < body.length + 1 then ⟨.overlong, body.take lim⟩
  else if body.getLast? = some CR ∧ CR ∉ body.dropLast ∧ NUL ∉ body then ⟨.command, body.dropLast⟩
  else ⟨.malformed, body⟩

/-- The stream `s` is the lines `bodies`, each followed by an LF, then `tail`, which holds no LF. -/
def Lines (s : List Byte) (bodies : List (List Byte)) (tail : List Byte) : Prop :=
  s = (bodies.map (· ++ [LF])).flatten ++ tail ∧ (∀ b ∈ bodies, LF ∉ b) ∧ LF ∉ tail

/-- Every stream is lines and a tail. -/
theorem lines_exist (s : List Byte) : ∃ bodies tail, Lines s bodies tail := by
  induction s with
  | nil => exact ⟨[], [], by simp [Lines]⟩
  | cons x rest ih =>
    obtain ⟨bodies, tail, hs, hb, ht⟩ := ih
    by_cases hx : x = LF
    · refine ⟨[] :: bodies, tail, ?_, ?_, ht⟩
      · simp [hs, hx]
      · intro b hb'
        simp only [List.mem_cons] at hb'
        rcases hb' with rfl | hb'
        · simp
        · exact hb b hb'
    · cases bodies with
      | nil =>
        refine ⟨[], x :: tail, ?_, by simp, ?_⟩
        · simp [hs]
        · simp only [List.mem_cons, not_or]; exact ⟨Ne.symm hx, ht⟩
      | cons b0 bs =>
        refine ⟨(x :: b0) :: bs, tail, ?_, ?_, ht⟩
        · simp [hs]
        · intro b hb'
          simp only [List.mem_cons] at hb'
          rcases hb' with rfl | hb'
          · simp only [List.mem_cons, not_or]
            exact ⟨Ne.symm hx, hb b0 (by simp)⟩
          · exact hb b (by simp [hb'])

/-! ## Multi-line blocks -/

def CRLF : List Byte := [CR, LF]

/-- A line of a block has no CRLF inside it: the first CRLF after its start is its end. -/
def Unbroken (l : List Byte) : Prop := ¬ CRLF <:+: l

instance (l : List Byte) : Decidable (Unbroken l) := inferInstanceAs (Decidable (¬ _))

/-- The stream `s` is a block of the lines `ls`, each followed by CRLF, and the line holding
a single dot with its CRLF, then `rest`, which follows the block. No line of `ls` holds a CRLF or
is a single dot, so the block ends at its first such line. -/
def Block (s : List Byte) (ls : List (List Byte)) (rest : List Byte) : Prop :=
  s = ((ls ++ [[DOT]]).map (· ++ CRLF)).flatten ++ rest ∧
    ∀ l ∈ ls, Unbroken l ∧ l ≠ [DOT]

/-- The stream `s` is a block that has not ended yet: its lines `ls`, each followed by CRLF, then
the line `r` it is still reading. No line holds a CRLF, and none of `ls` is a single dot. -/
def Open (s : List Byte) (ls : List (List Byte)) (r : List Byte) : Prop :=
  s = (ls.map (· ++ CRLF)).flatten ++ r ∧ (∀ l ∈ ls, Unbroken l ∧ l ≠ [DOT]) ∧ Unbroken r

theorem unbroken_cons {x : Byte} {l : List Byte} (h : Unbroken l)
    (hx : ¬ (x = CR ∧ l.head? = some LF)) : Unbroken (x :: l) := by
  intro hi
  rcases List.infix_cons_iff.mp hi with hp | hi
  · cases l with
    | nil => exact absurd hp.length_le (by simp [CRLF])
    | cons y l =>
      simp only [CRLF, List.cons_prefix_cons] at hp
      exact hx ⟨hp.1.symm, by simp [hp.2.1]⟩
  · exact h hi

theorem unbroken_of_cons {x : Byte} {l : List Byte} (h : Unbroken (x :: l)) : Unbroken l :=
  fun hi => h (List.infix_cons hi)

/-- Every stream is lines, each followed by CRLF, then what has not reached a CRLF yet. -/
theorem crlf_lines (s : List Byte) : ∃ (ls : List (List Byte)) (r : List Byte),
    s = (ls.map (· ++ CRLF)).flatten ++ r ∧ (∀ l ∈ ls, Unbroken l) ∧ Unbroken r := by
  induction s with
  | nil => exact ⟨[], [], by simp, by simp, by decide⟩
  | cons x rest ih =>
    obtain ⟨ls, r, hs, hls, hr⟩ := ih
    cases ls with
    | nil =>
      by_cases hc : x = CR ∧ r.head? = some LF
      · obtain ⟨rfl, hh⟩ := hc
        cases r with
        | nil => simp at hh
        | cons y r' =>
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          refine ⟨[[]], r', by simp [hs, CRLF], by simp; decide, unbroken_of_cons hr⟩
      · exact ⟨[], x :: r, by simp [hs], by simp, unbroken_cons hr hc⟩
    | cons l0 ls' =>
      have h0 : Unbroken l0 := hls l0 (by simp)
      have hrest : ∀ l ∈ ls', Unbroken l := fun l hl => hls l (by simp [hl])
      by_cases hc : x = CR ∧ l0.head? = some LF
      · obtain ⟨rfl, hh⟩ := hc
        cases l0 with
        | nil => simp at hh
        | cons y l0' =>
          simp only [List.head?_cons, Option.some.injEq] at hh
          subst hh
          refine ⟨[] :: l0' :: ls', r, by simp [hs, CRLF], ?_, hr⟩
          intro l hl
          simp only [List.mem_cons] at hl
          rcases hl with rfl | rfl | hl
          · decide
          · exact unbroken_of_cons h0
          · exact hrest l hl
      · refine ⟨(x :: l0) :: ls', r, by simp [hs], ?_, hr⟩
        intro l hl
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · exact unbroken_cons h0 hc
        · exact hrest l hl

/-- **Every stream is a block or a block not ended yet.** -/
theorem block_or_open (s : List Byte) :
    (∃ ls rest, Block s ls rest) ∨ ∃ ls r, Open s ls r := by
  obtain ⟨ls, r, hs, hls, hr⟩ := crlf_lines s
  subst hs
  induction ls with
  | nil => exact .inr ⟨[], r, by simp, by simp, hr⟩
  | cons l ls ih =>
    have hl : Unbroken l := hls l (by simp)
    by_cases hd : l = [DOT]
    · subst hd
      exact .inl ⟨[], (ls.map (· ++ CRLF)).flatten ++ r, by simp, by simp⟩
    · rcases ih (fun l' h' => hls l' (by simp [h'])) with ⟨a, rest, he, ha⟩ | ⟨a, r', he, ha, hr'⟩
      · refine .inl ⟨l :: a, rest, by simp [he], ?_⟩
        intro l' h'
        simp only [List.mem_cons] at h'
        rcases h' with rfl | h'
        · exact ⟨hl, hd⟩
        · exact ha l' h'
      · refine .inr ⟨l :: a, r', by simp [he], ?_, hr'⟩
        intro l' h'
        simp only [List.mem_cons] at h'
        rcases h' with rfl | h'
        · exact ⟨hl, hd⟩
        · exact ha l' h'

/-- A line of a block holds no CR, no LF and no NUL. -/
def Clean (l : List Byte) : Prop := CR ∉ l ∧ LF ∉ l ∧ NUL ∉ l

instance (l : List Byte) : Decidable (Clean l) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- A line that starts with a dot had one put before it by the sender. -/
def unstuff : List Byte → List Byte
  | x :: l => if x = DOT then l else x :: l
  | [] => []

/-- What the block holds: each line with its dot-stuffing undone, ended by CRLF. -/
def content (ls : List (List Byte)) : List Byte :=
  (ls.map (fun l => unstuff l ++ CRLF)).flatten

inductive BlockKind | accepted | refused | tooLarge
  deriving DecidableEq, Repr

structure BlockResult where
  kind : BlockKind
  /-- What the block holds, when it is accepted. -/
  held : List Byte
  deriving DecidableEq, Repr

/-- A block of the lines `ls`, for a buffer of `cap` bytes. -/
def blockResult (cap : Nat) (ls : List (List Byte)) : BlockResult :=
  if ∀ l ∈ ls, Clean l then
    if (content ls).length ≤ cap then ⟨.accepted, content ls⟩ else ⟨.tooLarge, []⟩
  else ⟨.refused, []⟩

/-! ## The premises hold of real streams -/

/-- A command, a line broken by a bare LF, and an unfinished line. -/
theorem lines_witness :
    Lines [67#8, 13#8, 10#8, 65#8, 10#8, 66#8] [[67#8, 13#8], [65#8]] [66#8] :=
  ⟨rfl, by decide, by decide⟩

/-- A block of one stuffed line, then what follows it. -/
theorem block_witness :
    Block [46#8, 46#8, 13#8, 10#8, 46#8, 13#8, 10#8, 81#8] [[46#8, 46#8]] [81#8] :=
  ⟨rfl, by decide⟩

/-- A block with one line read and the next begun. -/
theorem open_witness : Open [65#8, 13#8, 10#8, 46#8, 13#8] [[65#8]] [46#8, 13#8] :=
  ⟨rfl, by decide, by decide⟩

end DN.News.FrameSpec
