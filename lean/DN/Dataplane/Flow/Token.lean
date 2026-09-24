-- SPDX-License-Identifier: AGPL-3.0-or-later

/-!
# DN.Dataplane.Flow.Token

Source provenance is in docs/provenance.json; assurance boundaries are in
docs/assurance.md.
-/

namespace DN.Dataplane.Flow

/-- `2^64` — the size of the completion-token word. -/
def tokenSpace : Nat := 2 ^ 64

/-- The completion-token namespaces, as a datatype. One constructor per
namespace; the payloads are the fields recovered on dispatch. -/
inductive Token where
  /-- Wakeup sentinel: the multishot poll on the reactor's wakeup fd.
  Encodes to `0`. -/
  | wakeup
  /-- Cancel sentinel for async-cancel submissions. Encodes to `2^64 - 1`. -/
  | cancel
  /-- A pending-operation slab key: slot `index` in the low 32 bits, the
  slot-reuse `generation` in the high 32 bits. Slot 0 is reserved (key `0`
  would collide with the wakeup sentinel), and the generation must stay
  below `2^31` to keep slab keys out of the tagged half of the space. -/
  | slab (index generation : Nat)
  /-- Multishot-accept tag: top 16 bits `0xACCE`, listener fd in the low
  32 bits. -/
  | acceptMulti (listenerFd : Nat)
  /-- Multishot-recv tag: top 16 bits `0xBECF`, socket fd in the low
  32 bits. -/
  | recvMulti (socketFd : Nat)
  /-- Multishot-recvmsg (UDP) tag: top 16 bits `0xDC4F`, socket fd in the
  low 32 bits. -/
  | recvMsgMulti (socketFd : Nat)
  /-- A cross-queue message: top byte `0xFF`, opcode in bits 55–48, source
  reactor id in bits 47–32, payload in the low 32 bits. -/
  | msgRing (opcode source payload : Nat)
  /-- Source-side confirmation of a cross-queue message: exactly
  `0xFE <<< 56`. -/
  | msgRingSent
  /-- Per-channel wakeup: top byte `0xCA`, channel id in the low 8 bits. -/
  | channel (id : Nat)
  /-- Periodic-timer token: bit 63 set, job id in the low bits. The job id
  is bounded by `2^48` so the token cannot wander into the tag windows. -/
  | timer (job : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace Token

/-- Field bounds per namespace. Every bound is decidable; `decide` closes
concrete instances. -/
def Wf : Token → Prop
  | .wakeup => True
  | .cancel => True
  | .slab index generation => 0 < index ∧ index < 2 ^ 32 ∧ generation < 2 ^ 31
  | .acceptMulti fd => fd < 2 ^ 32
  | .recvMulti fd => fd < 2 ^ 32
  | .recvMsgMulti fd => fd < 2 ^ 32
  | .msgRing opcode source payload =>
      opcode < 2 ^ 8 ∧ source < 2 ^ 16 ∧ payload < 2 ^ 32 ∧
      ¬(opcode = 0xFF ∧ source = 0xFFFF ∧ payload = 2 ^ 32 - 1)
  | .msgRingSent => True
  | .channel id => id < 2 ^ 8
  | .timer job => job < 2 ^ 48

instance (t : Token) : Decidable t.Wf := by
  cases t <;> (simp only [Wf]; infer_instance)

/-- Encode a token into the 64-bit word. -/
def encode : Token → Nat
  | .wakeup => 0
  | .cancel => 2 ^ 64 - 1
  | .slab index generation => generation * 2 ^ 32 + index
  | .acceptMulti fd => 0xACCE * 2 ^ 48 + fd
  | .recvMulti fd => 0xBECF * 2 ^ 48 + fd
  | .recvMsgMulti fd => 0xDC4F * 2 ^ 48 + fd
  | .msgRing opcode source payload =>
      0xFF * 2 ^ 56 + opcode * 2 ^ 48 + source * 2 ^ 32 + payload
  | .msgRingSent => 0xFE * 2 ^ 56
  | .channel id => 0xCA * 2 ^ 56 + id
  | .timer job => 2 ^ 63 + job

/-- Decode a 64-bit word, in dispatch priority order: sentinels, top-byte
markers, top-16-bit tags, the bit-63 timer namespace, and slab keys as the
residue. Total — junk words decode to *something*; the round-trip theorem
holds on well-formed tokens. -/
def decode (v : Nat) : Option Token :=
  if v = 0 then some .wakeup
  else if v = 2 ^ 64 - 1 then some .cancel
  else if v / 2 ^ 56 = 0xCA then some (.channel (v % 2 ^ 8))
  else if v / 2 ^ 56 = 0xFE then some .msgRingSent
  else if v / 2 ^ 56 = 0xFF then
    some (.msgRing (v / 2 ^ 48 % 2 ^ 8) (v / 2 ^ 32 % 2 ^ 16) (v % 2 ^ 32))
  else if v / 2 ^ 48 = 0xACCE then some (.acceptMulti (v % 2 ^ 32))
  else if v / 2 ^ 48 = 0xBECF then some (.recvMulti (v % 2 ^ 32))
  else if v / 2 ^ 48 = 0xDC4F then some (.recvMsgMulti (v % 2 ^ 32))
  else if 2 ^ 63 ≤ v then some (.timer (v % 2 ^ 63))
  else some (.slab (v % 2 ^ 32) (v / 2 ^ 32))

/-- Every well-formed token fits in the 64-bit word. -/
theorem encode_lt_tokenSpace (t : Token) (h : t.Wf) : t.encode < tokenSpace := by
  cases t <;> simp only [Wf] at h <;> simp only [encode, tokenSpace] <;> omega

/-- **The partition theorem.** Decoding is a retraction of encoding on
well-formed tokens: every namespace is recovered, with its fields, from the
bare 64-bit word. -/
theorem decode_encode (t : Token) (h : t.Wf) : decode t.encode = some t := by
  cases t with
  | wakeup => decide
  | cancel => decide
  | slab index generation =>
    obtain ⟨h1, h2, h3⟩ := h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg]
    · simp only [Option.some.injEq, Token.slab.injEq]
      omega
    all_goals omega
  | acceptMulti fd =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.acceptMulti.injEq]
      omega
    all_goals omega
  | recvMulti fd =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.recvMulti.injEq]
      omega
    all_goals omega
  | recvMsgMulti fd =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.recvMsgMulti.injEq]
      omega
    all_goals omega
  | msgRing opcode source payload =>
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.msgRing.injEq]
      omega
    all_goals omega
  | msgRingSent => decide
  | channel id =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.channel.injEq]
      omega
    all_goals omega
  | timer job =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, Token.timer.injEq]
      omega
    all_goals omega

/-- **Injectivity across the whole space**: two well-formed tokens with the
same 64-bit encoding are the same token — no completion can be misrouted
between namespaces or between distinct objects of one namespace. -/
theorem encode_inj {a b : Token} (ha : a.Wf) (hb : b.Wf)
    (h : a.encode = b.encode) : a = b := by
  have hda := decode_encode a ha
  have hdb := decode_encode b hb
  rw [h] at hda
  exact Option.some.inj (hda.symm.trans hdb)

/-- The all-ones corner of the message-ring namespace is literally the cancel
sentinel. Well-formedness excludes exactly this point; a dispatch chain that
checks the cancel sentinel first resolves the alias silently at run time. -/
theorem msgRing_corner_aliases_cancel :
    encode (.msgRing 0xFF 0xFFFF (2 ^ 32 - 1)) = encode .cancel := by decide

/-- ... and that corner is not well-formed. -/
theorem msgRing_corner_not_wf : ¬ Wf (.msgRing 0xFF 0xFFFF (2 ^ 32 - 1)) := by
  decide

/-- **The generation bound is load-bearing.** With the `generation < 2^31`
bound dropped, a slab key collides with a multishot-recv tag: slot 5 at
reuse generation `0xBECF0000` encodes identically to the recv tag for
socket fd 5 — the completion for the pending op would dispatch as inbound
data for an unrelated socket. A free-running 32-bit generation counter
passes through windows like this one for every tagged namespace. -/
theorem slab_generation_overflow_collides :
    encode (.slab 5 0xBECF0000) = encode (.recvMulti 5) := by decide

/-- ... and that key is not well-formed. -/
theorem slab_generation_overflow_not_wf : ¬ Wf (.slab 5 0xBECF0000) := by
  decide

/-- Slot 0 is reserved: a zero slab key would collide with the wakeup
sentinel. (`Wf` requires `0 < index`.) -/
theorem slab_zero_aliases_wakeup :
    encode (.slab 0 0) = encode .wakeup := by decide

end Token

/-!
## The timeout-token sub-space

Kernel-timeout completions carry a *second* token — the timeout user token —
delivered through the timeout dispatch callback rather than the raw
completion word (the timeout operation itself rides a slab key). This
sub-space is partitioned by the top two bits:

  * bit 63 set — periodic-job tokens, job id in the low 63 bits;
  * bit 62 set, bit 63 clear — sweep-timer tokens, small id in the low bits,
    with one distinguished id (`20`) reserved for the connection deadline
    queue and matched exactly before the sweep test;
  * both clear — plain per-object tokens (below `2^62`).
-/

/-- The timeout-token namespaces. -/
inductive TimeoutToken where
  /-- A periodic job: bit 63 set, job id in the low 63 bits. -/
  | periodic (job : Nat)
  /-- The connection deadline queue's distinguished token: sweep id `20`. -/
  | deadlineMain
  /-- A sweep timer: bit 62 set, bit 63 clear, id in the low bits;
  id `20` is reserved for `deadlineMain`. -/
  | sweep (id : Nat)
  /-- A plain per-object token, below `2^62`. -/
  | plain (v : Nat)
  deriving Repr, DecidableEq, Inhabited

namespace TimeoutToken

/-- Field bounds per namespace. -/
def Wf : TimeoutToken → Prop
  | .periodic job => job < 2 ^ 63
  | .deadlineMain => True
  | .sweep id => id < 2 ^ 62 ∧ id ≠ 20
  | .plain v => v < 2 ^ 62

instance (t : TimeoutToken) : Decidable t.Wf := by
  cases t <;> (simp only [Wf]; infer_instance)

/-- Encode a timeout token. -/
def encode : TimeoutToken → Nat
  | .periodic job => 2 ^ 63 + job
  | .deadlineMain => 2 ^ 62 + 20
  | .sweep id => 2 ^ 62 + id
  | .plain v => v

/-- Decode, in dispatch priority order: the distinguished deadline token is
matched exactly first, then bit 63 (periodic), then bit 62 (sweep). -/
def decode (v : Nat) : Option TimeoutToken :=
  if v = 2 ^ 62 + 20 then some .deadlineMain
  else if 2 ^ 63 ≤ v then some (.periodic (v - 2 ^ 63))
  else if 2 ^ 62 ≤ v then some (.sweep (v - 2 ^ 62))
  else some (.plain v)

/-- Round-trip on well-formed timeout tokens. -/
theorem decode_encode (t : TimeoutToken) (h : t.Wf) : decode t.encode = some t := by
  cases t with
  | periodic job =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_pos]
    · simp only [Option.some.injEq, TimeoutToken.periodic.injEq]
      omega
    all_goals omega
  | deadlineMain => decide
  | sweep id =>
    obtain ⟨h1, h2⟩ := h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_pos]
    · simp only [Option.some.injEq, TimeoutToken.sweep.injEq]
      omega
    all_goals omega
  | plain v =>
    simp only [Wf] at h
    simp only [encode, decode]
    rw [if_neg, if_neg, if_neg]
    all_goals omega

/-- Injectivity of the timeout-token encoding on well-formed tokens. -/
theorem encode_inj {a b : TimeoutToken} (ha : a.Wf) (hb : b.Wf)
    (h : a.encode = b.encode) : a = b := by
  have hda := decode_encode a ha
  have hdb := decode_encode b hb
  rw [h] at hda
  exact Option.some.inj (hda.symm.trans hdb)

/-- Sweep id 20 is reserved: it encodes to the distinguished deadline
token. `Wf` excludes it from the sweep namespace. -/
theorem sweep_20_aliases_deadlineMain :
    encode (.sweep 20) = encode .deadlineMain := by decide

end TimeoutToken

/-! ## The token seam — timer against fd, by reuse

Timer completions and fd-bound completions share one 64-bit token word. The
theorems below instantiate the partition above for the deadline queue, which is
where the question arises: a fired timer must never dispatch as a socket
operation.
-/

/-- **A timer completion is unambiguous.** Any well-formed token whose encoding
equals a well-formed timer token's encoding *is* that timer token. Immediate from
`Token.encode_inj` — the bit-63 namespace does the work. -/
theorem timer_token_unambiguous {t : Token} {job : Nat}
    (ht : t.Wf) (hj : (Token.timer job).Wf)
    (h : t.encode = (Token.timer job).encode) : t = .timer job :=
  Token.encode_inj ht hj h

/-- A timer token never collides with a pending-operation slab key: a timer
firing can never dispatch as (and complete) a socket operation. -/
theorem timer_never_slab (job index gen : Nat)
    (hj : (Token.timer job).Wf) (hs : (Token.slab index gen).Wf) :
    (Token.timer job).encode ≠ (Token.slab index gen).encode := by
  intro h
  cases Token.encode_inj hj hs h

/-- A timer token never collides with a multishot-recv tag: a timer firing can
never dispatch as inbound socket data. -/
theorem timer_never_recv (job fd : Nat)
    (hj : (Token.timer job).Wf) (hr : (Token.recvMulti fd).Wf) :
    (Token.timer job).encode ≠ (Token.recvMulti fd).encode := by
  intro h
  cases Token.encode_inj hj hr h

/-- **The deadline queue's distinguished timeout token is unambiguous** in the
timeout-token sub-space: any well-formed timeout token encoding to it *is* it.
The queue's timeout dispatch (matched exactly, before the sweep test) can
therefore never steal another timer's completion. -/
theorem deadline_token_unambiguous {t : TimeoutToken} (ht : t.Wf)
    (h : t.encode = TimeoutToken.deadlineMain.encode) : t = .deadlineMain :=
  TimeoutToken.encode_inj ht trivial h

/-! ### Non-vacuity: both well-formedness conditions are satisfiable

Every theorem above assumes a well-formed token. These are the witnesses that the
assumption is not empty — the convention this project follows for a premise of its
own making, so that no theorem can be true only because nothing satisfies it.
-/

/-- Witness: a slab token with a live index and a small generation is well-formed. -/
theorem Token.Wf_witness : (Token.slab 1 0).Wf := by decide

/-- Witness: a sweep token inside its field, and outside the reserved id, is
well-formed — a branch of `Wf` with content, not the one that is `True`. -/
theorem TimeoutToken.Wf_witness : (TimeoutToken.sweep 21).Wf := by decide

end DN.Dataplane.Flow
