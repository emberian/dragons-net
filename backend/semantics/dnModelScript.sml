(* SPDX-License-Identifier: AGPL-3.0-or-later *)
(*
  The Lean model of Pancake, lean/DN/Compiler/Semantics.lean, written again in HOL clause by
  clause: the same constructors, the same helpers, the same matches in the same order. Lean's
  words are word64, its byte lists word8 lists, its strings HOL strings. dnModelProof proves this
  equal to panSem's evaluate on the subset; that it is the Lean text is read, and checked by
  evaluating both on the state corpus.
*)
Theory dnModel
Ancestors
  words list alist
Libs
  wordsLib

(* 1. Bytes *)

Definition dn_byte_align_def:
  dn_byte_align (w : word64) = w && ~(7w : word64)
End

Definition dn_byte_index_def:
  dn_byte_index (a : word64) (be : bool) =
    let d = 8 in if be then 8 * ((d - 1) - (w2n a MOD d)) else 8 * (w2n a MOD d)
End

Definition dn_get_byte_def:
  dn_get_byte (a : word64) (w : word64) be = (w2w (w >>> dn_byte_index a be) : word8)
End

Definition dn_word_slice_alt_def:
  dn_word_slice_alt hi lo (w : word64) =
    let low = (1w << lo) - 1w; high = (1w << hi) - 1w in w && (high && ~low)
End

Definition dn_set_byte_def:
  dn_set_byte (a : word64) (b : word8) (w : word64) be =
    let i = dn_byte_index a be in
      dn_word_slice_alt 64 (i + 8) w || (w2w b << i) || dn_word_slice_alt i 0 w
End

(* 2. Values, memory, the oracle, the state *)

Datatype:
  dn_outcome = OFailed | ODiverged
End

Datatype:
  dn_final = <| fname : string; fconf : word8 list; farray : word8 list; foutcome : dn_outcome |>
End

Datatype:
  dn_result = RError | RTimeout | RBreak | RContinue | RReturn word64 | RFinalFFI dn_final
End

Datatype:
  dn_ffi_result = FFinal dn_final | FRet 'w (word8 list)
End

Datatype:
  dn_oracle_result = ORet 'w (word8 list) | OFinal dn_outcome
End

Definition dn_call_ffi_def:
  dn_call_ffi (oracle : 'w -> string -> word8 list -> word8 list -> 'w dn_oracle_result) ffi name conf array =
    if name = "" then FRet ffi array
    else
      case oracle ffi name conf array of
      | ORet newffi newBytes =>
          if LENGTH newBytes = LENGTH array then FRet newffi newBytes
          else FFinal <| fname := name; fconf := conf; farray := array; foutcome := OFailed |>
      | OFinal outcome => FFinal <| fname := name; fconf := conf; farray := array; foutcome := outcome |>
End

Definition dn_mem_load_byte_def:
  dn_mem_load_byte (m : word64 -> word64) (dm : word64 -> bool) be w =
    if dm (dn_byte_align w) then SOME (dn_get_byte w (m (dn_byte_align w)) be) else NONE
End

Definition dn_mem_store_word_def:
  dn_mem_store_word (m : word64 -> word64) (dm : word64 -> bool) addr w =
    if dm addr then SOME (\k. if k = addr then w else m k) else NONE
End

Definition dn_mem_store_byte_def:
  dn_mem_store_byte (m : word64 -> word64) (dm : word64 -> bool) be w (b : word8) =
    if dm (dn_byte_align w)
    then SOME (\k. if k = dn_byte_align w then dn_set_byte w b (m (dn_byte_align w)) be else m k)
    else NONE
End

Definition dn_read_byte_array_def:
  dn_read_byte_array m dm be (a : word64) 0 = SOME [] /\
  dn_read_byte_array m dm be a (SUC n) =
    case dn_mem_load_byte m dm be a of
    | NONE => NONE
    | SOME b =>
        case dn_read_byte_array m dm be (a + 1w) n of
        | NONE => NONE
        | SOME bs => SOME (b :: bs)
End

Definition dn_write_byte_array_def:
  dn_write_byte_array dm be (a : word64) [] m = m /\
  dn_write_byte_array dm be a (b :: bs) m =
    case dn_mem_store_byte (dn_write_byte_array dm be (a + 1w) bs m) dm be a b of
    | SOME m' => m'
    | NONE => m
End

(* 3. Expressions *)

Datatype:
  dn_binop = BAdd | BAnd | BSub | BXor | BOr
End

Datatype:
  dn_cmp = CLess | CEqual | CNotLess
End

Datatype:
  dn_exp = EConst word64
      | EVar string
      | EBase
      | EOp dn_binop dn_exp dn_exp
      | EMul dn_exp dn_exp
      | ECmp dn_cmp dn_exp dn_exp
      | ELoadByte dn_exp
      | ELoadWord dn_exp
      | EShiftR dn_exp dn_exp
      | EShiftL dn_exp dn_exp
End

Datatype:
  dn_prog = PSkip
       | PDec string dn_exp dn_prog
       | PAssign string dn_exp
       | PStore dn_exp dn_exp
       | PExtCall string dn_exp dn_exp dn_exp dn_exp
       | PSeq dn_prog dn_prog
       | PCond dn_exp dn_prog dn_prog
       | PWhile dn_exp dn_prog
       | PRet dn_exp
       | PStoreByte dn_exp dn_exp
       | PDecCall string string (dn_exp list) dn_prog
End

Datatype:
  dn_state = <| locals : string -> word64 option
           ; memory : word64 -> word64
           ; memaddrs : word64 -> bool
           ; be : bool
           ; clock : num
           ; ffi : 'w
           ; baseAddr : word64
           ; code : string -> (string list # dn_prog) option |>
End

Definition dn_eval_def:
  dn_eval (s : 'w dn_state) (EConst w) = SOME w /\
  dn_eval s (EVar name) = s.locals name /\
  dn_eval s EBase = SOME s.baseAddr /\
  dn_eval s (EOp bop l r) =
    (case (dn_eval s l, dn_eval s r) of
     | (SOME a, SOME b) =>
         (case bop of
          | BAdd => SOME (a + b)
          | BAnd => SOME (a && b)
          | BSub => SOME (a - b)
          | BXor => SOME (a ?? b)
          | BOr => SOME (a || b))
     | _ => NONE) /\
  dn_eval s (EMul l r) =
    (case (dn_eval s l, dn_eval s r) of
     | (SOME a, SOME b) => SOME (a * b)
     | _ => NONE) /\
  dn_eval s (EShiftR l r) =
    (case (dn_eval s l, dn_eval s r) of
     | (SOME a, SOME b) =>
         let places = w2n b in if places <> 0 /\ places >= 64 then NONE else SOME (a >>> places)
     | _ => NONE) /\
  dn_eval s (EShiftL l r) =
    (case (dn_eval s l, dn_eval s r) of
     | (SOME a, SOME b) =>
         let places = w2n b in if places <> 0 /\ places >= 64 then NONE else SOME (a << places)
     | _ => NONE) /\
  dn_eval s (ECmp CLess l r) =
    (case (dn_eval s l, dn_eval s r) of
     | (SOME a, SOME b) => SOME (if a < b then 1w else 0w)
     | _ => NONE) /\
  dn_eval s (ECmp CEqual l r) =
    (case (dn_eval s l, dn_eval s r) of
     | (SOME a, SOME b) => SOME (if a = b then 1w else 0w)
     | _ => NONE) /\
  dn_eval s (ECmp CNotLess l r) =
    (case (dn_eval s l, dn_eval s r) of
     | (SOME a, SOME b) => SOME (if a < b then 0w else 1w)
     | _ => NONE) /\
  dn_eval s (ELoadByte addr) =
    (case dn_eval s addr of
     | SOME w =>
         (case dn_mem_load_byte s.memory s.memaddrs s.be w of
          | SOME b => SOME (w2w b)
          | NONE => NONE)
     | NONE => NONE) /\
  dn_eval s (ELoadWord addr) =
    (case dn_eval s addr of
     | SOME w => if s.memaddrs w then SOME (s.memory w) else NONE
     | NONE => NONE)
End

(* 4. Programs *)

Definition dn_set_local_def:
  dn_set_local (lc : string -> word64 option) v (val : word64) = \k. if k = v then SOME val else lc k
End

Definition dn_res_var_def:
  dn_res_var (lc : string -> word64 option) v (old : word64 option) = \k. if k = v then old else lc k
End

Definition dn_empty_locals_def:
  dn_empty_locals (s : 'w dn_state) = s with locals := (\k. NONE)
End

Definition dn_dec_clock_def:
  dn_dec_clock (s : 'w dn_state) = s with clock := s.clock - 1
End

Definition dn_clamp_clock_def:
  dn_clamp_clock old (r : dn_result option # 'w dn_state) = (FST r, SND r with clock := MIN old (SND r).clock)
End

Definition dn_lookup_code_def:
  dn_lookup_code (code : string -> (string list # dn_prog) option) f (args : word64 list) =
    case code f of
    | SOME (params, body) =>
        if ALL_DISTINCT params /\ LENGTH params = LENGTH args
        then SOME (body, \k. ALOOKUP (ZIP (params, args)) k)
        else NONE
    | NONE => NONE
End

Definition dn_eval_args_def:
  dn_eval_args (s : 'w dn_state) [] = SOME [] /\
  dn_eval_args s (e :: es) =
    case (dn_eval s e, dn_eval_args s es) of
    | (SOME v, SOME vs) => SOME (v :: vs)
    | _ => NONE
End

Definition dn_call_ended_def:
  dn_call_ended (r : dn_result option) (st : 'w dn_state) =
    case r of
    | NONE => (SOME RError, st)
    | SOME RBreak => (SOME RError, st)
    | SOME RContinue => (SOME RError, st)
    | SOME res => (SOME res, dn_empty_locals st)
End

Definition dn_sem_def:
  (dn_sem oracle PSkip (s : 'w dn_state) = (NONE, s)) /\
  (dn_sem oracle (PDec v e cont) s =
     case dn_eval s e of
     | SOME val =>
         let r = dn_sem oracle cont (s with locals := dn_set_local s.locals v val) in
           (FST r, SND r with locals := dn_res_var (SND r).locals v (s.locals v))
     | NONE => (SOME RError, s)) /\
  (dn_sem oracle (PAssign v e) s =
     case (dn_eval s e, s.locals v) of
     | (SOME val, SOME _) => (NONE, s with locals := dn_set_local s.locals v val)
     | _ => (SOME RError, s)) /\
  (dn_sem oracle (PStore dst src) s =
     case (dn_eval s dst, dn_eval s src) of
     | (SOME addr, SOME val) =>
         (case dn_mem_store_word s.memory s.memaddrs addr val of
          | SOME m => (NONE, s with memory := m)
          | NONE => (SOME RError, s))
     | _ => (SOME RError, s)) /\
  (dn_sem oracle (PExtCall name cptr clen aptr alen) s =
     case (dn_eval s cptr, dn_eval s clen, dn_eval s aptr, dn_eval s alen) of
     | (SOME cp, SOME cl, SOME ap, SOME al) =>
         (case (dn_read_byte_array s.memory s.memaddrs s.be cp (w2n cl),
                dn_read_byte_array s.memory s.memaddrs s.be ap (w2n al)) of
          | (SOME conf, SOME arr) =>
              (case dn_call_ffi oracle s.ffi name conf arr of
               | FFinal event => (SOME (RFinalFFI event), dn_empty_locals s)
               | FRet newffi newBytes =>
                   (NONE, s with <| memory := dn_write_byte_array s.memaddrs s.be ap newBytes s.memory;
                                    ffi := newffi |>))
          | _ => (SOME RError, s))
     | _ => (SOME RError, s)) /\
  (dn_sem oracle (PSeq c1 c2) s =
     let r = dn_clamp_clock s.clock (dn_sem oracle c1 s) in
       case FST r of
       | NONE => dn_sem oracle c2 (SND r)
       | SOME res => (SOME res, SND r)) /\
  (dn_sem oracle (PCond e c1 c2) s =
     case dn_eval s e of
     | SOME w => dn_sem oracle (if w <> 0w then c1 else c2) s
     | NONE => (SOME RError, s)) /\
  (dn_sem oracle (PWhile e c) s =
     case dn_eval s e of
     | SOME w =>
         if w <> 0w then
           if s.clock = 0 then (SOME RTimeout, dn_empty_locals s)
           else
             let r = dn_clamp_clock (s.clock - 1) (dn_sem oracle c (dn_dec_clock s)) in
               case FST r of
               | SOME RContinue => dn_sem oracle (PWhile e c) (SND r)
               | NONE => dn_sem oracle (PWhile e c) (SND r)
               | SOME RBreak => (NONE, SND r)
               | SOME res => (SOME res, SND r)
         else (NONE, s)
     | NONE => (SOME RError, s)) /\
  (dn_sem oracle (PRet e) s =
     case dn_eval s e of
     | SOME v => (SOME (RReturn v), dn_empty_locals s)
     | NONE => (SOME RError, s)) /\
  (dn_sem oracle (PStoreByte dst src) s =
     case (dn_eval s dst, dn_eval s src) of
     | (SOME adr, SOME w) =>
         (case dn_mem_store_byte s.memory s.memaddrs s.be adr (w2w w) of
          | SOME m => (NONE, s with memory := m)
          | NONE => (SOME RError, s))
     | _ => (SOME RError, s)) /\
  (dn_sem oracle (PDecCall rt f args cont) s =
     case dn_eval_args s args of
     | SOME vs =>
         (case dn_lookup_code s.code f vs of
          | SOME (body, params) =>
              if s.clock = 0 then (SOME RTimeout, dn_empty_locals s)
              else
                (let r = dn_clamp_clock (s.clock - 1) (dn_sem oracle body (dn_dec_clock s with locals := params)) in
                   case FST r of
                   | SOME (RReturn v) =>
                       let r2 = dn_sem oracle cont (SND r with locals := dn_set_local s.locals rt v) in
                         (FST r2, SND r2 with locals := dn_res_var (SND r2).locals rt (s.locals rt))
                   | other => dn_call_ended other (SND r))
          | NONE => (SOME RError, s))
     | NONE => (SOME RError, s))
Termination
  WF_REL_TAC `inv_image (measure I LEX measure dn_prog_size) (\(orc,p,s). (s.clock, p))` >>
  rw[dn_clamp_clock_def, dn_dec_clock_def, arithmeticTheory.MIN_DEF] >> gvs[]
End
