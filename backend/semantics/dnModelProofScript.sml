(* SPDX-License-Identifier: AGPL-3.0-or-later *)
(*
  dnModel, the Lean model written in HOL, against panSem itself: the byte helpers are HOL's, and
  on the subset the model's expressions and programs end where panSem's evaluate does.
*)
Theory dnModelProof
Ancestors
  dnModel panSem panLang ffi misc byte alignment wordLang asm
Libs
  wordsLib blastLib

(* c1. The byte helpers *)

Theorem dn_byte_align_thm:
  dn_byte_align w = byte_align (w : word64)
Proof
  `LOG2 (dimindex (:64) DIV 8) = 3` by EVAL_TAC >>
  simp[dn_byte_align_def, byte_align_def, align_def] >> BBLAST_TAC
QED

Theorem dn_byte_index_thm:
  dn_byte_index a be = byte_index (a : word64) be
Proof
  simp[dn_byte_index_def, byte_index_def]
QED

Theorem dn_get_byte_thm:
  dn_get_byte a w be = get_byte (a : word64) (w : word64) be
Proof
  simp[dn_get_byte_def, get_byte_def, dn_byte_index_thm]
QED

Theorem dn_byte_index_cases[local]:
  dn_byte_index a be IN {0; 8; 16; 24; 32; 40; 48; 56}
Proof
  `w2n a MOD 8 < 8` by simp[] >>
  qabbrev_tac `k = w2n a MOD 8` >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7` by decide_tac >>
  rw[dn_byte_index_def]
QED

Theorem dn_set_byte_thm:
  dn_set_byte a b w be = set_byte (a : word64) b (w : word64) be
Proof
  assume_tac dn_byte_index_cases >>
  fs[dn_set_byte_def, set_byte_64, GSYM dn_byte_index_thm] >>
  rw[dn_word_slice_alt_def] >> BBLAST_TAC
QED

Theorem dn_mem_load_byte_thm:
  mem_load_byte (Word o m) dm be w = dn_mem_load_byte m dm be (w : word64)
Proof
  simp[mem_load_byte_def, dn_mem_load_byte_def, dn_byte_align_thm, dn_get_byte_thm, IN_DEF]
QED

Theorem dn_mem_store_byte_thm:
  mem_store_byte (Word o m) dm be w b =
    OPTION_MAP (\m'. Word o m') (dn_mem_store_byte m dm be (w : word64) b)
Proof
  simp[mem_store_byte_def, dn_mem_store_byte_def, GSYM dn_byte_align_thm, GSYM dn_set_byte_thm, IN_DEF] >>
  IF_CASES_TAC >> simp[combinTheory.APPLY_UPDATE_THM] >>
  simp[FUN_EQ_THM] >> qx_gen_tac `k` >> simp[combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `k = dn_byte_align w` >> simp[]
QED

(* c2. Expressions *)

Definition pan_binop_def:
  pan_binop BAdd = Add /\ pan_binop BAnd = And /\ pan_binop BSub = Sub /\
  pan_binop BXor = Xor /\ pan_binop BOr = Or
End

Definition pan_cmp_def:
  pan_cmp CLess = Less /\ pan_cmp CEqual = Equal /\ pan_cmp CNotLess = NotLess
End

(* A shift by an expression has no panLang form at this revision; exp_ok keeps literal ones. *)
Definition pan_exp_def:
  pan_exp (EConst w) = (Const w : 64 panLang$exp) /\
  pan_exp (EVar v) = Var Local (implode v) /\
  pan_exp EBase = BaseAddr /\
  pan_exp (EOp b l r) = Op (pan_binop b) [pan_exp l; pan_exp r] /\
  pan_exp (EMul l r) = Panop Mul [pan_exp l; pan_exp r] /\
  pan_exp (ECmp c l r) = Cmp (pan_cmp c) (pan_exp l) (pan_exp r) /\
  pan_exp (ELoadByte a) = LoadByte (pan_exp a) /\
  pan_exp (ELoadWord a) = Load One (pan_exp a) /\
  pan_exp (EShiftR l r) = Shift Lsr (pan_exp l) (case r of EConst k => w2n k | _ => 0) /\
  pan_exp (EShiftL l r) = Shift Lsl (pan_exp l) (case r of EConst k => w2n k | _ => 0)
End

Definition exp_ok_def:
  exp_ok (EOp b l r) = (exp_ok l /\ exp_ok r) /\
  exp_ok (EMul l r) = (exp_ok l /\ exp_ok r) /\
  exp_ok (ECmp c l r) = (exp_ok l /\ exp_ok r) /\
  exp_ok (ELoadByte a) = exp_ok a /\
  exp_ok (ELoadWord a) = exp_ok a /\
  exp_ok (EShiftR l r) = (exp_ok l /\ ?k. r = EConst k) /\
  exp_ok (EShiftL l r) = (exp_ok l /\ ?k. r = EConst k) /\
  exp_ok _ = T
End

Definition locals_rel_def:
  locals_rel (fm : mlstring |-> 64 v) (lc : string -> word64 option) <=>
    !k. FLOOKUP fm k = OPTION_MAP ValWord (lc (explode k))
End

Definition mem_rel_def:
  mem_rel (t : (64, 'w) panSem$state) (s : 'w dn_state) <=>
    locals_rel t.locals s.locals /\ t.memory = Word o s.memory /\ t.memaddrs = s.memaddrs /\
    t.be = s.be /\ t.base_addr = s.baseAddr
End

Theorem dn_eval_cmp[local]:
  dn_eval s (ECmp c l r) =
    case (dn_eval s l, dn_eval s r) of
    | (SOME a, SOME b) =>
        SOME (if (case c of CLess => a < b | CEqual => a = b | CNotLess => ~(a < b)) then 1w else 0w)
    | _ => NONE
Proof
  Cases_on `c` >> rw[dn_eval_def] >> rpt CASE_TAC >> rw[]
QED

Theorem word_cmp_pan[local]:
  word_cmp (pan_cmp c) a b = (case c of CLess => a < b | CEqual => a = b | CNotLess => ~(a < b))
Proof
  Cases_on `c` >> rw[pan_cmp_def, word_cmp_def]
QED

Theorem dn_eval_thm:
  !t s. mem_rel t s ==> !e. exp_ok e ==> eval t (pan_exp e) = OPTION_MAP ValWord (dn_eval s e)
Proof
  ntac 3 strip_tac >> fs[mem_rel_def] >> Induct >>
  rw[pan_exp_def, exp_ok_def, dn_eval_cmp, dn_eval_def, eval_def, word_cmp_pan, dn_mem_load_byte_thm,
     mem_load_def, is_wf_shape_def, word_sh_def] >>
  gvs[locals_rel_def, mlstringTheory.explode_implode, IN_DEF] >>
  gvs[dn_eval_def, pan_exp_def, eval_def, word_sh_def] >>
  rpt (CASE_TAC >> gvs[]) >> simp[pan_binop_def, word_op_def, pan_op_def]
QED

(* c3, c4. Programs *)

Definition pan_prog_def:
  pan_prog PSkip = (Skip : 64 panLang$prog) /\
  pan_prog (PDec v e c) = Dec (implode v) One (pan_exp e) (pan_prog c) /\
  pan_prog (PAssign v e) = Assign Local (implode v) (pan_exp e) /\
  pan_prog (PStore d e) = Store (pan_exp d) (pan_exp e) /\
  pan_prog (PExtCall n a b c d) = ExtCall (implode n) (pan_exp a) (pan_exp b) (pan_exp c) (pan_exp d) /\
  pan_prog (PSeq a b) = Seq (pan_prog a) (pan_prog b) /\
  pan_prog (PCond e a b) = If (pan_exp e) (pan_prog a) (pan_prog b) /\
  pan_prog (PWhile e c) = While (pan_exp e) (pan_prog c) /\
  pan_prog (PRet e) = Return (pan_exp e) /\
  pan_prog (PStoreByte d e) = StoreByte (pan_exp d) (pan_exp e) /\
  pan_prog (PDecCall r f args c) = DecCall (implode r) One (implode f) (MAP pan_exp args) (pan_prog c)
End

Definition prog_ok_def:
  prog_ok (PDec v e c) = (exp_ok e /\ prog_ok c) /\
  prog_ok (PAssign v e) = exp_ok e /\
  prog_ok (PStore d e) = (exp_ok d /\ exp_ok e) /\
  prog_ok (PExtCall n a b c d) = (exp_ok a /\ exp_ok b /\ exp_ok c /\ exp_ok d) /\
  prog_ok (PSeq a b) = (prog_ok a /\ prog_ok b) /\
  prog_ok (PCond e a b) = (exp_ok e /\ prog_ok a /\ prog_ok b) /\
  prog_ok (PWhile e c) = (exp_ok e /\ prog_ok c) /\
  prog_ok (PRet e) = exp_ok e /\
  prog_ok (PStoreByte d e) = (exp_ok d /\ exp_ok e) /\
  prog_ok (PDecCall r f args c) = (EVERY exp_ok args /\ prog_ok c) /\
  prog_ok PSkip = T
End

Definition code_rel_def:
  code_rel (tc : mlstring |-> ((mlstring # shape) list # 64 panLang$prog))
           (sc : string -> (string list # dn_prog) option) <=>
    (!f. FLOOKUP tc f = OPTION_MAP (\(ps, b). (MAP (\p. (implode p, One)) ps, pan_prog b)) (sc (explode f))) /\
    (!f ps b. sc f = SOME (ps, b) ==> prog_ok b)
End

Definition pan_outcome_def:
  pan_outcome OFailed = FFI_failed /\ pan_outcome ODiverged = FFI_diverged
End

Definition pan_oracle_def:
  pan_oracle (orc : 'w -> string -> word8 list -> word8 list -> 'w dn_oracle_result) =
    \nm st conf arr.
      case nm of
      | ExtCall n =>
          (case orc st (explode n) conf arr of
           | ORet st' bs => Oracle_return st' bs
           | OFinal out => Oracle_final (pan_outcome out))
      | SharedMem _ => Oracle_final FFI_failed
End

Definition pan_final_def:
  pan_final (e : dn_final) = Final_event (ExtCall (implode e.fname)) e.fconf e.farray (pan_outcome e.foutcome)
End

Definition pan_res_def:
  pan_res RError = (Error : 64 panSem$result) /\
  pan_res RTimeout = TimeOut /\
  pan_res RBreak = Break /\
  pan_res RContinue = Continue /\
  pan_res (RReturn w) = Return (ValWord w) /\
  pan_res (RFinalFFI e) = FinalFFI (pan_final e)
End

Definition state_rel_def:
  state_rel orc (t : (64, 'w) panSem$state) (s : 'w dn_state) <=>
    mem_rel t s /\ t.clock = s.clock /\ t.ffi.ffi_state = s.ffi /\ t.ffi.oracle = pan_oracle orc /\
    code_rel t.code s.code
End

Theorem locals_rel_update[local]:
  locals_rel fm lc ==> locals_rel (fm |+ (implode v, ValWord w)) (dn_set_local lc v w)
Proof
  rw[locals_rel_def, dn_set_local_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[mlstringTheory.explode_implode] >>
  `k <> implode v` by (strip_tac >> gvs[mlstringTheory.explode_implode]) >> gvs[]
QED

Theorem locals_rel_res_var[local]:
  locals_rel fm lc ==>
  locals_rel (res_var fm (implode v, OPTION_MAP ValWord old)) (dn_res_var lc v old)
Proof
  Cases_on `old` >>
  rw[locals_rel_def, dn_res_var_def, res_var_def, finite_mapTheory.FLOOKUP_UPDATE,
     finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  rw[] >> gvs[mlstringTheory.explode_implode] >>
  TRY (`k <> implode v` by (strip_tac >> gvs[mlstringTheory.explode_implode])) >> gvs[]
QED

Theorem locals_rel_empty[local]:
  locals_rel FEMPTY (\k. NONE)
Proof
  rw[locals_rel_def]
QED

(* The clause of dn_sem_def for the statement named, chosen by its constructor. *)
fun sem name =
  Lib.first (fn th => #1 (dest_const (repeat rator (el 2 (#2 (strip_comb (lhs (concl (SPEC_ALL th)))))))) = name
                      handle HOL_ERR _ => false)
    (CONJUNCTS dn_sem_def);

Theorem read_thm[local]:
  !n a. read_bytearray a n (mem_load_byte (Word o m) dm be) = dn_read_byte_array m dm be (a : word64) n
Proof
  Induct >> rw[read_bytearray_def, dn_read_byte_array_def, dn_mem_load_byte_thm]
QED

Theorem write_thm[local]:
  !bs a m. write_bytearray a bs (Word o m) dm be = Word o dn_write_byte_array dm be (a : word64) bs m
Proof
  Induct >> rw[write_bytearray_def, dn_write_byte_array_def, dn_mem_store_byte_thm] >>
  Cases_on `dn_mem_store_byte (dn_write_byte_array dm be (a + 1w) bs m) dm be a h` >> simp[]
QED

Theorem clamp_id[local]:
  (SND r).clock <= n ==> dn_clamp_clock n (r : dn_result option # 'w dn_state) = r
Proof
  Cases_on `r` >> rw[dn_clamp_clock_def, arithmeticTheory.MIN_DEF] >> simp[dn_state_component_equality]
QED

Theorem args_thm[local]:
  !args. mem_rel t s /\ EVERY exp_ok args ==>
    OPT_MMAP (eval t) (MAP pan_exp args) = OPTION_MAP (MAP ValWord) (dn_eval_args s args)
Proof
  Induct >> rw[dn_eval_args_def] >> imp_res_tac dn_eval_thm >> simp[] >>
  Cases_on `dn_eval s h` >> Cases_on `dn_eval_args s args` >> gvs[]
QED

Theorem alookup_rev[local]:
  ALL_DISTINCT (MAP FST l) ==> ALOOKUP (REVERSE l) = ALOOKUP l
Proof
  strip_tac >> irule alistTheory.ALOOKUP_ALL_DISTINCT_PERM_same >>
  simp[listTheory.MAP_REVERSE, sortingTheory.PERM_REVERSE_EQ, listTheory.ALL_DISTINCT_REVERSE] >>
  simp[pred_setTheory.EXTENSION]
QED

Theorem alookup_implode[local]:
  !ps (ws : 'b list) k. LENGTH ps = LENGTH ws ==>
    ALOOKUP (ZIP (MAP implode ps, ws)) k = ALOOKUP (ZIP (ps, ws)) (explode k)
Proof
  Induct >> rw[] >> Cases_on `ws` >> gvs[] >> rw[] >> gvs[mlstringTheory.explode_implode] >>
  Cases_on `k` >> gvs[mlstringTheory.explode_def]
QED

Theorem distinct_thm[local]:
  !ps. ALL_DISTINCT (MAP FST (MAP (\p. (implode p, One)) ps)) <=> ALL_DISTINCT ps
Proof
  gen_tac >> simp[listTheory.MAP_MAP_o, combinTheory.o_DEF] >> eq_tac >> strip_tac
  >- metis_tac[listTheory.ALL_DISTINCT_MAP]
  >- (irule listTheory.ALL_DISTINCT_MAP_INJ >> simp[])
QED

Theorem shapes_thm[local]:
  !ps. LIST_REL (\vshape arg. SND vshape = shape_of arg) (MAP (\p. (implode p, One)) ps) (MAP ValWord (vs : word64 list)) <=> LENGTH ps = LENGTH vs
Proof
  rw[listTheory.LIST_REL_EL_EQN, listTheory.EL_MAP, shape_of_def] >> eq_tac >> rw[listTheory.EL_MAP, shape_of_def]
QED

Theorem zip_distinct[local]:
  LENGTH x0 = LENGTH (vs : word64 list) /\ ALL_DISTINCT x0 ==> ALL_DISTINCT (MAP FST (ZIP (MAP implode x0, MAP ValWord vs)))
Proof
  rw[] >> simp[listTheory.MAP_ZIP] >> irule listTheory.ALL_DISTINCT_MAP_INJ >> simp[]
QED

Theorem newlocals_thm[local]:
  LENGTH x0 = LENGTH (vs : word64 list) /\ ALL_DISTINCT x0 ==>
    locals_rel (FEMPTY |++ ZIP (MAP implode x0, MAP ValWord vs)) (\k. ALOOKUP (ZIP (x0, vs)) k)
Proof
  rw[locals_rel_def] >> imp_res_tac zip_distinct >>
  simp[alistTheory.FLOOKUP_FUPDATE_LIST, alookup_rev, alookup_implode, alistTheory.ALOOKUP_ZIP_MAP_SND] >>
  CASE_TAC >> simp[]
QED

Theorem lookup_thm[local]:
  code_rel tc sc ==>
    (dn_lookup_code sc f vs = NONE ==> lookup_code tc (implode f) (MAP ValWord vs) = NONE) /\
    (dn_lookup_code sc f vs = SOME (body, params) ==>
       ?nl. lookup_code tc (implode f) (MAP ValWord vs) = SOME (pan_prog body, nl) /\
            locals_rel nl params /\ prog_ok body)
Proof
  strip_tac >> fs[code_rel_def] >>
  first_x_assum (qspec_then `implode f` assume_tac) >> fs[mlstringTheory.explode_implode] >>
  rw[dn_lookup_code_def, lookup_code_def] >> Cases_on `sc f` >> gvs[] >> PairCases_on `x` >>
  gvs[distinct_thm, shapes_thm] >> rw[] >> gvs[] >> res_tac >>
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, ETA_THM] >> irule newlocals_thm >> simp[]
QED

Theorem lookup_none[local]:
  code_rel tc sc /\ dn_lookup_code sc f vs = NONE ==> lookup_code tc (implode f) (MAP ValWord vs) = NONE
Proof
  metis_tac[lookup_thm]
QED

Theorem lookup_some[local]:
  code_rel tc sc /\ dn_lookup_code sc f vs = SOME (body, params) ==>
       ?nl. lookup_code tc (implode f) (MAP ValWord vs) = SOME (pan_prog body, nl) /\
            locals_rel nl params /\ prog_ok body
Proof
  metis_tac[lookup_thm]
QED

Theorem dn_sem_thm:
  !orc p s t. prog_ok p /\ state_rel orc t s ==>
    ?t'. evaluate (pan_prog p, t) = (OPTION_MAP pan_res (FST (dn_sem orc p s)), t') /\
         state_rel orc t' (SND (dn_sem orc p s))
Proof
  recInduct dn_sem_ind >> rpt conj_tac
  (* Skip *)
  >- (
    rw[pan_prog_def, Once evaluate_def, sem "PSkip"])
  (* Dec *)
  >- (
    rw[pan_prog_def, prog_ok_def] >>
    simp[Once evaluate_def, sem "PDec"] >>
    `mem_rel t s` by fs[state_rel_def] >>
    drule dn_eval_thm >> disch_then (qspec_then `e` mp_tac) >> simp[] >> strip_tac >>
    Cases_on `dn_eval s e` >> gvs[shape_of_def, pan_res_def] >> rename1 `dn_eval s e = SOME val` >>
    qpat_x_assum `!t'. _` (qspec_then `t with locals := (t.locals |+ (implode v, ValWord val))` mp_tac) >>
    impl_tac >- (fs[state_rel_def, mem_rel_def] >> irule locals_rel_update >> simp[]) >>
    strip_tac >> simp[] >>
    fs[state_rel_def, mem_rel_def] >>
    `FLOOKUP t.locals (implode v) = OPTION_MAP ValWord (s.locals v)` by fs[locals_rel_def, mlstringTheory.explode_implode] >>
    simp[locals_rel_res_var])
  (* Assign *)
  >- (
    rw[pan_prog_def, prog_ok_def] >> simp[Once evaluate_def, sem "PAssign"] >>
    `mem_rel t s` by fs[state_rel_def] >>
    drule dn_eval_thm >> disch_then (qspec_then `e` mp_tac) >> simp[] >> strip_tac >>
    `FLOOKUP t.locals (implode v) = OPTION_MAP ValWord (s.locals v)` by
    fs[state_rel_def, mem_rel_def, locals_rel_def, mlstringTheory.explode_implode] >>
    Cases_on `dn_eval s e` >> Cases_on `s.locals v` >>
    gvs[is_valid_value_def, shape_of_def, pan_res_def, set_var_def] >>
    fs[state_rel_def, mem_rel_def] >> irule locals_rel_update >> simp[])
  (* Store *)
  >- (
    rw[pan_prog_def, prog_ok_def] >> simp[Once evaluate_def, sem "PStore"] >>
    `mem_rel t s` by fs[state_rel_def] >> imp_res_tac dn_eval_thm >> simp[] >>
    Cases_on `dn_eval s dst` >> Cases_on `dn_eval s src` >>
    gvs[pan_res_def, flatten_def, mem_stores_def, mem_store_def, dn_mem_store_word_def, IN_DEF] >>
    fs[state_rel_def, mem_rel_def] >> rw[] >> gvs[pan_res_def] >>
    simp[FUN_EQ_THM, combinTheory.APPLY_UPDATE_THM] >> rw[])
  (* ExtCall *)
  >- (
    rw[pan_prog_def, prog_ok_def] >> simp[Once evaluate_def, sem "PExtCall"] >>
    `mem_rel t s` by fs[state_rel_def] >> imp_res_tac dn_eval_thm >> simp[] >>
    `t.memory = Word o s.memory /\ t.memaddrs = s.memaddrs /\ t.be = s.be /\
    t.ffi.oracle = pan_oracle oracle /\ t.ffi.ffi_state = s.ffi` by fs[state_rel_def, mem_rel_def] >>
    simp[read_thm] >>
    rpt (CASE_TAC >> gvs[pan_res_def]) >>
    gvs[call_FFI_def, dn_call_ffi_def, pan_oracle_def, AllCaseEqs()] >>
    gvs[pan_res_def, pan_final_def, pan_outcome_def, state_rel_def, mem_rel_def, write_thm,
    empty_locals_def, dn_empty_locals_def, locals_rel_empty])
  (* Seq *)
  >- (
    rw[pan_prog_def, prog_ok_def] >> simp[Once evaluate_def, sem "PSeq"] >>
    qpat_x_assum `!t. prog_ok c1 /\ _ ==> _` (qspec_then `t` mp_tac) >> simp[] >> strip_tac >>
    imp_res_tac evaluate_clock >>
    `(SND (dn_sem oracle c1 s)).clock <= s.clock` by fs[state_rel_def] >>
    gvs[clamp_id] >>
    Cases_on `FST (dn_sem oracle c1 s)` >> gvs[] >>
    first_x_assum (qspec_then `t'` mp_tac) >> simp[])
  (* If *)
  >- (
    rw[pan_prog_def, prog_ok_def] >> simp[Once evaluate_def, sem "PCond"] >>
    `mem_rel t s` by fs[state_rel_def] >> imp_res_tac dn_eval_thm >> simp[] >>
    Cases_on `dn_eval s e` >> gvs[pan_res_def] >> rename1 `dn_eval s e = SOME w` >>
    Cases_on `w = 0w` >> gvs[] >> first_x_assum (qspec_then `t` mp_tac) >> simp[])
  (* While *)
  >- (
    rw[pan_prog_def, prog_ok_def] >> ONCE_REWRITE_TAC [sem "PWhile"] >> simp[Once evaluate_def] >>
    `mem_rel t s` by fs[state_rel_def] >> imp_res_tac dn_eval_thm >> simp[] >>
    Cases_on `dn_eval s e` >> gvs[pan_res_def] >> rename1 `dn_eval s e = SOME w` >>
    Cases_on `w = 0w` >> gvs[] >>
    `t.clock = s.clock` by fs[state_rel_def] >>
    Cases_on `s.clock = 0` >> gvs[pan_res_def] >>
    TRY (fs[state_rel_def, mem_rel_def, empty_locals_def, dn_empty_locals_def, locals_rel_empty] >> NO_TAC) >>
    qpat_assum `!t'. state_rel oracle t' (dn_dec_clock s) ==> _` (qspec_then `dec_clock t` mp_tac) >>
    impl_tac >- fs[state_rel_def, mem_rel_def, dec_clock_def, dn_dec_clock_def] >>
    strip_tac >> simp[] >>
    imp_res_tac evaluate_clock >> fs[dec_clock_def] >>
    `(SND (dn_sem oracle c (dn_dec_clock s))).clock <= s.clock - 1` by fs[state_rel_def] >>
    gvs[clamp_id] >>
    Cases_on `FST (dn_sem oracle c (dn_dec_clock s))` >> gvs[pan_res_def] >>
    TRY (rename1 `_ = SOME res` >> Cases_on `res` >> gvs[pan_res_def]) >>
    first_x_assum drule >> simp[pan_prog_def])
  (* Return *)
  >- (
    rw[pan_prog_def, prog_ok_def] >> simp[Once evaluate_def, sem "PRet"] >>
    `mem_rel t s` by fs[state_rel_def] >> imp_res_tac dn_eval_thm >> simp[] >>
    Cases_on `dn_eval s e` >>
    gvs[pan_res_def, shape_of_def, size_of_sh_with_ctxt_def, empty_locals_def, dn_empty_locals_def] >>
    fs[state_rel_def, mem_rel_def, locals_rel_empty])
  (* StoreByte *)
  >- (
    rw[pan_prog_def, prog_ok_def] >> simp[Once evaluate_def, sem "PStoreByte"] >>
    `mem_rel t s` by fs[state_rel_def] >> imp_res_tac dn_eval_thm >> simp[] >>
    `t.memory = Word o s.memory /\ t.memaddrs = s.memaddrs /\ t.be = s.be` by fs[state_rel_def, mem_rel_def] >>
    Cases_on `dn_eval s dst` >> Cases_on `dn_eval s src` >> gvs[pan_res_def, dn_mem_store_byte_thm] >>
    rename1 `dn_eval s src = SOME w` >> rename1 `dn_eval s dst = SOME adr` >>
    Cases_on `dn_mem_store_byte s.memory s.memaddrs s.be adr (w2w w)` >> gvs[pan_res_def] >>
    fs[state_rel_def, mem_rel_def])
  (* DecCall *)
  >> (
    rw[pan_prog_def, prog_ok_def] >> simp[Once evaluate_def, sem "PDecCall"] >>
    `mem_rel t s` by fs[state_rel_def] >>
    drule_all args_thm >> strip_tac >> simp[] >>
    Cases_on `dn_eval_args s args` >> gvs[pan_res_def] >>
    `code_rel t.code s.code` by fs[state_rel_def] >>
    rename1 `dn_eval_args s args = SOME vs` >>
    Cases_on `dn_lookup_code s.code f vs` >> gvs[pan_res_def] >>
    TRY (imp_res_tac lookup_none >> gvs[pan_res_def] >> NO_TAC) >>
    rename1 `dn_lookup_code s.code f vs = SOME bp` >> PairCases_on `bp` >> gvs[] >>
    drule_all lookup_some >> strip_tac >> gvs[] >>
    `t.clock = s.clock` by fs[state_rel_def] >>
    Cases_on `s.clock = 0` >> gvs[pan_res_def] >>
    TRY (fs[state_rel_def, mem_rel_def, empty_locals_def, dn_empty_locals_def, locals_rel_empty] >> NO_TAC) >>
    qpat_x_assum `!t'. state_rel oracle t' (dn_dec_clock s with locals := bp1) ==> _`
    (qspec_then `dec_clock t with locals := nl` mp_tac) >>
    impl_tac >- fs[state_rel_def, mem_rel_def, dec_clock_def, dn_dec_clock_def] >>
    strip_tac >> simp[] >>
    imp_res_tac evaluate_clock >> fs[dec_clock_def] >>
    `(SND (dn_sem oracle bp0 (dn_dec_clock s with locals := bp1))).clock <= s.clock - 1` by fs[state_rel_def] >>
    gvs[clamp_id] >>
    Cases_on `FST (dn_sem oracle bp0 (dn_dec_clock s with locals := bp1))` >> gvs[pan_res_def, dn_call_ended_def] >>
    TRY (fs[state_rel_def] >> NO_TAC) >>
    rename1 `_ = SOME res` >> Cases_on `res` >> gvs[pan_res_def, dn_call_ended_def, shape_of_def] >>
    TRY (fs[state_rel_def, mem_rel_def, empty_locals_def, dn_empty_locals_def, locals_rel_empty] >> NO_TAC) >>
    rename1 `RReturn rv` >>
    qpat_x_assum `!t''. state_rel oracle t'' _ ==> _`
    (qspec_then `t' with locals := t.locals |+ (implode rt, ValWord rv)` mp_tac) >>
    impl_tac >- (fs[state_rel_def, mem_rel_def] >> irule locals_rel_update >> simp[]) >>
    strip_tac >> simp[set_var_def] >>
    fs[state_rel_def, mem_rel_def] >>
    `FLOOKUP t.locals (implode rt) = OPTION_MAP ValWord (s.locals rt)` by
    fs[locals_rel_def, mlstringTheory.explode_implode] >>
    simp[locals_rel_res_var])
QED


(* What the proofs rest on, asked of the prover: nothing but theorems read from theory files
   (DISK_THM, upstream's criterion in misc/preamble.sml), so no oracle and no cheat. *)
val _ =
  if List.all (fn th => let val tag = Thm.tag th in Tag.isEmpty tag orelse Tag.isDisk tag end)
       [dn_sem_thm, dn_eval_thm, dn_set_byte_thm, dn_mem_store_byte_thm]
  then print "DN SEMANTICS: dn_sem_thm and dn_eval_thm carry no oracle\n"
  else raise Fail "an oracle in the proofs of dnModelProof";
