Require Import Real Base MachineWord ConcurrencyInterfaceTypesV2 ConcurrencyInterfaceV2.
From stdpp Require Import bitvector.definitions.

Import ListNotations.
Open Scope string.
Open Scope bool.
Open Scope Z.

Module Defs (A : Arch) (I : InterfaceT A).

Definition monad E := I.iMon (fun _ => E).
Definition returnm {A E} : A -> monad E A := I.Ret.

Definition monadR R E := I.iMon (fun _ => (R + E)%type).
Definition returnR {A E} R : A -> monadR R E A := I.Ret.

Definition bind {A B E : Type} (m : monad E A) (f : A -> monad E B) : monad E B := I.iMon_bind m f.
#[warnings="-notation-overridden"]
Notation "m >>= f" := (bind m f) (at level 50, left associativity).
Definition bind0 {A E} (m : monad E unit) (n : monad E A) :=
  m >>= fun (_ : unit) => n.
#[warnings="-notation-overridden"]
Notation "m >> n" := (bind0 m n) (at level 50, left associativity).

Definition fail {A E} (msg : string) : monad E A :=
  I.Next (I.GenericFail msg) (fun f => match f with end).

Definition exit {A E} (_ : unit) : monad E A := fail "exit".

Definition choose_bool {E} (_descr : string) : monad E bool := I.Next (I.Choose ChooseBool) mret.
Definition choose_int {E} (_descr : string) : monad E Z := I.Next (I.Choose ChooseInt) mret.
Definition choose_nat {E} (_descr : string) : monad E Z := I.Next (I.Choose ChooseNat) mret.
Definition choose_real {E} (_descr : string) : monad E R := I.Next (I.Choose ChooseReal) mret.
Definition choose_string {E} (_descr : string) : monad E string := I.Next (I.Choose ChooseString) mret.
Definition choose_range {E} (_descr : string) (lo hi : Z) : monad E Z := I.Next (I.Choose (ChooseRange lo hi)) mret.
Definition choose_bitvector {E} (_descr : string) (n : Z) : monad E (mword n) :=
  I.Next (I.Choose (ChooseBitvector n)) mret.

Definition assert_exp {E} (exp :bool) msg : monad E unit :=
 if exp then returnm tt else fail msg.
Definition assert_exp' {E} (exp :bool) msg : monad E (exp = true) :=
 if exp return monad E (exp = true) then returnm eq_refl else fail msg.

Definition throw {A E} (e : E) : monad E A := I.Next (I.ExtraOutcome e) mret.

Fixpoint try_catch {A E1 E2} (m : monad E1 A) (h : E1 -> monad E2 A) : monad E2 A :=
  match m with
  | I.Ret r => I.Ret r
  | I.Next (I.ExtraOutcome e)                  _ => h e
  | I.Next (I.RegRead reg direct)              f => I.Next (I.RegRead reg direct) (fun t => try_catch (f t) h)
  | I.Next (I.RegWrite reg direct regval)      f => I.Next (I.RegWrite reg direct regval) (fun t => try_catch (f t) h)
  | I.Next (I.MemRead mr)                      f => I.Next (I.MemRead mr) (fun t => try_catch (f t) h)
  | I.Next (I.MemWrite mr value tags)          f => I.Next (I.MemWrite mr value tags) (fun t => try_catch (f t) h)
  | I.Next (I.MemAddressAnnounce mr)           f => I.Next (I.MemAddressAnnounce mr) (fun t => try_catch (f t) h)
  | I.Next (I.InstrAnnounce opcode)            f => I.Next (I.InstrAnnounce opcode) (fun t => try_catch (f t) h)
  | I.Next (I.BranchAnnounce sz pa)            f => I.Next (I.BranchAnnounce sz pa) (fun t => try_catch (f t) h)
  | I.Next (I.Barrier barrier)                 f => I.Next (I.Barrier barrier) (fun t => try_catch (f t) h)
  | I.Next (I.CacheOp op)                      f => I.Next (I.CacheOp op) (fun t => try_catch (f t) h)
  | I.Next (I.TlbOp op)                        f => I.Next (I.TlbOp op) (fun t => try_catch (f t) h)
  | I.Next (I.TakeException fault)             f => I.Next (I.TakeException fault) (fun t => try_catch (f t) h)
  | I.Next  I.ReturnException                  f => I.Next  I.ReturnException (fun t => try_catch (f t) h)
  | I.Next (I.TranslationStart ts)             f => I.Next (I.TranslationStart ts) (fun t => try_catch (f t) h)
  | I.Next (I.TranslationEnd te)               f => I.Next (I.TranslationEnd te) (fun t => try_catch (f t) h)
  | I.Next (I.GenericFail msg)                 f => I.Next (I.GenericFail msg) (fun t => try_catch (f t) h)
  | I.Next  I.CycleCount                       f => I.Next  I.CycleCount (fun t => try_catch (f t) h)
  | I.Next  I.GetCycleCount                    f => I.Next  I.GetCycleCount (fun t => try_catch (f t) h)
  | I.Next (I.Choose n)                        f => I.Next (I.Choose n) (fun t => try_catch (f t) h)
  | I.Next (I.Discard)                         f => I.Next (I.Discard) (fun t => try_catch (f t) h)
  | I.Next (I.Message msg)                     f => I.Next (I.Message msg) (fun t => try_catch (f t) h)
  end.

Definition early_return {A R E} (r : R) : monadR R E A := throw (inl r).
Definition catch_early_return {A E} (m : monadR A E A) : monad E A :=
  try_catch m
    (fun r => match r with
      | inl a => returnm a
      | inr e => throw e
     end).

Definition pure_early_return_bind {A B E} (v : E + A) (f : A -> E + B) : E + B :=
  match v with
  | inl e => inl e
  | inr a => f a
  end.

#[warnings="-notation-overridden"]
Notation "m >>$= f" := (pure_early_return_bind m f) (at level 50, left associativity).
#[warnings="-notation-overridden"]
Notation "m >>$ n" := (m >>$= fun _ => n) (at level 50, left associativity).

Definition pure_early_return {A} (v : A + A) : A :=
  match v with
  | inl v' => v'
  | inr v' => v'
  end.

(* Lift to monad with early return by wrapping exceptions *)
Definition liftR {A R E} (m : monad E A) : monadR R E A :=
 try_catch m (fun e => throw (inr e)).

Definition pure_early_return_embed {A R E} (v : R + A) : monadR R E A :=
  match v with
  | inl v' => early_return v'
  | inr v' => returnm v'
  end.

(* Catch exceptions in the presence : early returns *)
Definition try_catchR {A R E} (m : monadR R E A) (h : E -> monadR R E A) :=
  try_catch m
    (fun r => match r with
      | inl r => throw (inl r)
      | inr e => h e
     end).


(* Helper for value definitions that may contain an assertion or incomplete pattern match.  If the
   computation reduces immediately to a value it will return that, otherwise there will be a
   typechecking failure. *)
Definition unwrap_value {A E} (m : monad E A) : match m with I.Ret _ => A | I.Next _ _ => True end :=
  match m with
  | I.Ret a => a
  | I.Next _ _ => I
  end.


Section Undef.

Definition undefined_unit {E} (_:unit) : monad E unit := returnm tt.
Definition undefined_bool {E} (_:unit) : monad E bool := choose_bool "undefined_bool".
Definition undefined_string {E} (_:unit) : monad E string := choose_string "undefined_string".
 Definition undefined_int {E} (_:unit) : monad E Z := choose_int "undefined_int".
Definition undefined_nat {E} (_:unit) : monad E Z := choose_nat "undefined_nat".
Definition undefined_real {E} (_:unit) : monad E _ := choose_real "undefined_real".
Definition undefined_range {E} i j : monad E Z := choose_range "undefined_range" i j.
Definition undefined_bitvector {E} n : monad E (mword n) := choose_bitvector "undefined_bitvector" n.

Definition undefined_vector {E T} n `{Inhabited T} (a:T) : monad E (vec T n) := returnm (vector_init n a).

End Undef.

(* ---- Prompt_monad *)

Definition read_reg {e} (reg : A.reg) : monad e (A.reg_type reg) :=
  let k v := I.Ret v in
  I.Next (I.RegRead reg None) k.

Definition read_reg_ref {a e} (ref : @register_ref A.reg A.reg_type a) : monad e a :=
  let k v := I.Ret (ref.(to_ty) v) in
  I.Next (I.RegRead ref.(reg) None) k.

Definition reg_deref {a e} := @read_reg_ref a e.

Definition write_reg {e} (reg : A.reg) (v : A.reg_type reg) : monad e unit :=
 I.Next (I.RegWrite reg None v) I.Ret.

Definition write_reg_ref {a e} (ref : @register_ref A.reg A.reg_type a) (v : a) : monad e unit :=
 I.Next (I.RegWrite ref.(reg) None (ref.(from_ty) v)) I.Ret.

(* ---- Prompt *)

Fixpoint foreachM {a e Vars} (l : list a) (vars : Vars) (body : a -> Vars -> monad e Vars) : monad e Vars :=
match l with
| [] => returnm vars
| (x :: xs) =>
  body x vars >>= fun vars =>
  foreachM xs vars body
end.

Fixpoint foreachE {a Vars e} (l : list a) (vars : Vars) (body : a -> Vars -> e + Vars) : e + Vars :=
match l with
| [] => inr vars
| (x :: xs) =>
  body x vars >>$= fun vars =>
  foreachE xs vars body
end.

Fixpoint foreach_ZM_up' {E Vars} (from to step : Z) (n : nat) (vars : Vars) (body : forall (z : Z), Vars -> monad E Vars) {struct n} : monad E Vars :=
  if from <=? to then
    match n with
    | O => returnm vars
    | S n => body from vars >>= fun vars => foreach_ZM_up' (from + step) to step n vars body
    end
  else returnm vars.

Lemma unroll_foreach_ZM_up' E Vars from to step n vars body:
  from <= to ->
  @foreach_ZM_up' E Vars from to step (S n) vars body =
  body from vars >>= fun vars' => @foreach_ZM_up' E Vars (from + step) to step n vars' body.
Proof.
  intro Range.
  unfold foreach_ZM_up' at 1.
  replace (from <=? to) with true by lia.
  fold (@foreach_ZM_up' E Vars).
  reflexivity.
Qed.

Fixpoint foreach_ZE_up' {e Vars} (from to step : Z) (n : nat) (* 0 <? step *) (vars : Vars) (body : forall (z : Z) (* from <=? z <=? to *), Vars -> e + Vars) {struct n} : e + Vars :=
  if from <=? to then
    match n with
    | O => inr vars
    | S n => body from vars >>$= fun vars => foreach_ZE_up' (from + step) to step n vars body
    end
  else inr vars.

Lemma unroll_foreach_ZE_up' E Vars from to step n vars body:
  from <= to ->
  @foreach_ZE_up' E Vars from to step (S n) vars body =
  body from vars >>$= fun vars' => @foreach_ZE_up' E Vars (from + step) to step n vars' body.
Proof.
  intro Range.
  unfold foreach_ZE_up' at 1.
  replace (from <=? to) with true by lia.
  fold (@foreach_ZE_up' E Vars).
  reflexivity.
Qed.

Fixpoint foreach_ZM_down' {E Vars} (from to step : Z) (n : nat) (* 0 <? step *) (vars : Vars) (body : forall (z : Z) (* to <=? z <=? from *), Vars -> monad E Vars) {struct n} : monad E Vars :=
  if to <=? from then
    match n with
    | O => returnm vars
    | S n => body from vars >>= fun vars => foreach_ZM_down' (from - step) to step n vars body
    end
  else returnm vars.

Lemma unroll_foreach_ZM_down' E Vars from to step n vars body:
  to <= from ->
  @foreach_ZM_down' E Vars from to step (S n) vars body =
  body from vars >>= fun vars' => @foreach_ZM_down' E Vars (from - step) to step n vars' body.
Proof.
  intro Range.
  unfold foreach_ZM_down' at 1.
  replace (to <=? from) with true by lia.
  fold (@foreach_ZM_down' E Vars).
  reflexivity.
Qed.

Fixpoint foreach_ZE_down' {e Vars} (from to step : Z) (n : nat) (* 0 <? step *) (vars : Vars) (body : forall (z : Z) (* to <=? z <=? from *), Vars -> e + Vars) {struct n} : e + Vars :=
  if to <=? from then
    match n with
    | O => inr vars
    | S n => body from vars >>$= fun vars => foreach_ZE_down' (from - step) to step n vars body
    end
  else inr vars.

Lemma unroll_foreach_ZE_down' E Vars from to step n vars body:
  to <= from ->
  @foreach_ZE_down' E Vars from to step (S n) vars body =
  body from vars >>$= fun vars' => @foreach_ZE_down' E Vars (from - step) to step n vars' body.
Proof.
  intro Range.
  unfold foreach_ZE_down' at 1.
  replace (to <=? from) with true by lia.
  fold (@foreach_ZE_down' E Vars).
  reflexivity.
Qed.


Definition foreach_ZM_up {E Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZM_up' (E := E) (Vars := Vars) from to step (S (Z.abs_nat (from - to))) vars body.

Definition foreach_ZM_down {E Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZM_down' (E := E) (Vars := Vars) from to step (S (Z.abs_nat (from - to))) vars body.

Definition foreach_ZE_up {e Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZE_up' (e := e) (Vars := Vars) from to step (S (Z.abs_nat (from - to))) vars body.
Definition foreach_ZE_down {e Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZE_down' (e := e) (Vars := Vars) from to step (S (Z.abs_nat (from - to))) vars body.

Definition genlistM {A E} (f : nat -> monad E A) (n : nat) : monad E (list A) :=
  let indices := List.seq 0 n in
  foreachM indices [] (fun n xs => (f n >>= (fun x => returnm (xs ++ [x])%list))).

Definition and_boolM {E} (l : monad E bool) (r : monad E bool) : monad E bool :=
 l >>= (fun l => if l then r else returnm false).

Definition or_boolM {E} (l : monad E bool) (r : monad E bool) : monad E bool :=
 l >>= (fun l => if l then returnm true else r).


(* For termination of recursive functions. *)
Definition _limit_reduces {_limit} (_acc:Acc (Zwf 0) _limit) (H : _limit >= 0) : Acc (Zwf 0) (_limit - 1).
refine (Acc_inv _acc _).
unbool_comparisons.
red.
Lia.lia.
Defined.

(* A version of well-foundedness of measures with a guard to ensure that
   definitions can be reduced without inspecting proofs, based on a coq-club
   thread featuring Barras, Gonthier and Gregoire, see
     https://sympa.inria.fr/sympa/arc/coq-club/2007-07/msg00014.html *)

Fixpoint pos_guard_wf {A:Type} {R:A -> A -> Prop} (p:positive) : well_founded R -> well_founded R :=
 match p with
 | xH => fun wfR x => Acc_intro x (fun y _ => wfR y)
 | xO p' => fun wfR x => let F := pos_guard_wf p' in Acc_intro x (fun y _ => F (F 
wfR) y)
 | xI p' => fun wfR x => let F := pos_guard_wf p' in Acc_intro x (fun y _ => F (F 
wfR) y)
 end.

Definition Zwf_guarded (z:Z) : Acc (Zwf 0) z :=
  Acc_intro _ (fun y H => match z with
  | Zpos p => pos_guard_wf p (Zwf_well_founded _) _
  | Zneg p => pos_guard_wf p (Zwf_well_founded _) _
  | Z0 => Zwf_well_founded _ _
  end).

(*val whileM : forall 'rv 'vars 'e. 'vars -> ('vars -> monad 'rv bool 'e) ->
                ('vars -> monad 'rv 'vars 'e) -> monad 'rv 'vars 'e*)
Fixpoint whileMT' {E Vars} limit (vars : Vars) (cond : Vars -> monad E bool) (body : Vars -> monad E Vars) (acc : Acc (Zwf 0) limit) : monad E Vars.
exact (
  if Z_ge_dec limit 0 then
    cond vars >>= fun cond_val =>
    if cond_val then
      body vars >>= fun vars => whileMT' _ _ (limit - 1) vars cond body (_limit_reduces acc ltac:(assumption))
    else returnm vars
  else fail "Termination limit reached").
Defined.

Definition whileMT {E Vars} (vars : Vars) (measure : Vars -> Z) (cond : Vars -> monad E bool) (body : Vars -> monad E Vars) : monad E Vars :=
  let limit := measure vars in
  whileMT' limit vars cond body (Zwf_guarded limit).

Fixpoint untilMT' {E Vars} limit (vars : Vars) (cond : Vars -> monad E bool) (body : Vars -> monad E Vars) (acc : Acc (Zwf 0) limit) : monad E Vars.
exact (
  if Z_ge_dec limit 0 then
    body vars >>= fun vars =>
    cond vars >>= fun cond_val =>
    if cond_val then returnm vars else untilMT' _ _ (limit - 1) vars cond body (_limit_reduces acc ltac:(assumption))
  else fail "Termination limit reached").
Defined.

Definition untilMT {E Vars} (vars : Vars) (measure : Vars -> Z) (cond : Vars -> monad E bool) (body : Vars -> monad E Vars) : monad E Vars :=
  let limit := measure vars in
  untilMT' limit vars cond body (Zwf_guarded limit).

Section Choose.

Definition choose_from_list {A E} (descr : string) (xs : list A) : monad E A :=
  (* Use sufficiently many nondeterministically chosen bits and convert into an
     index into the list *)
  choose_range descr 0 (Z.of_nat (List.length xs) - 1) >>= fun idx =>
  match List.nth_error xs (Z.to_nat idx) with
    | Some x => returnm x
    | None => fail ("choose " ++ descr)
  end.

Definition internal_pick {a e} (xs : list a) : monad e a :=
  choose_from_list "internal_pick" xs.

End Choose.

(* --- Operators_mwords.v *)

Definition autocast_m {e m n} {T : Z -> Type} `{H : Inhabited (T n)} (x : monad e (T m)) : monad e (T n) :=
  x >>= fun x => returnm (autocast x).

(* --- should probably define generic versions of these, parametrised by Arch *)

Definition sail_barrier {e} (b : A.barrier) : monad e unit :=
  I.Next (I.Barrier b) I.Ret.

Definition sail_take_exception {e} (f : A.exn) : monad e unit :=
  I.Next (I.TakeException f) I.Ret.

Definition sail_return_exception {e} (_:unit) : monad e unit :=
  I.Next I.ReturnException I.Ret.

Definition sail_cache_op {e} (op : A.cache_op) : monad e unit :=
  I.Next (I.CacheOp op) I.Ret.

Definition sail_tlbi {e} (op : A.tlbi) : monad e unit :=
  I.Next (I.TlbOp op) I.Ret.

Definition branch_announce {e} sz (addr : mword sz) : monad e unit :=
  (* TODO: branch_announce seems rather odd *)
  I.Next (I.BranchAnnounce sz addr) I.Ret.

Definition instr_announce {e sz} (opcode : mword sz) : monad e unit :=
  I.Next (I.InstrAnnounce (bv_to_bvn (get_word opcode))) I.Ret.

Definition cycle_count {e} (_ : unit) : monad e unit := I.Next I.CycleCount I.Ret.
Definition get_cycle_count {e} (_ : unit) : monad e Z := I.Next I.GetCycleCount I.Ret.

(* TODO: check endianness *)
Definition bytes_of_bv {n} (v : bv (8 * Z.to_N n)) : vec (bv 8) n :=
  vec_init_fn n (fun i => bv_extract (8 * Z.to_N i) 8 v).

Definition bools_of_bv {n} (v : bv (Z.to_N n)) : vec bool n :=
  vec_init_fn n (fun i => MachineWord.MachineWord.get_bit v (Z.to_N i)).

Definition sail_mem_read {e n nt} (req : Mem_request n nt (Z.of_N A.addr_size) A.addr_space A.mem_acc) : monad e (result (vec (mword 8) n * vec bool nt) A.abort) :=
  let n' := Z.to_N n in
  let nt' := Z.to_N nt in
  let address := cast_N req.(Mem_request_address) (N2Z.id _) in
  let req' := I.MemReq.make req.(Mem_request_access_kind) address req.(Mem_request_address_space) n' nt' in
  let k r :=
    match r with
    | inl (x,y) =>
        I.Ret (Ok (bytes_of_bv x, bools_of_bv y))
    | inr abort => I.Ret (Err abort)
    end
  in
  I.Next (I.MemRead req') k.

Definition bv_of_bytes {n} (v : vec (bv 8) n) : bv (8 * Z.to_N n).
refine (
  cast_N (list_rec (fun l => bv (8 * N.of_nat (length l))) (bv_0 0) (fun v _ t => bv_concat _ v t) (projT1 v)) _
).
destruct v as [l H].
simpl.
rewrite H.
rewrite Z_nat_N.
reflexivity.
Defined.

Local Lemma bv_of_bools_size n (v : vec bool n) : MachineWord.nat_idx (length (projT1 v)) = Z.to_N n.
Proof.
  destruct v as [l H].
  simpl.
  rewrite H.
  lia.
Qed.

Definition bv_of_bools {n} (v : vec bool n) : bv (Z.to_N n) := cast_N (MachineWord.bools_to_word (projT1 v)) (bv_of_bools_size _ _).

Definition sail_mem_write {e n nt} (req : Mem_request n nt (Z.of_N A.addr_size) A.addr_space A.mem_acc) (value_bytes : vec (mword 8) n) (tags_vec : vec bool nt) : monad e (result unit A.abort) :=
  let n' := Z.to_N n in
  let nt' := Z.to_N nt in
  let value := bv_of_bytes value_bytes in
  let address := cast_N req.(Mem_request_address) (N2Z.id _) in
  let address_space := req.(Mem_request_address_space) in
  let tags := bv_of_bools tags_vec in
  let access_kind := req.(Mem_request_access_kind) in
  let req' := I.MemReq.make access_kind address address_space n' nt' in
  let k x :=
    match x with
    | inl _ => I.Ret (Ok tt)
    | inr y => I.Ret (Err y)
    end
  in
  I.Next (I.MemWrite req' value tags) k.

Definition sail_mem_address_announce {e n nt} (ann : Mem_request n nt (Z.of_N A.addr_size) A.addr_space A.mem_acc) : monad e unit :=
  let n' := Z.to_N n in
  let nt' := Z.to_N nt in
  let address := cast_N ann.(Mem_request_address) (N2Z.id _) in
  let address_space := ann.(Mem_request_address_space) in
  let access_kind := ann.(Mem_request_access_kind) in
  let ann' := I.MemReq.make access_kind address address_space n' nt' in
  I.Next (I.MemAddressAnnounce ann') I.Ret.

Definition sail_sys_reg_read {a e} (id : A.sys_reg_id) (r : @register_ref A.reg A.reg_type a) : monad e a :=
  I.Next (I.RegRead r.(Values.reg) (Some id)) (fun v => I.Ret (r.(to_ty) v)).

Definition sail_sys_reg_write {a e} (id : A.sys_reg_id) (r : @register_ref A.reg A.reg_type a) (v : a) : monad e unit :=
  I.Next (I.RegWrite r.(Values.reg) (Some id) (r.(from_ty) v)) I.Ret.

Definition sail_translation_start {e} (ts : A.trans_start) : monad e unit := I.Next (I.TranslationStart ts) I.Ret.
Definition sail_translation_end {e} (te : A.trans_end) : monad e unit := I.Next (I.TranslationEnd te) I.Ret.

(* ----------- *)
(* The normal print routines do nothing in Coq so that they don't drag terms and functions into the
   monad.  Here are alternative versions which do, which can be controlled by defining PRINT_EFFECTS
   in Sail. *)
Definition print_effect {e} (s : string) : monad e unit :=
  I.Next (I.Message s) I.Ret.

Definition print_endline_effect {e} (s : string) : monad e unit :=
  print_effect (s ++ "
")%string.

Definition print_int_effect {e} s i : monad e unit :=
  print_endline_effect (s ++ string_of_int i).

Definition print_bits_effect {e n} s (w : mword n) : monad e unit :=
  print_endline_effect (s ++ string_of_bits w).

(* We only have one output stream that we use for both. *)
Definition prerr_effect {e} s := @print_effect e s.
Definition prerr_endline_effect {e} s := @print_endline_effect e s.
Definition prerr_int_effect {e} s i := @print_int_effect e s i.
Definition prerr_bits_effect {e} s i := @print_bits_effect e s i.

End Defs.
