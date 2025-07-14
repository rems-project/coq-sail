Require Import Real Base ConcurrencyInterfaceTypes ConcurrencyInterface.
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
Definition choose_bit {E} (_descr : string) : monad E bitU := I.Next (I.Choose ChooseBit) mret.
Definition choose_int {E} (_descr : string) : monad E Z := I.Next (I.Choose ChooseInt) mret.
Definition choose_nat {E} (_descr : string) : monad E Z := I.Next (I.Choose ChooseNat) mret.
Definition choose_real {E} (_descr : string) : monad E R := I.Next (I.Choose ChooseReal) mret.
Definition choose_string {E} (_descr : string) : monad E string := I.Next (I.Choose ChooseString) mret.
Definition choose_range {E} (_descr : string) (lo hi : Z) : monad E Z := I.Next (I.Choose (ChooseRange lo hi)) mret.
Definition choose_bitvector {E} (_descr : string) (n : Z) : monad E (mword n) :=
  I.Next (I.Choose (ChooseBitvector n)) mret.
(* match n return monad (mword n) E with
 | Zneg _ => returnm (bv_0 0)
 | Z0 => returnm (bv_0 0)
 | Zpos p => I.Next (I.Choose (N.of_nat (Pos.to_nat p))) (fun bv => returnm bv)
 end.*)

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
  | I.Next (I.MemRead n req)                   f => I.Next (I.MemRead n req) (fun t => try_catch (f t) h)
  | I.Next (I.MemWrite n req)                  f => I.Next (I.MemWrite n req) (fun t => try_catch (f t) h)
  | I.Next (I.InstrAnnounce opcode)            f => I.Next (I.InstrAnnounce opcode) (fun t => try_catch (f t) h)
  | I.Next (I.BranchAnnounce sz pa)            f => I.Next (I.BranchAnnounce sz pa) (fun t => try_catch (f t) h)
  | I.Next (I.Barrier barrier)                 f => I.Next (I.Barrier barrier) (fun t => try_catch (f t) h)
  | I.Next (I.CacheOp op)                      f => I.Next (I.CacheOp op) (fun t => try_catch (f t) h)
  | I.Next (I.TlbOp op)                        f => I.Next (I.TlbOp op) (fun t => try_catch (f t) h)
  | I.Next (I.TakeException fault)             f => I.Next (I.TakeException fault) (fun t => try_catch (f t) h)
  | I.Next (I.ReturnException pa)              f => I.Next (I.ReturnException pa) (fun t => try_catch (f t) h)
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
Definition undefined_bit {E} (_:unit) : monad E bitU := choose_bool "undefined_bit" >>= fun b => returnm (bitU_of_bool b).
Definition undefined_string {E} (_:unit) : monad E string := choose_string "undefined_string".
 Definition undefined_int {E} (_:unit) : monad E Z := choose_int "undefined_int".
Definition undefined_nat {E} (_:unit) : monad E Z := choose_nat "undefined_nat".
Definition undefined_real {E} (_:unit) : monad E _ := choose_real "undefined_real".
Definition undefined_range {E} i j : monad E Z := choose_range "undefined_range" i j.
Definition undefined_bitvector {E} n : monad E (mword n) := choose_bitvector "undefined_bitvector" n.

Definition undefined_vector {E T} n `{Inhabited T} (a:T) : monad E (vec T n) := returnm (vector_init n a).

End Undef.

(* ---- Prompt_monad *)

Definition read_reg {a e} (reg : A.reg a) : monad e a :=
  let k v := I.Ret v in
  I.Next (I.RegRead reg None) k.

Definition read_reg_ref {a e} (ref : register_ref A.reg a) : monad e a :=
  let k v := I.Ret v in
  I.Next (I.RegRead ref.(Values.reg) None) k.

Definition reg_deref {a e} := @read_reg_ref a e.

Definition write_reg {a e} (reg : A.reg a) (v : a) : monad e unit :=
 I.Next (I.RegWrite reg None v) I.Ret.

Definition write_reg_ref {a e} (ref : register_ref A.reg a) (v : a) : monad e unit :=
 I.Next (I.RegWrite ref.(Values.reg) None v) I.Ret.

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

Fixpoint foreach_ZM_up' {E Vars} (from to step off : Z) (n : nat) (* 0 <? step *) (* 0 <=? off *) (vars : Vars) (body : forall (z : Z) (* from <=? z <=? to *), Vars -> monad E Vars) {struct n} : monad E Vars :=
  if sumbool_of_bool (from + off <=? to) then
    match n with
    | O => returnm vars
    | S n => body (from + off) vars >>= fun vars => foreach_ZM_up' from to step (off + step) n vars body
    end
  else returnm vars.

Fixpoint foreach_ZE_up' {e Vars} (from to step off : Z) (n : nat) (* 0 <? step *) (* 0 <=? off *) (vars : Vars) (body : forall (z : Z) (* from <=? z <=? to *), Vars -> e + Vars) {struct n} : e + Vars :=
  if sumbool_of_bool (from + off <=? to) then
    match n with
    | O => inr vars
    | S n => body (from + off) vars >>$= fun vars => foreach_ZE_up' from to step (off + step) n vars body
    end
  else inr vars.

Fixpoint foreach_ZM_down' {E Vars} (from to step off : Z) (n : nat) (* 0 <? step *) (* off <=? 0 *) (vars : Vars) (body : forall (z : Z) (* to <=? z <=? from *), Vars -> monad E Vars) {struct n} : monad E Vars :=
  if sumbool_of_bool (to <=? from + off) then
    match n with
    | O => returnm vars
    | S n => body (from + off) vars >>= fun vars => foreach_ZM_down' from to step (off - step) n vars body
    end
  else returnm vars.

Fixpoint foreach_ZE_down' {e Vars} (from to step off : Z) (n : nat) (* 0 <? step *) (* off <=? 0 *) (vars : Vars) (body : forall (z : Z) (* to <=? z <=? from *), Vars -> e + Vars) {struct n} : e + Vars :=
  if sumbool_of_bool (to <=? from + off) then
    match n with
    | O => inr vars
    | S n => body (from + off) vars >>$= fun vars => foreach_ZE_down' from to step (off - step) n vars body
    end
  else inr vars.

Definition foreach_ZM_up {E Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZM_up' (E := E) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.
Definition foreach_ZM_down {E Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZM_down' (E := E) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.

Definition foreach_ZE_up {e Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZE_up' (e := e) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.
Definition foreach_ZE_down {e Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZE_down' (e := e) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.

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

Definition sail_take_exception {e} (f : A.fault) : monad e unit :=
  I.Next (I.TakeException f) I.Ret.

Definition sail_return_exception {e} pa : monad e unit :=
  I.Next (I.ReturnException pa) I.Ret.

Definition sail_cache_op {e} (op : A.cache_op) : monad e unit :=
  I.Next (I.CacheOp op) I.Ret.

Definition sail_tlbi {e} (op : A.tlb_op) : monad e unit :=
  I.Next (I.TlbOp op) I.Ret.

Definition branch_announce {e} sz (addr : mword sz) : monad e unit :=
  (* TODO: branch_announce seems rather odd *)
  I.Next (I.BranchAnnounce sz addr) I.Ret.

Definition instr_announce {e sz} (opcode : mword sz) : monad e unit :=
  I.Next (I.InstrAnnounce (bv_to_bvn (get_word opcode))) I.Ret.

Definition cycle_count {e} (_ : unit) : monad e unit := I.Next I.CycleCount I.Ret.
Definition get_cycle_count {e} (_ : unit) : monad e Z := I.Next I.GetCycleCount I.Ret.

Definition sail_mem_read {e n} (req : Mem_read_request n (Z.of_N A.va_size) A.pa A.translation A.arch_ak) : monad e (result (mword (8 * n) * option bool) A.abort).
refine (
  let n' := Z.to_N n in
  let va : option (bv A.va_size) :=
    match req.(Mem_read_request_va) with
    | None => None
    | Some va =>
        Some (match A.va_size as x return mword (Z.of_N x) -> bv x with
        | N0 => fun y => y
        | Npos _ => fun y => cast_N y _
        end va)
    end
  in
  let req' := I.ReadReq.make n' req.(Mem_read_request_pa) req.(Mem_read_request_access_kind) va req.(Mem_read_request_translation) req.(Mem_read_request_tag) in
  let k r :=
    match r with
    | inl (x,y) =>
        let x' := cast_N (m := 8 * Z.to_N n) (n := (Z.to_N (8 * n))) x _ in
        I.Ret (Ok (x', y))
    | inr abort => I.Ret (Err abort)
    end
  in
  I.Next (I.MemRead n' req') k
).
clear; abstract Lia.lia.
Unshelve.
reflexivity.
Defined.

Definition sail_mem_write {e n} (req : Mem_write_request n (Z.of_N A.va_size) A.pa A.translation A.arch_ak) : monad e (result (option bool) A.abort).
refine (
  let n' := Z.to_N n in
  match req.(Mem_write_request_value) with
  | None => I.Ret (Ok None) (* TODO: ought to support tag-only writes *)
  | Some value =>
      let va : option (bv A.va_size) :=
        match req.(Mem_write_request_va) with
        | None => None
        | Some va =>
            Some (match A.va_size as x return mword (Z.of_N x) -> bv x with
                  | N0 => fun y => y
                  | Npos _ => fun y => cast_N y _
                  end va)
        end
      in
      let value := cast_N value _ in
      let pa := req.(Mem_write_request_pa) in
      let tag := req.(Mem_write_request_tag) in
      let access_kind := req.(Mem_write_request_access_kind) in
      let translation := req.(Mem_write_request_translation) in
      let req' := I.WriteReq.make n' pa access_kind value va translation tag in
      let k x :=
        match x with
        | inl y => I.Ret (Ok y)
        | inr y => I.Ret (Err y)
        end
      in
      I.Next (I.MemWrite n' req') k
  end
).
clear; abstract (unfold MachineWord.MachineWord.Z_idx; Lia.lia).
Unshelve.
reflexivity.
Defined.

Definition sail_sys_reg_read {e T} (id : A.sys_reg_id) (r : register_ref A.reg T) : monad e T :=
  I.Next (I.RegRead r.(Values.reg) (Some id)) I.Ret.

Definition sail_sys_reg_write {e T} (id : A.sys_reg_id) (r : register_ref A.reg T) (v : T) : monad e unit :=
  I.Next (I.RegWrite r.(Values.reg) (Some id) v) I.Ret.

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
