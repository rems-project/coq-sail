(*==========================================================================*)
(*     Sail                                                                 *)
(*                                                                          *)
(*  Sail and the Sail architecture models here, comprising all files and    *)
(*  directories except the ASL-derived Sail code in the aarch64 directory,  *)
(*  are subject to the BSD two-clause licence below.                        *)
(*                                                                          *)
(*  The ASL derived parts of the ARMv8.3 specification in                   *)
(*  aarch64/no_vector and aarch64/full are copyright ARM Ltd.               *)
(*                                                                          *)
(*  Copyright (c) 2013-2021                                                 *)
(*    Kathyrn Gray                                                          *)
(*    Shaked Flur                                                           *)
(*    Stephen Kell                                                          *)
(*    Gabriel Kerneis                                                       *)
(*    Robert Norton-Wright                                                  *)
(*    Christopher Pulte                                                     *)
(*    Peter Sewell                                                          *)
(*    Alasdair Armstrong                                                    *)
(*    Brian Campbell                                                        *)
(*    Thomas Bauereiss                                                      *)
(*    Anthony Fox                                                           *)
(*    Jon French                                                            *)
(*    Dominic Mulligan                                                      *)
(*    Stephen Kell                                                          *)
(*    Mark Wassell                                                          *)
(*    Alastair Reid (Arm Ltd)                                               *)
(*                                                                          *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  This work was partially supported by EPSRC grant EP/K008528/1 <a        *)
(*  href="http://www.cl.cam.ac.uk/users/pes20/rems">REMS: Rigorous          *)
(*  Engineering for Mainstream Systems</a>, an ARM iCASE award, EPSRC IAA   *)
(*  KTF funding, and donations from Arm.  This project has received         *)
(*  funding from the European Research Council (ERC) under the European     *)
(*  Union’s Horizon 2020 research and innovation programme (grant           *)
(*  agreement No 789108, ELVER).                                            *)
(*                                                                          *)
(*  This software was developed by SRI International and the University of  *)
(*  Cambridge Computer Laboratory (Department of Computer Science and       *)
(*  Technology) under DARPA/AFRL contracts FA8650-18-C-7809 ("CIFV")        *)
(*  and FA8750-10-C-0237 ("CTSRD").                                         *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*     notice, this list of conditions and the following disclaimer.        *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*     notice, this list of conditions and the following disclaimer in      *)
(*     the documentation and/or other materials provided with the           *)
(*     distribution.                                                        *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS''      *)
(*  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED       *)
(*  TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A         *)
(*  PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR     *)
(*  CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,            *)
(*  SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT        *)
(*  LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF        *)
(*  USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND     *)
(*  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,      *)
(*  OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT      *)
(*  OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF      *)
(*  SUCH DAMAGE.                                                            *)
(*==========================================================================*)

Require Import Values Instances String Prompt_monad.
From Coq Require Export ZArith.Zwf.
From Coq Require Import Lia List.
Import ListNotations.
Local Open Scope Z.

Section WithRegisterType.
Context {register : Type} {reg_to_type : register -> Type}.

Let monad := @monad register reg_to_type.

(*

val iter_aux : forall 'rv 'a 'e. integer -> (integer -> 'a -> monad 'rv unit 'e) -> list 'a -> monad 'rv unit 'e
let rec iter_aux i f xs = match xs with
  | x :: xs -> f i x >> iter_aux (i + 1) f xs
  | [] -> return ()
  end

declare {isabelle} termination_argument iter_aux = automatic

val iteri : forall 'rv 'a 'e. (integer -> 'a -> monad 'rv unit 'e) -> list 'a -> monad 'rv unit 'e
let iteri f xs = iter_aux 0 f xs

val iter : forall 'rv 'a 'e. ('a -> monad 'rv unit 'e) -> list 'a -> monad 'rv unit 'e
let iter f xs = iteri (fun _ x -> f x) xs

val foreachM : forall 'a 'rv 'vars 'e.
  list 'a -> 'vars -> ('a -> 'vars -> monad 'rv 'vars 'e) -> monad 'rv 'vars 'e*)
Fixpoint foreachM {a Vars e} (l : list a) (vars : Vars) (body : a -> Vars -> monad Vars e) : monad Vars e :=
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

Fixpoint foreach_ZM_up' {e Vars} (from to step off : Z) (n : nat) (* 0 <? step *) (* 0 <=? off *) (vars : Vars) (body : forall (z : Z) (* from <=? z <=? to *), Vars -> monad Vars e) {struct n} : monad Vars e :=
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

Fixpoint foreach_ZM_down' {e Vars} (from to step off : Z) (n : nat) (* 0 <? step *) (* off <=? 0 *) (vars : Vars) (body : forall (z : Z) (* to <=? z <=? from *), Vars -> monad Vars e) {struct n} : monad Vars e :=
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

Definition foreach_ZM_up {e Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZM_up' (e := e) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.
Definition foreach_ZM_down {e Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZM_down' (e := e) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.

Definition foreach_ZE_up {e Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZE_up' (e := e) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.
Definition foreach_ZE_down {e Vars} from to step vars body (* 0 <? step *) :=
    foreach_ZE_down' (e := e) (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.

(*declare {isabelle} termination_argument foreachM = automatic*)

Definition genlistM {A E} (f : nat -> monad A E) (n : nat) : monad (list A) E :=
  let indices := List.seq 0 n in
  foreachM indices [] (fun n xs => (f n >>= (fun x => returnm (xs ++ [x])))).

(*val and_boolM : forall 'rv 'e. monad 'rv bool 'e -> monad 'rv bool 'e -> monad 'rv bool 'e*)
Definition and_boolM {E} (l : monad bool E) (r : monad bool E) : monad bool E :=
 l >>= (fun l => if l then r else returnm false).

(*val or_boolM : forall 'rv 'e. monad 'rv bool 'e -> monad 'rv bool 'e -> monad 'rv bool 'e*)
Definition or_boolM {E} (l : monad bool E) (r : monad bool E) : monad bool E :=
 l >>= (fun l => if l then returnm true else r).


(*val bool_of_bitU_fail : forall 'rv 'e. bitU -> monad 'rv bool 'e*)
Definition bool_of_bitU_fail {E} (b : bitU) : monad bool E :=
match b with
  | B0 => returnm false
  | B1 => returnm true
  | BU => Fail "bool_of_bitU"
end.

Definition bool_of_bitU_nondet {E} (b : bitU) : monad bool E :=
match b with
  | B0 => returnm false
  | B1 => returnm true
  | BU => choose_bool "bool_of_bitU"
end.

Definition bools_of_bits_nondet {E} (bits : list bitU) : monad (list bool) E :=
  foreachM bits []
    (fun b bools =>
      bool_of_bitU_nondet b >>= fun b => 
      returnm (bools ++ [b])).

Definition of_bits_nondet {n E} (bits : list bitU) : monad (mword n) E :=
  bools_of_bits_nondet bits >>= fun bs =>
  returnm (of_bools bs).

Definition of_bits_fail {n E} (bits : list bitU) : monad (mword n) E :=
  maybe_fail "of_bits" (of_bits bits).

(* For termination of recursive functions. *)
Definition _limit_reduces {_limit} (_acc:Acc (Zwf 0) _limit) (H : _limit >= 0) : Acc (Zwf 0) (_limit - 1).
refine (Acc_inv _acc _).
unbool_comparisons.
red.
lia.
Defined.

Definition _limit_reduces_bool {_limit} (_acc:Acc (Zwf 0) _limit) (H: _limit >=? 0 = true) : Acc (Zwf 0) (_limit - 1).
refine (_limit_reduces _acc _).
apply Z.geb_ge.
assumption.
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
Fixpoint whileMT' {Vars E} limit (vars : Vars) (cond : Vars -> monad bool E) (body : Vars -> monad Vars E) (acc : Acc (Zwf 0) limit) : monad Vars E.
exact (
  if Z_ge_dec limit 0 then
    cond vars >>= fun cond_val =>
    if cond_val then
      body vars >>= fun vars => whileMT' _ _ (limit - 1) vars cond body (_limit_reduces acc ltac:(assumption))
    else returnm vars
  else Fail "Termination limit reached").
Defined.

Definition whileMT {Vars E} (vars : Vars) (measure : Vars -> Z) (cond : Vars -> monad bool E) (body : Vars -> monad Vars E) : monad Vars E :=
  let limit := measure vars in
  whileMT' limit vars cond body (Zwf_guarded limit).

(*val untilM : forall 'rv 'vars 'e. 'vars -> ('vars -> monad 'rv bool 'e) ->
                ('vars -> monad 'rv 'vars 'e) -> monad 'rv 'vars 'e*)
Fixpoint untilMT' {Vars E} limit (vars : Vars) (cond : Vars -> monad bool E) (body : Vars -> monad Vars E) (acc : Acc (Zwf 0) limit) : monad Vars E.
exact (
  if Z_ge_dec limit 0 then
    body vars >>= fun vars =>
    cond vars >>= fun cond_val =>
    if cond_val then returnm vars else untilMT' _ _ (limit - 1) vars cond body (_limit_reduces acc ltac:(assumption))
  else Fail "Termination limit reached").
Defined.

Definition untilMT {Vars E} (vars : Vars) (measure : Vars -> Z) (cond : Vars -> monad bool E) (body : Vars -> monad Vars E) : monad Vars E :=
  let limit := measure vars in
  untilMT' limit vars cond body (Zwf_guarded limit).

(*let write_two_regs r1 r2 vec =
  let is_inc =
    let is_inc_r1 = is_inc_of_reg r1 in
    let is_inc_r2 = is_inc_of_reg r2 in
    let () = ensure (is_inc_r1 = is_inc_r2)
                    "write_two_regs called with vectors of different direction" in
    is_inc_r1 in

  let (size_r1 : integer) = size_of_reg r1 in
  let (start_vec : integer) = get_start vec in
  let size_vec = length vec in
  let r1_v =
    if is_inc
    then slice vec start_vec (size_r1 - start_vec - 1)
    else slice vec start_vec (start_vec - size_r1 - 1) in
  let r2_v =
    if is_inc
    then slice vec (size_r1 - start_vec) (size_vec - start_vec)
    else slice vec (start_vec - size_r1) (start_vec - size_vec) in
  write_reg r1 r1_v >> write_reg r2 r2_v*)

Section Choose.
Context {E : Type}.

Definition choose_from_list {A} (descr : string) (xs : list A) : monad A E :=
  (* Use sufficiently many nondeterministically chosen bits and convert into an
     index into the list *)
  choose_range descr 0 (Z.of_nat (List.length xs) - 1) >>= fun idx =>
  match List.nth_error xs (Z.to_nat idx) with
    | Some x => returnm x
    | None => Fail ("choose " ++ descr)
  end.

Definition internal_pick {a} (xs : list a) : monad a E :=
  choose_from_list "internal_pick" xs.

End Choose.

(* The normal print routines do nothing in Coq so that they don't drag terms and functions into the
   monad.  Here are alternative versions which do, which can be controlled by defining PRINT_EFFECTS
   in Sail. *)
Definition print_effect {E} (s : string) : monad unit E :=
  Print s (Done tt).

Definition print_endline_effect {E} (s : string) : monad unit E :=
  print_effect (s ++ "
")%string.

Definition print_int_effect {E} s i : monad unit E :=
  print_endline_effect (s ++ string_of_int i).

Definition print_bits_effect {E n} s (w : mword n) : monad unit E :=
  print_endline_effect (s ++ string_of_bits w).

(* We only have one output stream that we use for both. *)
Definition prerr_effect {E} s := @print_effect E s.
Definition prerr_endline_effect {E} s := @print_endline_effect E s.
Definition prerr_int_effect {E} s i := @print_int_effect E s i.
Definition prerr_bits_effect {E} s i := @print_bits_effect E s i.

End WithRegisterType.
