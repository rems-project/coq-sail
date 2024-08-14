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

(* Machinery for typeclass instances, stdpp version *)

From Coq Require Reals.ROrderedType.
From SailStdpp Require Import Values.
From stdpp Require Import base countable decidable strings.

Definition generic_eq {T:Type} (x y:T) `{EqDecision T} : bool := bool_decide (x = y).
Definition generic_neq {T:Type} (x y:T) `{EqDecision T} := negb (bool_decide (x = y)).
Lemma generic_eq_true {T} {x y:T} `{EqDecision T} : generic_eq x y = true -> x = y.
Proof.
  apply bool_decide_eq_true.
Qed.
Lemma generic_eq_false {T} {x y:T} `{EqDecision T} : generic_eq x y = false -> x <> y.
Proof.
  apply bool_decide_eq_false.
Qed.
Lemma generic_neq_true {T} {x y:T} `{EqDecision T} : generic_neq x y = true -> x <> y.
Proof.
  unfold generic_neq.
  rewrite negb_true_iff.
  apply bool_decide_eq_false_1.
Qed.
Lemma generic_neq_false {T} {x y:T} `{EqDecision T} : generic_neq x y = false -> x = y.
Proof.
  unfold generic_neq.
  rewrite negb_false_iff.
  apply bool_decide_eq_true_1.
Qed.

Definition generic_dec {T:Type} (x y:T) `{EqDecision T} : {x = y} + {x <> y} := decide (x = y).

(* Used by generated code that builds Decidable equality instances for records. *)
Ltac cmp_record_field x y :=
  let H := fresh "H" in
  case (generic_dec x y);
  intro H; [ | right; injection; auto ].

#[export] Instance Decidable_eq_bit : EqDecision bitU := bitU_eq_dec.

#[export] Instance Countable_bitU : Countable bitU.
refine {|
  encode x := match x with B0 => 1 | B1 => 2 | BU => 3 end;
  decode x := match x with 1 => Some B0 | 2 => Some B1 | 3 => Some BU | _ => None end
|}%positive.
intros [| |]; reflexivity.
Defined.

Ltac unbool_comparisons :=
  repeat match goal with
  | H:@eq bool _ _ -> @ex bool _ |- _ => apply lift_bool_exists in H; destruct H
  | H:@ex Z _ |- _ => destruct H
  (* Omega doesn't know about In, but can handle disjunctions. *)
  | H:context [member_Z_list _ _ = true] |- _ => rewrite member_Z_list_In in H
  | H:context [In ?x (?y :: ?t)] |- _ => change (In x (y :: t)) with (y = x \/ In x t) in H
  | H:context [In ?x []] |- _ => change (In x []) with False in H
  | H:?v = true |- _ => is_var v; subst v
  | H:?v = false |- _ => is_var v; subst v
  | H:true = ?v |- _ => is_var v; subst v
  | H:false = ?v |- _ => is_var v; subst v
  | H:_ /\ _ |- _ => destruct H
  | H:context [Z.geb _ _] |- _ => rewrite Z.geb_leb in H
  | H:context [Z.gtb _ _] |- _ => rewrite Z.gtb_ltb in H
  | H:context [Z.leb _ _ = true] |- _ => rewrite Z.leb_le in H
  | H:context [Z.ltb _ _ = true] |- _ => rewrite Z.ltb_lt in H
  | H:context [Z.eqb _ _ = true] |- _ => rewrite Z.eqb_eq in H
  | H:context [Z.leb _ _ = false] |- _ => rewrite Z.leb_gt in H
  | H:context [Z.ltb _ _ = false] |- _ => rewrite Z.ltb_ge in H
  | H:context [Z.eqb _ _ = false] |- _ => rewrite Z.eqb_neq in H
  | H:context [orb _ _ = true] |- _ => rewrite Bool.orb_true_iff in H
  | H:context [orb _ _ = false] |- _ => rewrite Bool.orb_false_iff in H
  | H:context [andb _ _ = true] |- _ => rewrite Bool.andb_true_iff in H
  | H:context [andb _ _ = false] |- _ => rewrite Bool.andb_false_iff in H
  | H:context [negb _ = true] |- _ => rewrite Bool.negb_true_iff in H
  | H:context [negb _ = false] |- _ => rewrite Bool.negb_false_iff in H
  | H:context [Bool.eqb _ ?r = true] |- _ => rewrite Bool.eqb_true_iff in H;
                                             try (is_var r; subst r)
  | H:context [Bool.eqb _ _ = false] |- _ => rewrite Bool.eqb_false_iff in H
  | H:context [generic_eq _ _ = true] |- _ => apply generic_eq_true in H
  | H:context [generic_eq _ _ = false] |- _ => apply generic_eq_false in H
  | H:context [generic_neq _ _ = true] |- _ => apply generic_neq_true in H
  | H:context [generic_neq _ _ = false] |- _ => apply generic_neq_false in H
  | H:context [_ <> true] |- _ => rewrite Bool.not_true_iff_false in H
  | H:context [_ <> false] |- _ => rewrite Bool.not_false_iff_true in H
  | H:context [@eq bool ?l ?r] |- _ =>
    lazymatch r with
    | true => fail
    | false => fail
    | _ => rewrite (Bool.eq_iff_eq_true l r) in H
    end
  end.
Ltac unbool_comparisons_goal :=
  repeat match goal with
  (* Important to have these early in the list - setoid_rewrite can
     unfold member_Z_list. *)
  | |- context [member_Z_list _ _ = true] => rewrite member_Z_list_In
  | |- context [In ?x (?y :: ?t)] => change (In x (y :: t)) with (y = x \/ In x t) 
  | |- context [In ?x []] => change (In x []) with False
  | |- context [Z.geb _ _] => setoid_rewrite Z.geb_leb
  | |- context [Z.gtb _ _] => setoid_rewrite Z.gtb_ltb
  | |- context [Z.leb _ _ = true] => setoid_rewrite Z.leb_le
  | |- context [Z.ltb _ _ = true] => setoid_rewrite Z.ltb_lt
  | |- context [Z.eqb _ _ = true] => setoid_rewrite Z.eqb_eq
  | |- context [Z.leb _ _ = false] => setoid_rewrite Z.leb_gt
  | |- context [Z.ltb _ _ = false] => setoid_rewrite Z.ltb_ge
  | |- context [Z.eqb _ _ = false] => setoid_rewrite Z.eqb_neq
  | |- context [orb _ _ = true] => setoid_rewrite Bool.orb_true_iff
  | |- context [orb _ _ = false] => setoid_rewrite Bool.orb_false_iff
  | |- context [andb _ _ = true] => setoid_rewrite Bool.andb_true_iff
  | |- context [andb _ _ = false] => setoid_rewrite Bool.andb_false_iff
  | |- context [negb _ = true] => setoid_rewrite Bool.negb_true_iff
  | |- context [negb _ = false] => setoid_rewrite Bool.negb_false_iff
  | |- context [Bool.eqb _ _ = true] => setoid_rewrite Bool.eqb_true_iff
  | |- context [Bool.eqb _ _ = false] => setoid_rewrite Bool.eqb_false_iff
  | |- context [generic_eq _ _ = true] => apply generic_eq_true
  | |- context [generic_eq _ _ = false] => apply generic_eq_false
  | |- context [generic_neq _ _ = true] => apply generic_neq_true
  | |- context [generic_neq _ _ = false] => apply generic_neq_false
  | |- context [_ <> true] => setoid_rewrite Bool.not_true_iff_false
  | |- context [_ <> false] => setoid_rewrite Bool.not_false_iff_true
  | |- context [@eq bool _ ?r] =>
    lazymatch r with
    | true => fail
    | false => fail
    | _ => setoid_rewrite Bool.eq_iff_eq_true
    end
  end.

#[export] Instance Decidable_eq_vec {n} `{EqDecision T} : EqDecision (vec T n) :=
   vec_eq_dec (fun x y => generic_dec x y).

#[export] Instance Countable_vec {n} `{Countable T} : Countable (vec T n).
refine {|
  encode v := encode (projT1 v);
  decode p := l ← decode p;
              vec_of_list n l
|}.
intros [l pf].
rewrite decode_encode.
simpl.
apply vec_of_list_eq.
Qed.

(* "Decidable" in a classical sense... *)
#[export] Instance Decidable_eq_real : EqDecision Reals.Rdefinitions.R :=
  Reals.ROrderedType.Req_dec.

#[export] Instance Decidable_eq_mword {n} : EqDecision (mword n) := eq_vec_dec.

#[export] Instance Countable_mword {n} : Countable (mword n).
refine {|
  encode := match n with Zpos _ => encode | _ => encode end;
  decode p := match n return option (mword n) with Zpos _ => decode p | _ => decode p end;
|}.
destruct n; apply decode_encode.
Qed.
