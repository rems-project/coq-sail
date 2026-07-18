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

(* Zeuclid will be removed once the Sail backend stops generating it.  The replacement definition is below. *)
From Stdlib Require Export ZArith String List Sumbool Zeuclid.
From Stdlib Require Import Ascii Eqdep_dec Lia.
From Stdlib Require BinaryString HexString.
Import ListNotations.
From Stdlib Require Import Rbase.  (* TODO would like to avoid this in models without reals *)
From Stdlib Require Eqdep EqdepFacts Zquot.

Require Import TypeCasts MachineWord.

Local Open Scope Z.
Local Open Scope bool.

(* Constraint solving basics.  A HintDb which unfolding hints and lemmata
   can be added to, and a typeclass to wrap constraint arguments in to
   trigger automatic solving. *)
Create HintDb sail.


Notation "x <=? y <=? z" := ((x <=? y) && (y <=? z)) (at level 70, y at next level) : Z_scope.
Notation "x <=? y <? z" := ((x <=? y) && (y <? z)) (at level 70, y at next level) : Z_scope.
Notation "x <? y <? z" := ((x <? y) && (y <? z)) (at level 70, y at next level) : Z_scope.
Notation "x <? y <=? z" := ((x <? y) && (y <=? z)) (at level 70, y at next level) : Z_scope.

Inductive result {a : Type} {b : Type} :=
| Ok : a -> result
| Err : b -> result.
Arguments result : clear implicits.

#[export]
Instance dummy_result {a : Type} {b : Type} `{Inhabited a} `{Inhabited b} :
  Inhabited (result a b) :=
{
  inhabitant := Ok inhabitant
}.

Definition result_bind {A B E} (f : A -> result B E) (a : result A E) : result B E :=
  match a with
  | Ok a => f a
  | Err e => Err e
  end.

Lemma result_bind_inv {A B E} (f : A -> result B E) (a : result A E) (b : B) :
  result_bind f a = Ok b -> exists a', a = Ok a' /\ f a' = Ok b.
Proof.
  intros EQ.
  destruct a as [a' | err].
  * exists a'. auto.
  * simpl in EQ. congruence.
Qed.

Definition result_bind_pf {A B E} (a : result A E) (f : forall a', a = Ok a' -> result B E) : result B E :=
  match a with
  | Ok a => fun f => f a eq_refl
  | Err e => fun _ => Err e
  end f.

(*** Basic pure functions *)

Definition pow m n := m ^ n.

Definition pow2 n := pow 2 n.

Lemma Z_geb_ge n m : (n >=? m) = true <-> n >= m.
Proof.
  rewrite Z.geb_leb.
  split.
  * intro. apply Z.le_ge, Z.leb_le. assumption.
  * intro. apply Z.ge_le in H. apply Z.leb_le. assumption.
Qed.

Definition neq l r := (negb (l =? r)). (* Z only *)

Definition print_endline (_ : string) : unit := tt.
Definition print (_ : string) : unit := tt.
Definition prerr_endline (_ : string) : unit := tt.
Definition prerr (_ : string) : unit := tt.
Definition print_int (_ : string) (_ : Z) : unit := tt.
Definition prerr_int (_ : string) (_ : Z) : unit := tt.
Definition putchar (_ : Z) : unit := tt.

Definition shl_int := Z.shiftl.
Definition shr_int := Z.shiftr.

Definition append_list {A:Type} (l : list A) r := l ++ r.
Definition length_list {A:Type} (xs : list A) := Z.of_nat (List.length xs).
Definition take_list {A:Type} n (xs : list A) := firstn (Z.to_nat n) xs.
Definition drop_list {A:Type} n (xs : list A) := skipn (Z.to_nat n) xs.

(* TODO: make all Sail model preludes use the Z definitions directly,
   preferably by having them in the standard library (currently
   waiting only on sail-cheri-riscv and cheriot-sail to update their
   base risc-v models). *)
Definition min_atom (a : Z) (b : Z) : Z := Z.min a b.
Definition max_atom (a : Z) (b : Z) : Z := Z.max a b.

(* Rocq stdlib has deprecated Euclidean convention division because it
   is rarely used, but it is included in the Sail standard library, so
   we include it here with some trivial rewrites. *)
Definition e_modulo a b := Z.modulo a (Z.abs b).
Definition e_div a b := (Z.sgn b) * (Z.div a (Z.abs b)).

Lemma e_modulo_pos a b : b > 0 -> e_modulo a b = Z.modulo a b.
Proof.
  intro H.
  unfold e_modulo.
  rewrite Z.abs_eq by lia.
  reflexivity.
Qed.

Lemma e_div_pos a b : b > 0 -> e_div a b = Z.div a b.
Proof.
  intro H.
  unfold e_div.
  rewrite Z.abs_eq, Z.sgn_pos by lia.
  lia.
Qed.


Fixpoint repeat' {a} (xs : list a) n :=
  match n with
  | O => []
  | S n => xs ++ repeat' xs n
  end.
Lemma repeat'_length {a} {xs : list a} {n : nat} : List.length (repeat' xs n) = (n * List.length xs)%nat.
Proof.
  induction n.
  * reflexivity.
  * simpl.
    rewrite length_app.
    auto with arith.
Qed.
Definition repeat {a} (xs : list a) (n : Z) :=
  if n <? 0 then []
  else repeat' xs (Z.to_nat n).

Lemma repeat_length {a} {xs : list a} {n : Z} (H : n >= 0) : (List.length (repeat xs n) = (Z.to_nat n) * List.length xs)%nat.
Proof.
  unfold repeat.
  apply Z.ge_le in H.
  rewrite <- Z.ltb_ge in H.
  rewrite H.
  apply repeat'_length.
Qed.

Lemma repeat_length_list {a} {xs : list a} {n : Z} (H : n >= 0) : length_list (repeat xs n) = n * length_list xs.
Proof.
  unfold length_list, repeat.
  destruct n.
  + reflexivity. 
  + simpl (List.length _).
    rewrite repeat'_length.
    rewrite Nat2Z.inj_mul.
    unfold Z.to_nat.
    rewrite positive_nat_Z.
    reflexivity.  
  + exfalso.
    auto with zarith.
Qed.


(* just_list takes a list of maybes and returns Some xs if all elements have
   a value, and None if one of the elements is None. *)
Fixpoint just_list {A} (l : list (option A)) := match l with
  | [] => Some []
  | (x :: xs) =>
    match (x, just_list xs) with
      | (Some x, Some xs) => Some (x :: xs)
      | (_, _) => None
    end
  end.

Lemma just_list_length {A} : forall (l : list (option A)) (l' : list A),
  Some l' = just_list l -> List.length l = List.length l'.
Proof.
  induction l.
  * intros.
    simpl in H.
    inversion H.
    reflexivity.
  * intros.
    destruct a; simplify_eq H.
    simpl in *.
    destruct (just_list l); simplify_eq H.
    intros.
    subst.
    simpl.
    f_equal.
    apply IHl.
    reflexivity.
Qed.

Lemma just_list_length_Z {A} : forall (l : list (option A)) l', Some l' = just_list l -> length_list l = length_list l'.
Proof.
  unfold length_list.
  intros.
  f_equal.
  auto using just_list_length.
Qed.

Fixpoint member_Z_list (x : Z) (l : list Z) : bool :=
  match l with
  | [] => false
  | h::t => if x =? h then true else member_Z_list x t
  end.

Lemma member_Z_list_In {x l} : member_Z_list x l = true <-> In x l.
Proof.
  induction l.
  * simpl. split. congruence. tauto.
  * simpl. destruct (x =? a) eqn:H.
    + rewrite Z.eqb_eq in H. subst. tauto.
    + rewrite Z.eqb_neq in H. split.
      - intro Heq. right. apply IHl. assumption.
      - intros [bad | good]. congruence. apply IHl. assumption.
Qed.

(*** Bool lists ***)

Fixpoint bools_of_nat_aux len (x : nat) (acc : list bool) : list bool :=
  match len with
  | O => acc
  | S len' => bools_of_nat_aux len' (x / 2) ((if x mod 2 =? 1 then true else false) :: acc)
  end %nat.
Definition bools_of_nat len n := bools_of_nat_aux (Z.to_nat len) n [].

Fixpoint nat_of_bools_aux (acc : nat) (bs : list bool) : nat :=
  match bs with
  | [] => acc
  | true :: bs => nat_of_bools_aux ((2 * acc) + 1) bs
  | false :: bs => nat_of_bools_aux (2 * acc) bs
end.
Definition nat_of_bools bs := nat_of_bools_aux 0 bs.

Definition unsigned_of_bools bs := Z.of_nat (nat_of_bools bs).

Definition signed_of_bools bs :=
  match bs with
    | true :: _  => 0 - (1 + (unsigned_of_bools (List.map negb bs)))
    | false :: _ => unsigned_of_bools bs
    | [] => 0 (* Treat empty list as all zeros *)
  end.

Definition int_of_bools (sign : bool) bs := if sign then signed_of_bools bs else unsigned_of_bools bs.

Fixpoint pad_list_nat {a} (x : a) (xs : list a) n :=
  match n with
  | O => xs
  | S n' => pad_list_nat x (x :: xs) n'
  end.
Definition pad_list {a} x xs n := @pad_list_nat a x xs (Z.to_nat n).

Definition ext_list {a} pad len (xs : list a) :=
  let longer := len - (Z.of_nat (List.length xs)) in
  if longer <? 0 then skipn (Z.abs_nat (longer)) xs
  else pad_list pad xs longer.

Definition exts_bools len bs :=
  match bs with
    | true :: _ => ext_list true len bs
    | _ => ext_list false len bs
  end.

Fixpoint add_one_bool_ignore_overflow_aux bits := match bits with
  | [] => []
  | false :: bits => true :: bits
  | true :: bits => false :: add_one_bool_ignore_overflow_aux bits
end.

Definition add_one_bool_ignore_overflow bits :=
  List.rev (add_one_bool_ignore_overflow_aux (List.rev bits)).

(*** List operations *)

Definition subrange_list_inc {A} (xs : list A) i j :=
  let toJ := firstn (Z.to_nat j + 1) xs in
  let fromItoJ := skipn (Z.to_nat i) toJ in
  fromItoJ.

Definition subrange_list_dec {A} (xs : list A) i j :=
  let top := (length_list xs) - 1 in
  subrange_list_inc xs (top - i) (top - j).

Definition subrange_list {A} (is_inc : bool) (xs : list A) i j :=
 if is_inc then subrange_list_inc xs i j else subrange_list_dec xs i j.

Definition splitAt {A} n (l : list A) := (firstn n l, skipn n l).

Definition update_subrange_list_inc {A} (xs : list A) i j xs' :=
  let (toJ,suffix) := splitAt (Z.to_nat j + 1) xs in
  let (prefix,_fromItoJ) := splitAt (Z.to_nat i) toJ in
  prefix ++ xs' ++ suffix.

Definition update_subrange_list_dec {A} (xs : list A) i j xs' :=
  let top := (length_list xs) - 1 in
  update_subrange_list_inc xs (top - i) (top - j) xs'.

Definition update_subrange_list {A} (is_inc : bool) (xs : list A) i j xs' :=
  if is_inc then update_subrange_list_inc xs i j xs' else update_subrange_list_dec xs i j xs'.

Open Scope nat.
Fixpoint nth_in_range {A} (n:nat) (l:list A) : n < length l -> A.
Proof.
  refine 
    (match n, l with
    | O, h::_ => fun _ => h
    | S m, _::t => fun H => nth_in_range A m t _
    | _,_ => fun H => _
    end).
  exfalso. inversion H.
  exfalso. inversion H.
  simpl in H. lia.
Defined.

Lemma nth_in_range_is_nth : forall A n (l : list A) d (H : n < length l),
  nth_in_range n l H = nth n l d.
Proof.
  intros until d. revert n.
  induction l; intros n H.
  * inversion H.
  * destruct n.
    + reflexivity.
    + apply IHl.
Qed.

Lemma nth_Z_nat {A} {n} {xs : list A} :
  (0 <= n)%Z -> (n < length_list xs)%Z -> Z.to_nat n < length xs.
Proof.
  unfold length_list.
  intros nonneg bounded.
  rewrite Z2Nat.inj_lt in bounded; auto using Zle_0_nat.
  rewrite Nat2Z.id in bounded.
  assumption.
Qed.

Close Scope nat.

Definition access_list_inc {A} (xs : list A) `{Inhabited A} (n : Z) : A :=
  if n <? 0 then dummy_value else nth (Z.to_nat n) xs dummy_value.

Definition access_list_dec {A} (xs : list A) n `{Inhabited A} : A :=
  let top := (length_list xs) - 1 in
  access_list_inc xs (top - n).

Definition access_list {A} (is_inc : bool) (xs : list A) n `{Inhabited A} :=
  if is_inc then access_list_inc xs n else access_list_dec xs n.

Definition access_list_opt_inc {A} (xs : list A) n := nth_error xs (Z.to_nat n).

Definition access_list_opt_dec {A} (xs : list A) n :=
  let top := (length_list xs) - 1 in
  access_list_opt_inc xs (top - n).

Definition access_list_opt {A} (is_inc : bool) (xs : list A) n :=
  if is_inc then access_list_opt_inc xs n else access_list_opt_dec xs n.

Definition list_update {A} (xs : list A) n x := firstn n xs ++ x :: skipn (S n) xs.

Definition update_list_inc {A} (xs : list A) n x := list_update xs (Z.to_nat n) x.

Definition update_list_dec {A} (xs : list A) n x :=
  let top := (length_list xs) - 1 in
  update_list_inc xs (top - n) x.

Definition update_list {A} (is_inc : bool) (xs : list A) n x :=
  if is_inc then update_list_inc xs n x else update_list_dec xs n x.

(*** Machine words *)

Section MachineWords.

Import MachineWord.

(* ISA models tend to use integers for sizes, so Sail's bitvectors are integer
   indexed.  To avoid carrying around proofs that sizes are non-negative
   everywhere we define negative sized machine words to be a trivial value. *)

Definition mword (n : Z) := word (Z_idx n).

#[export] Instance dummy_mword {n} : Inhabited (mword n) := {
  inhabitant := match n with
  | Zpos _ => zeros _
  | _ => zeros _
  end
}.

Definition to_word_idx {n} (w : word n) : mword (idx_Z n) :=
  (cast_idx w (Z_idx_Z n)).

(* Show that to_word_idx doesn't really change the bitvector, starting with some
   reasoning using dependent equality, but ultimately finishing with a directly
   usably plain equality result. *)

Lemma cast_idx_eq_dep T m n o (x : T m) (y : T n) EQ : EqdepFacts.eq_dep _ _ _ x _ y -> EqdepFacts.eq_dep _ _ _ x o (cast_idx y EQ).
Proof.
  intros.
  subst.
  rewrite cast_idx_refl.
  assumption.
Qed.

Lemma Z_idx_eq_dep T m n (x : T (Z_idx m)) (y : T (Z_idx n)) : m > 0 -> n > 0 -> EqdepFacts.eq_dep idx T _ x _ y -> EqdepFacts.eq_dep Z (fun n => T (Z_idx n)) _ x _ y.
Proof.
  intros M N EQ.
  assert (m = n). {
    inversion EQ.
    apply Z2Nat.inj; auto with zarith.
  }
  subst.
  apply Eqdep.EqdepTheory.eq_dep_eq in EQ.
  subst.
  constructor.
Qed.

Lemma to_word_idx_cast n (w : mword n) :
  n > 0 ->
  w = autocast (to_word_idx w).
Proof.
  intros.
  change (word (Z_idx n)) with (mword n).
  apply Eqdep_dec.eq_dep_eq_dec; auto using Z.eq_dec.
  eapply EqdepFacts.eq_dep_trans. 2: apply autocast_eq_dep. 2: (apply idx_Z_idx; lia).
  unfold to_word_idx.
  apply Z_idx_eq_dep; [ assumption | rewrite idx_Z_idx; lia | ].
  apply cast_idx_eq_dep.
  constructor.
Qed.

Definition length_mword {n} (w : mword n) := n.

Definition access_mword_dec {m} (w : mword m) n : mword 1 := slice 1 w (Z_idx n).

Definition access_mword_inc {m} (w : mword m) n : mword 1 :=
  let top := (length_mword w) - 1 in
  access_mword_dec w (top - n).

Definition access_mword {a} (is_inc : bool) (w : mword a) n :=
  if is_inc then access_mword_inc w n else access_mword_dec w n.

Definition update_mword_bool_dec {a} (w : mword a) n b : mword a :=
  set_bit w (Z_idx n) b.
Definition update_mword_dec {a} (w : mword a) n (b : mword 1) :=
  update_slice w (Z_idx n) b.

Definition update_mword_inc {a} (w : mword a) n b :=
  let top := (length_mword w) - 1 in
  update_mword_dec w (top - n) b.

Definition update_mword {a} (is_inc : bool) (w : mword a) n b :=
  if is_inc then update_mword_inc w n b else update_mword_dec w n b.

Definition int_of_mword {a} (sign : bool) (w : mword a) :=
  if sign then word_to_Z w else Z.of_N (word_to_N w).

Definition mword_of_int {len} n : mword len := Z_to_word _ n.

Definition mword_to_N {n} (w : mword n) : N := word_to_N w.

Lemma word_to_N_cast_idx {m n w} {E : m = n} :
  word_to_N (cast_idx w E) = word_to_N w.
Proof.
  subst.
  rewrite cast_idx_refl.
  reflexivity.
Qed.

Lemma mword_to_N_cast_Z {m n w} {E : m = n} :
  mword_to_N (cast_Z w E) = mword_to_N w.
Proof.
  subst.
  rewrite cast_Z_refl.
  reflexivity.
Qed.

Definition mword_to_bools {n} (w : mword n) : list bool := word_to_bools w.
Definition bools_to_mword (l : list bool) : mword (length_list l) := cast_idx (bools_to_word l) (nat_idx_Z _).

Definition eq_vec_dec {n} : forall (x y : mword n), {x = y} + {x <> y} :=
  match n with
  | Z0 => @MachineWord.eq_dec _
  | Zpos m => @MachineWord.eq_dec _
  | Zneg m => @MachineWord.eq_dec _
  end.

Local Lemma mword_of_bytes_idx (bs : list (mword 8)) :
  idx_Z (idx_mul (Z_idx 8) (nat_idx (Datatypes.length bs))) = 8 * length_list bs.
Proof.
  rewrite idx_Z_idx_mul, nat_idx_Z, !idx_Z_idx.
  * reflexivity.
  * apply Z.le_ge. apply Nat2Z.is_nonneg.
  * lia.
Qed.

Definition mword_of_bytes (bs : list (mword 8)) : mword (8 * length_list bs) :=
  cast_Z (to_word_idx (MachineWord.word_list_concat bs)) (mword_of_bytes_idx bs).

Local Lemma bytes_of_mword_idx n : n >= 0 -> Z_idx (8 * n) = idx_mul (Z_idx 8) (Z_idx n).
Proof.
  intro.
  rewrite Z_idx_Z.
  f_equal.
  rewrite idx_Z_idx_mul.
  rewrite !idx_Z_idx; lia.
Qed.

Definition bytes_of_mword [n] (w : mword (8 * n)) : list (mword 8) :=
  match Z_ge_lt_dec n 0 with
  | left p => MachineWord.word_split_list (cast_idx (n := idx_mul (Z_idx 8) (Z_idx n)) w (bytes_of_mword_idx _ p))
  | right _ => []
  end.

Definition bit_of_bool (b : bool) : mword 1 :=
  if b then mword_of_int 0 else mword_of_int 1.

Definition bool_of_bit (b : mword 1) : bool :=
  MachineWord.get_bit b 0.

End MachineWords.

(* Some useful tactics left over from when we did constraint solving. *)

Lemma lift_bool_exists (l r : bool) (P : bool -> Prop) :
  (l = r -> exists x, P x) ->
  (exists x, l = r -> P x).
Proof.
  intro H.
  destruct (Bool.bool_dec l r) as [e | ne].
  * destruct (H e) as [x H']; eauto.
  * exists true; tauto.
Qed.

Ltac dump_context :=
  repeat match goal with
  | H:=?X |- _ => idtac H ":=" X; fail
  | H:?X |- _ => idtac H ":" X; fail end;
  match goal with |- ?X => idtac "Goal:" X end.

#[export] Hint Unfold length_mword : sail.

Lemma unit_comparison_lemma : true = true <-> True.
Proof.
  intuition.
Qed.
#[export] Hint Resolve unit_comparison_lemma : sail.

Definition neq_atom (x : Z) (y : Z) : bool := negb (Z.eqb x y).
#[export] Hint Unfold neq_atom : sail.

Definition opt_def {a} (def:a) (v:option a) :=
  match v with
  | Some x => x
  | None => def
  end.

Fixpoint byte_chunks {a} (bs : list a) : option (list (list a)) := match bs with
  | [] => Some []
  | a::b::c::d::e::f::g::h::rest =>
     match byte_chunks rest with
     | None => None
     | Some rest => Some ([a;b;c;d;e;f;g;h] :: rest)
     end
  | _ => None
end.

(*** Registers *)

Record register_ref {register : Type} {type_of_register : register -> Type} (ty : Type) := {
  name : string;
  reg : register;
  to_ty : type_of_register reg -> ty;
  from_ty : ty -> type_of_register reg;
}.
Arguments name [_ _ _].
Arguments reg [_ _ _].
Arguments to_ty [_ _ _].
Arguments from_ty [_ _ _].

(* Remember that these inhabitants are not used by well typed Sail
code, so it doesn't matter that it's not useful. *)
#[export] Instance dummy_register_ref {register} {type_of_register} `{Inhabited register} : Inhabited (@register_ref register type_of_register (type_of_register dummy_value)) := {
  inhabitant := {| name := ""; reg := dummy_value; to_ty := fun x => x; from_ty := fun x => x |}
}.

(* Register accessors: pair of functions for reading and writing register values *)
Definition register_accessors regstate reg_type reg_to_type : Type :=
  ((forall (r : reg_type), regstate -> reg_to_type r) *
   (forall (r : reg_type), reg_to_type r -> regstate -> regstate)).


(* The choice operations in the monads operate on a small selection of base
   types.  Normally, -undefined_gen is used to construct functions for more
   complex types. *)
Inductive ChooseType : Type :=
  | ChooseBool | ChooseInt | ChooseNat | ChooseReal | ChooseString
  | ChooseRange (lo hi : Z) | ChooseBitvector (n:Z).
Scheme Equality for ChooseType.
Definition choose_type ty :=
  match ty with
  | ChooseBool => bool | ChooseInt => Z | ChooseNat => Z
  | ChooseReal => R | ChooseString => string
  | ChooseRange _ _ => Z | ChooseBitvector n => mword n
  end.

(* The property that is expected to hold of the chosen value. *)
Definition choose_prop ty : choose_type ty -> Prop :=
  match ty with
  | ChooseBool
  | ChooseInt
  | ChooseNat
  | ChooseReal
  | ChooseString => fun _ => True
  | ChooseBitvector _n => fun _ => True
  | ChooseRange lo hi => fun z => (lo <= z <= hi)%Z
  end.

(* TODO: try and split out Reals again *)
#[export] Instance R_inhabited : Inhabited R := { inhabitant := R0 }.

(* NB: this only works because we don't enforce choose_prop here. *)
#[export] Instance choose_type_inhabited {ty} : Inhabited (choose_type ty).
Proof.
  destruct ty; simpl; constructor; apply inhabitant.
Defined.

(*** Loop combinators *)

Fixpoint foreach {a Vars} (l : list a) (vars : Vars) (body : a -> Vars -> Vars) : Vars :=
  match l with
  | [] => vars
  | (x :: xs) => foreach xs (body x vars) body
  end.

Fixpoint index_list' from to step n :=
  if orb (andb (step >? 0) (from <=? to)) (andb (step <? 0) (to <=? from)) then
    match n with
    | O => []
    | S n => from :: index_list' (from + step) to step n
    end
  else [].

Definition index_list from to step :=
  if orb (andb (step >? 0) (from <=? to)) (andb (step <? 0) (to <=? from)) then
    index_list' from to step (S (Z.abs_nat (from - to)))
  else [].

Fixpoint foreach_Z' {Vars} from to step n (vars : Vars) (body : Z -> Vars -> Vars) : Vars :=
  if orb (andb (step >? 0) (from <=? to)) (andb (step <? 0) (to <=? from)) then
    match n with
    | O => vars
    | S n => let vars := body from vars in foreach_Z' (from + step) to step n vars body
    end
  else vars.

Definition foreach_Z {Vars} from to step vars body :=
  foreach_Z' (Vars := Vars) from to step (S (Z.abs_nat (from - to))) vars body.

Fixpoint foreach_Z_up' {Vars} (from to step off : Z) (n:nat) (* 0 <? step *) (* 0 <=? off *) (vars : Vars) (body : forall (z : Z) (* from <=? z <=? to *), Vars -> Vars) {struct n} : Vars :=
  if sumbool_of_bool (from + off <=? to) then
    match n with
    | O => vars
    | S n => let vars := body (from + off) vars in foreach_Z_up' from to step (off + step) n vars body
    end
  else vars
.

Fixpoint foreach_Z_down' {Vars} from to step off (n:nat) (* 0 <? step *) (* off <=? 0 *) (vars : Vars) (body : forall (z : Z) (* to <=? z <=? from *), Vars -> Vars) {struct n} : Vars :=
  if sumbool_of_bool (to <=? from + off) then
    match n with
    | O => vars
    | S n => let vars := body (from + off) vars in foreach_Z_down' from to step (off - step) n vars body
    end
  else vars
.

Definition foreach_Z_up {Vars} from to step vars body (* 0 <? step *) :=
    foreach_Z_up' (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.
Definition foreach_Z_down {Vars} from to step vars body (* 0 <? step *) :=
    foreach_Z_down' (Vars := Vars) from to step 0 (S (Z.abs_nat (from - to))) vars body.

(* We do not give combinators for while and until here because they do not necessarily
   terminate; instead they are provided alongside the monad. *)

(*** Generic vectors *)

Definition vec (T:Type) (n:Z) := { l : list T & List.length l = Z.to_nat n }.
Definition vec_length {T n} (v : vec T n) := n.
Definition vec_access_dec {T n} (v : vec T n) m `{Inhabited T} : T :=
  access_list_dec (projT1 v) m.

Definition vec_access_inc {T n} (v : vec T n) m `{Inhabited T} : T :=
  access_list_inc (projT1 v) m.

(* "Negative" length vectors are treated as empty, but would normally be a mistake,
   so define an opaque default value for them so that it's obvious when one appears. *)
Definition dodgy_vec {T:Type} n (NEG: (n >=? 0) = false) : vec T n.
Proof.
  refine (@existT _ _ [] _).
  destruct n; try discriminate.
  reflexivity.
Qed.

Lemma vec_init_ok {T} {n} {t : T} : (n >=? 0) = true -> Datatypes.length (repeat [t] n) = Z.to_nat n.
Proof.
  intro GE.
  rewrite repeat_length.
  - simpl.
    apply Nat.mul_1_r.
  - auto with zarith.
Qed.

Definition vector_init {T} (n : Z) (t : T) : vec T n :=
  match sumbool_of_bool (n >=? 0) with
  | left GE => @existT _ _ (repeat [t] n) (vec_init_ok GE)
  | right NGE => dodgy_vec n NGE
  end.

#[export] Instance dummy_vec {T:Type} `{Inhabited T} n : Inhabited (vec T n) := {| inhabitant := vector_init n inhabitant |}.

Fixpoint list_init {T} n (f : Z -> T) : list T :=
  match n with
  | O => []
  | S m => f (Z.of_nat m) :: list_init m f
  end.

Lemma list_init_length T n (f : Z -> T) :
  length (list_init n f) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. auto.
Qed.

Definition vec_init_fn {T} n (f : Z -> T) : vec T n :=
  match sumbool_of_bool (n >=? 0) with
  | left GE => @existT _ _ (list_init (Z.to_nat n) f) (list_init_length _ _ _)
  | right NGE => dodgy_vec n NGE
  end.

Definition vec_concat {T m n} `{Inhabited T} (v : vec T m) (w : vec T n) : vec T (m + n).
Proof.
  refine (
    if sumbool_of_bool ((m >=? 0) && (n >=? 0)) then
       @existT _ _ (projT1 v ++ projT1 w) _
    else dummy_value).
  destruct v,w.
  rewrite length_app.
  rewrite Z2Nat.inj_add; auto with zarith.
Defined.

Lemma skipn_length {A n} {l: list A} : (n <= List.length l -> List.length (skipn n l) = List.length l - n)%nat.
Proof.
  revert l.
  induction n.
  * simpl. auto with arith.
  * intros l H.
    destruct l.
    + inversion H.
    + simpl in H.
      simpl.
      rewrite IHn; auto with arith.
Qed.
Lemma update_list_inc_length {T} {l:list T} {m x} : 0 <= m < length_list l -> List.length (update_list_inc l m x) = List.length l.
Proof.
  unfold update_list_inc, list_update.
  intro H.
  assert ((0 <= Z.to_nat m < Datatypes.length l)%nat).
  { destruct H as [H1 H2].
    split.
    + change 0%nat with (Z.to_nat 0).
      apply Z2Nat.inj_le; auto with zarith.
    + rewrite <- Nat2Z.id.
      apply Z2Nat.inj_lt; auto with zarith.
  }
  rewrite length_app.
  rewrite firstn_length_le; only 2:lia.
  cbn -[skipn].
  rewrite skipn_length;
  lia.
Qed.

Lemma vec_update_dec_lemma {T n} {v : vec T n} {m t} : (0 <=? m <? n) = true -> length (update_list_dec (projT1 v) m t) = Z.to_nat n.
Proof.
  intro.
  unfold update_list_dec.
  destruct v as [v' L].
  rewrite update_list_inc_length.
  + apply L.
  + simpl.
    unfold length_list.
    lia.
Qed.

Definition vec_update_dec {T n} `{Inhabited T} (v : vec T n) (m : Z) (t : T) : vec T n :=
  match sumbool_of_bool (0 <=? m <? n) with
  | left e => @existT _ _ (update_list_dec (projT1 v) m t) (vec_update_dec_lemma e)
  | right _ => dummy_value
  end.

Lemma vec_update_inc_lemma {T n} {v : vec T n} {m t} : (0 <=? m <? n) = true -> length (update_list_inc (projT1 v) m t) = Z.to_nat n.
Proof.
  intro e.
  destruct v as [v' L].
  rewrite update_list_inc_length.
  + apply L.
  + unfold length_list.
    simpl.
    lia.
Qed.

Definition vec_update_inc {T n} `{Inhabited T} (v : vec T n) (m : Z) (t : T) : vec T n :=
  match sumbool_of_bool (0 <=? m <? n) with
  | left e => @existT _ _ (update_list_inc (projT1 v) m t) (vec_update_inc_lemma e)
  | right _ => dummy_value
  end.

Definition vec_map {S T} (f : S -> T) {n} (v : vec S n) : vec T n.
Proof.
  refine (@existT _ _ (List.map f (projT1 v)) _).
  destruct v as [l H].
  cbn.
  unfold length_list.
  rewrite length_map.
  apply H.
Defined.

#[local] Obligation Tactic := idtac.
Program Definition just_vec {A n} (v : vec (option A) n) : option (vec A n) :=
  match just_list (projT1 v) with
  | None => None
  | Some v' => Some (@existT _ _ v' _)
  end.
Next Obligation.
  intros until v.
  simpl.
  intros v' EQ.
  rewrite <- (just_list_length _ _ EQ).
  destruct v.
  assumption.
Defined.

Definition list_of_vec {A n} (v : vec A n) : list A := projT1 v.

Definition vec_eq_dec {T n} (D : forall x y : T, {x = y} + {x <> y}) (x y : vec T n) :
  {x = y} + {x <> y}.
Proof.
  refine (if List.list_eq_dec D (projT1 x) (projT1 y) then left _ else right _).
  * apply eq_sigT_hprop; auto using UIP_nat.
  * contradict n0. rewrite n0. reflexivity.
Defined.

Definition vec_of_list {A} n (l : list A) : option (vec A n).
Proof.
  refine (
    match sumbool_of_bool (List.length l =? Z.to_nat n)%nat with
    | left H => Some (@existT _ _ l _)
    | right _ => None
    end
  ).
  apply Nat.eqb_eq.
  exact H.
Defined.

Lemma vec_of_list_eq {A n l} pf :
  @vec_of_list A n l = Some (@existT _ _ l pf).
Proof.
  simpl in pf.
  unfold vec_of_list.
  destruct (sumbool_of_bool (Datatypes.length l =? Z.to_nat n)%nat) as [e|e].
  * do 2 f_equal.
    apply UIP_nat.
  * exfalso.
    apply Nat.eqb_neq in e.
    congruence.
Qed.

Definition vec_of_list_len {A} (l : list A) : vec A (length_list l). 
Proof.
  refine (@existT _ _ l _).
  unfold length_list.
  rewrite Nat2Z.id.
  reflexivity.
Defined.

Definition map_bind {A B} (f : A -> option B) (a : option A) : option B :=
  match a with
  | Some a' => f a'
  | None => None
  end.

(* Limits for remainders *)

Lemma Z_rem_really_nonneg : forall a b : Z, 0 <= a -> 0 <= Z.rem a b.
Proof.
  intros.
  destruct (Z.eq_dec b 0).
  + subst. rewrite Zquot.Zrem_0_r. assumption.
  + auto using Z.rem_nonneg.
Qed.

Lemma Z_rem_pow_upper_bound : forall x x0 l,
0 <= x -> 2 ^ l <= x0 -> x0 <= 2 ^ l -> 0 <= l -> Z.rem x x0 < 2 ^ l.
Proof.
  intros.
  assert (x0 = 2 ^ l). auto with zarith.
  subst.
  apply Z.rem_bound_pos; auto with zarith.
Qed.

#[export] Hint Resolve Z_rem_really_nonneg Z_rem_pow_upper_bound : sail.

(* This is needed because Sail's internal constraint language doesn't have
   < and could disappear if we add it... *)

Lemma sail_lt_ge (x y : Z) :
  x < y <-> y >= x +1.
Proof.
  lia.
Qed.
#[export] Hint Resolve sail_lt_ge : sail.

(* Helpers for constructing eq_dec functions from encodings into positives *)

Lemma decode_encode_inj {T} (f : T -> positive) (g : positive -> option T) :
  (forall x, g (f x) = Some x) ->
  forall x y, f x = f y -> x = y.
Proof.
  intros H x y ?.
  enough (Some x = Some y); congruence.
Qed.
Definition decode_encode_eq_dec {T} (f : T -> positive) (g : positive -> option T)
  (H : forall x, g (f x) = Some x) (x y : T) : {x = y} + {x <> y}.
Proof.
  refine (match Pos.eq_dec (f x) (f y) with
  | left e => left (decode_encode_inj f g H x y e)
  | right ne => right _
  end).
  congruence.
Defined.

(* If we can pick arbitrary inhabitants for the elements of a dependent pair,
   then it's inhabited. *)

#[export] Instance Inhabited_sigT {T} {P : T -> Type} `{Inhabited T} `{forall t, Inhabited (P t)} : Inhabited (sigT P) := {
  inhabitant := @existT _ _ inhabitant inhabitant
}.

(* Override expensive unary exponential notation for binary, fill in sizes too *)
Notation "sz ''b' a" := (MachineWord.N_to_word sz (BinaryString.Raw.to_N a N0)) (at level 50).
Notation "''b' a" := (MachineWord.N_to_word _ (BinaryString.Raw.to_N a N0) :
                       mword (ltac:(let sz := eval cbv in (Z.of_nat (String.length a)) in exact sz)))
                     (at level 50, only parsing).
Notation "'Ox' a" := (MachineWord.N_to_word _ (HexString.Raw.to_N a N0) :
                       mword (ltac:(let sz := eval cbv in (4 * (Z.of_nat (String.length a))) in exact sz)))
                     (at level 50, only parsing).
