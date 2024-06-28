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

(* Version of sail_values.lem that uses Lems machine words library *)

(*Require Import Sail_impl_base*)
Require Export ZArith.
Require Import Ascii.
Require Export String.
Require BinaryString.
Require HexString.
Require Export List.
Require Export Sumbool.
Require Import Eqdep_dec.
Require Export Zeuclid.
Require Import Lia.
Import ListNotations.
Require Import Rbase.  (* TODO would like to avoid this in models without reals *)
Require Eqdep EqdepFacts.

Require Import Sail.TypeCasts.
Require Import Sail.MachineWord.

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

Definition ii := Z.
Definition nn := nat.

(*val pow : Z -> Z -> Z*)
Definition pow m n := m ^ n.

Definition pow2 n := pow 2 n.

Lemma ZEuclid_div_pos : forall x y, 0 < y -> 0 <= x -> 0 <= ZEuclid.div x y.
intros.
unfold ZEuclid.div.
change 0 with (0 * 0).
apply Zmult_le_compat.
3,4: auto with zarith.
* apply Z.sgn_nonneg. auto with zarith.
* apply Z_div_pos; auto. apply Z.lt_gt. apply Z.abs_pos. auto with zarith.
Qed.

Lemma ZEuclid_pos_div : forall x y, 0 < y -> 0 <= ZEuclid.div x y -> 0 <= x.
intros x y GT.
  specialize (ZEuclid.div_mod x y);
  specialize (ZEuclid.mod_always_pos x y);
  generalize (ZEuclid.modulo x y);
  generalize (ZEuclid.div x y);
  intros.
nia.
Qed.

Lemma ZEuclid_div_ge : forall x y, y > 0 -> x >= 0 -> x - ZEuclid.div x y >= 0.
intros.
unfold ZEuclid.div.
rewrite Z.sgn_pos. 2: solve [ auto with zarith ].
rewrite Z.mul_1_l.
apply Z.le_ge.
apply Zle_minus_le_0.
apply Z.div_le_upper_bound.
* apply Z.abs_pos. auto with zarith.
* rewrite Z.mul_comm.
  nia.
Qed.

Lemma ZEuclid_div_mod0 : forall x y, y <> 0 ->
  ZEuclid.modulo x y = 0 ->
  y * ZEuclid.div x y = x.
intros x y H1 H2.
rewrite Zplus_0_r_reverse at 1.
rewrite <- H2.
symmetry.
apply ZEuclid.div_mod.
assumption.
Qed.

#[export] Hint Resolve ZEuclid_div_pos ZEuclid_pos_div ZEuclid_div_ge ZEuclid_div_mod0 : sail.

Lemma Z_geb_ge n m : (n >=? m) = true <-> n >= m.
rewrite Z.geb_leb.
split.
* intro. apply Z.le_ge, Z.leb_le. assumption.
* intro. apply Z.ge_le in H. apply Z.leb_le. assumption.
Qed.


(*
Definition inline lt := (<)
Definition inline gt := (>)
Definition inline lteq := (<=)
Definition inline gteq := (>=)

val eq : forall a. Eq a => a -> a -> bool
Definition inline eq l r := (l = r)

val neq : forall a. Eq a => a -> a -> bool*)
Definition neq l r := (negb (l =? r)). (* Z only *)

(*let add_int l r := integerAdd l r
Definition add_signed l r := integerAdd l r
Definition sub_int l r := integerMinus l r
Definition mult_int l r := integerMult l r
Definition div_int l r := integerDiv l r
Definition div_nat l r := natDiv l r
Definition power_int_nat l r := integerPow l r
Definition power_int_int l r := integerPow l (Z.to_nat r)
Definition negate_int i := integerNegate i
Definition min_int l r := integerMin l r
Definition max_int l r := integerMax l r

Definition add_real l r := realAdd l r
Definition sub_real l r := realMinus l r
Definition mult_real l r := realMult l r
Definition div_real l r := realDiv l r
Definition negate_real r := realNegate r
Definition abs_real r := realAbs r
Definition power_real b e := realPowInteger b e*)

Definition print_endline (_ : string) : unit := tt.
Definition print (_ : string) : unit := tt.
Definition prerr_endline (_ : string) : unit := tt.
Definition prerr (_ : string) : unit := tt.
Definition print_int (_ : string) (_ : Z) : unit := tt.
Definition prerr_int (_ : string) (_ : Z) : unit := tt.
Definition putchar (_ : Z) : unit := tt.

Definition shl_int := Z.shiftl.
Definition shr_int := Z.shiftr.

(*
Definition or_bool l r := (l || r)
Definition and_bool l r := (l && r)
Definition xor_bool l r := xor l r
*)
Definition append_list {A:Type} (l : list A) r := l ++ r.
Definition length_list {A:Type} (xs : list A) := Z.of_nat (List.length xs).
Definition take_list {A:Type} n (xs : list A) := firstn (Z.to_nat n) xs.
Definition drop_list {A:Type} n (xs : list A) := skipn (Z.to_nat n) xs.
(*
val repeat : forall a. list a -> Z -> list a*)
Fixpoint repeat' {a} (xs : list a) n :=
  match n with
  | O => []
  | S n => xs ++ repeat' xs n
  end.
Lemma repeat'_length {a} {xs : list a} {n : nat} : List.length (repeat' xs n) = (n * List.length xs)%nat.
induction n.
* reflexivity.
* simpl.
  rewrite app_length.
  auto with arith.
Qed.
Definition repeat {a} (xs : list a) (n : Z) :=
  if n <? 0 then []
  else repeat' xs (Z.to_nat n).
Lemma repeat_length {a} {xs : list a} {n : Z} (H : n >= 0) : (List.length (repeat xs n) = (Z.to_nat n) * List.length xs)%nat.
unfold repeat.
apply Z.ge_le in H.
rewrite <- Z.ltb_ge in H.
rewrite H.
apply repeat'_length.
Qed.
Lemma repeat_length_list {a} {xs : list a} {n : Z} (H : n >= 0) : length_list (repeat xs n) = n * length_list xs.
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

(*declare {isabelle} termination_argument repeat = automatic

Definition duplicate_to_list bit length := repeat [bit] length

Fixpoint replace bs (n : Z) b' := match bs with
  | [] => []
  | b :: bs =>
     if n = 0 then b' :: bs
              else b :: replace bs (n - 1) b'
  end
declare {isabelle} termination_argument replace = automatic

Definition upper n := n

(* Modulus operation corresponding to quot below -- result
   has sign of dividend. *)
Definition hardware_mod (a: Z) (b:Z) : Z :=
  let m := (abs a) mod (abs b) in
  if a < 0 then ~m else m

(* There are different possible answers for integer divide regarding
rounding behaviour on negative operands. Positive operands always
round down so derive the one we want (trucation towards zero) from
that *)
Definition hardware_quot (a:Z) (b:Z) : Z :=
  let q := (abs a) / (abs b) in
  if ((a<0) = (b<0)) then
    q  (* same sign -- result positive *)
  else
    ~q (* different sign -- result negative *)

Definition max_64u := (integerPow 2 64) - 1
Definition max_64  := (integerPow 2 63) - 1
Definition min_64  := 0 - (integerPow 2 63)
Definition max_32u := (4294967295 : Z)
Definition max_32  := (2147483647 : Z)
Definition min_32  := (0 - 2147483648 : Z)
Definition max_8   := (127 : Z)
Definition min_8   := (0 - 128 : Z)
Definition max_5   := (31 : Z)
Definition min_5   := (0 - 32 : Z)
*)

(* just_list takes a list of maybes and returns Some xs if all elements have
   a value, and None if one of the elements is None. *)
(*val just_list : forall a. list (option a) -> option (list a)*)
Fixpoint just_list {A} (l : list (option A)) := match l with
  | [] => Some []
  | (x :: xs) =>
    match (x, just_list xs) with
      | (Some x, Some xs) => Some (x :: xs)
      | (_, _) => None
    end
  end.
(*declare {isabelle} termination_argument just_list = automatic

lemma just_list_spec:
  ((forall xs. (just_list xs = None) <-> List.elem None xs) &&
   (forall xs es. (just_list xs = Some es) <-> (xs = List.map Some es)))*)

Lemma just_list_length {A} : forall (l : list (option A)) (l' : list A),
  Some l' = just_list l -> List.length l = List.length l'.
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
induction l.
* simpl. split. congruence. tauto.
* simpl. destruct (x =? a) eqn:H.
  + rewrite Z.eqb_eq in H. subst. tauto.
  + rewrite Z.eqb_neq in H. split.
    - intro Heq. right. apply IHl. assumption.
    - intros [bad | good]. congruence. apply IHl. assumption.
Qed.

(*** Bits *)
Inductive bitU := B0 | B1 | BU.

Scheme Equality for bitU.
Definition eq_bit := bitU_beq.

#[export] Instance dummy_bitU : Inhabited bitU := {
  inhabitant := BU
}.

Definition showBitU b :=
match b with
  | B0 => "O"
  | B1 => "I"
  | BU => "U"
end%string.

Definition bitU_char b :=
match b with
| B0 => "0"
| B1 => "1"
| BU => "?"
end%char.

(*instance (Show bitU)
  let show := showBitU
end*)

Class BitU (a : Type) : Type := {
  to_bitU : a -> bitU;
  of_bitU : bitU -> a
}.

#[export] Instance bitU_BitU : (BitU bitU) := {
  to_bitU b := b;
  of_bitU b := b
}.

Definition bool_of_bitU bu := match bu with
  | B0 => Some false
  | B1 => Some true
  | BU => None
  end.

Definition bitU_of_bool (b : bool) := if b then B1 else B0.

(*Instance bool_BitU : (BitU bool) := {
  to_bitU := bitU_of_bool;
  of_bitU := bool_of_bitU
}.*)

Definition cast_bit_bool := bool_of_bitU.
(*
Definition bit_lifted_of_bitU bu := match bu with
  | B0 => Bitl_zero
  | B1 => Bitl_one
  | BU => Bitl_undef
  end.

Definition bitU_of_bit := function
  | Bitc_zero => B0
  | Bitc_one  => B1
  end.

Definition bit_of_bitU := function
  | B0 => Bitc_zero
  | B1 => Bitc_one
  | BU => failwith "bit_of_bitU: BU"
  end.

Definition bitU_of_bit_lifted := function
  | Bitl_zero => B0
  | Bitl_one  => B1
  | Bitl_undef => BU
  | Bitl_unknown => failwith "bitU_of_bit_lifted Bitl_unknown"
  end.
*)
Definition not_bit b :=
match b with
  | B1 => B0
  | B0 => B1
  | BU => BU
  end.

(*val is_one : Z -> bitU*)
Definition is_one (i : Z) :=
  if i =? 1 then B1 else B0.

Definition binop_bit op x y :=
  match (x, y) with
  | (BU,_) => BU (*Do we want to do this or to respect | of I and & of B0 rules?*)
  | (_,BU) => BU (*Do we want to do this or to respect | of I and & of B0 rules?*)
(*  | (x,y) => bitU_of_bool (op (bool_of_bitU x) (bool_of_bitU y))*)
  | (B0,B0) => bitU_of_bool (op false false)
  | (B0,B1) => bitU_of_bool (op false  true)
  | (B1,B0) => bitU_of_bool (op  true false)
  | (B1,B1) => bitU_of_bool (op  true  true)
  end.

(*val and_bit : bitU -> bitU -> bitU*)
Definition and_bit := binop_bit andb.

(*val or_bit : bitU -> bitU -> bitU*)
Definition or_bit := binop_bit orb.

(*val xor_bit : bitU -> bitU -> bitU*)
Definition xor_bit := binop_bit xorb.

(*val (&.) : bitU -> bitU -> bitU
Definition inline (&.) x y := and_bit x y

val (|.) : bitU -> bitU -> bitU
Definition inline (|.) x y := or_bit x y

val (+.) : bitU -> bitU -> bitU
Definition inline (+.) x y := xor_bit x y
*)

(*** Bool lists ***)

(*val bools_of_nat_aux : integer -> natural -> list bool -> list bool*)
Fixpoint bools_of_nat_aux len (x : nat) (acc : list bool) : list bool :=
  match len with
  | O => acc
  | S len' => bools_of_nat_aux len' (x / 2) ((if x mod 2 =? 1 then true else false) :: acc)
  end %nat.
  (*else (if x mod 2 = 1 then true else false) :: bools_of_nat_aux (x / 2)*)
(*declare {isabelle} termination_argument bools_of_nat_aux = automatic*)
Definition bools_of_nat len n := bools_of_nat_aux (Z.to_nat len) n [] (*List.reverse (bools_of_nat_aux n)*).

(*val nat_of_bools_aux : natural -> list bool -> natural*)
Fixpoint nat_of_bools_aux (acc : nat) (bs : list bool) : nat :=
  match bs with
  | [] => acc
  | true :: bs => nat_of_bools_aux ((2 * acc) + 1) bs
  | false :: bs => nat_of_bools_aux (2 * acc) bs
end.
(*declare {isabelle; hol} termination_argument nat_of_bools_aux = automatic*)
Definition nat_of_bools bs := nat_of_bools_aux 0 bs.

(*val unsigned_of_bools : list bool -> integer*)
Definition unsigned_of_bools bs := Z.of_nat (nat_of_bools bs).

(*val signed_of_bools : list bool -> integer*)
Definition signed_of_bools bs :=
  match bs with
    | true :: _  => 0 - (1 + (unsigned_of_bools (List.map negb bs)))
    | false :: _ => unsigned_of_bools bs
    | [] => 0 (* Treat empty list as all zeros *)
  end.

(*val int_of_bools : bool -> list bool -> integer*)
Definition int_of_bools (sign : bool) bs := if sign then signed_of_bools bs else unsigned_of_bools bs.

(*val pad_list : forall 'a. 'a -> list 'a -> integer -> list 'a*)
Fixpoint pad_list_nat {a} (x : a) (xs : list a) n :=
  match n with
  | O => xs
  | S n' => pad_list_nat x (x :: xs) n'
  end.
(*declare {isabelle} termination_argument pad_list = automatic*)
Definition pad_list {a} x xs n := @pad_list_nat a x xs (Z.to_nat n).

Definition ext_list {a} pad len (xs : list a) :=
  let longer := len - (Z.of_nat (List.length xs)) in
  if longer <? 0 then skipn (Z.abs_nat (longer)) xs
  else pad_list pad xs longer.

(*let extz_bools len bs = ext_list false len bs*)
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
(*declare {isabelle; hol} termination_argument add_one_bool_ignore_overflow_aux = automatic*)

Definition add_one_bool_ignore_overflow bits :=
  List.rev (add_one_bool_ignore_overflow_aux (List.rev bits)).

(*** Bit lists ***)

(*val bits_of_nat_aux : natural -> list bitU*)
Fixpoint bits_of_nat_aux n x :=
  match n,x with
  | O,_ => []
  | _,O => []
  | S n, S _ => (if x mod 2 =? 1 then B1 else B0) :: bits_of_nat_aux n (x / 2)
  end%nat.
(**declare {isabelle} termination_argument bits_of_nat_aux = automatic*)
Definition bits_of_nat n := List.rev (bits_of_nat_aux n n).

(*val nat_of_bits_aux : natural -> list bitU -> natural*)
Fixpoint nat_of_bits_aux acc bs := match bs with
  | [] => Some acc
  | B1 :: bs => nat_of_bits_aux ((2 * acc) + 1) bs
  | B0 :: bs => nat_of_bits_aux (2 * acc) bs
  | BU :: bs => None
end%nat.
(*declare {isabelle} termination_argument nat_of_bits_aux = automatic*)
Definition nat_of_bits bits := nat_of_bits_aux 0 bits.

Definition not_bits := List.map not_bit.

Definition binop_bits op bsl bsr :=
  List.fold_right (fun '(bl, br) acc => binop_bit op bl br :: acc) [] (List.combine bsl bsr).
(*
Definition and_bits := binop_bits (&&)
Definition or_bits := binop_bits (||)
Definition xor_bits := binop_bits xor

val unsigned_of_bits : list bitU -> Z*)
Definition unsigned_of_bits bits :=
match just_list (List.map bool_of_bitU bits) with
| Some bs => Some (unsigned_of_bools bs)
| None => None
end.

(*val signed_of_bits : list bitU -> Z*)
Definition signed_of_bits bits :=
  match just_list (List.map bool_of_bitU bits) with
  | Some bs => Some (signed_of_bools bs)
  | None => None
  end.

(*val int_of_bits : bool -> list bitU -> maybe integer*)
Definition int_of_bits (sign : bool) bs :=
 if sign then signed_of_bits bs else unsigned_of_bits bs.

(*val pad_bitlist : bitU -> list bitU -> Z -> list bitU*)
Fixpoint pad_bitlist_nat (b : bitU) bits n :=
match n with
| O => bits
| S n' => pad_bitlist_nat b (b :: bits) n'
end.
Definition pad_bitlist b bits n := pad_bitlist_nat b bits (Z.to_nat n). (* Negative n will come out as 0 *)
(*  if n <= 0 then bits else pad_bitlist b (b :: bits) (n - 1).
declare {isabelle} termination_argument pad_bitlist = automatic*)

Definition ext_bits pad len bits :=
  let longer := len - (Z.of_nat (List.length bits)) in
  if longer <? 0 then skipn (Z.abs_nat longer) bits
  else pad_bitlist pad bits longer.

Definition extz_bits len bits := ext_bits B0 len bits.

Definition exts_bits len bits :=
  match bits with
  | b :: _ => ext_bits b len bits
  | _ => ext_bits B0 len bits
  end.

Fixpoint add_one_bit_ignore_overflow_aux bits := match bits with
  | [] => []
  | B0 :: bits => B1 :: bits
  | B1 :: bits => B0 :: add_one_bit_ignore_overflow_aux bits
  | BU :: _ => dummy bits (*failwith "add_one_bit_ignore_overflow: undefined bit"*)
end.
(*declare {isabelle} termination_argument add_one_bit_ignore_overflow_aux = automatic*)

Definition add_one_bit_ignore_overflow bits :=
  rev (add_one_bit_ignore_overflow_aux (rev bits)).

Definition bitlist_of_int n :=
  let bits_abs := B0 :: bits_of_nat (Z.abs_nat n) in
  if n >=? 0 then bits_abs
  else add_one_bit_ignore_overflow (not_bits bits_abs).

Definition bits_of_int len n := exts_bits len (bitlist_of_int n).

(*val arith_op_bits :
  (integer -> integer -> integer) -> bool -> list bitU -> list bitU -> list bitU*)
Definition arith_op_bits (op : Z -> Z -> Z) (sign : bool) l r :=
  match (int_of_bits sign l, int_of_bits sign r) with
    | (Some li, Some ri) => bits_of_int (length_list l) (op li ri)
    | (_, _) => repeat [BU] (length_list l)
  end.


Definition char_of_nibble x :=
  match x with
  | (B0, B0, B0, B0) => Some "0"%char
  | (B0, B0, B0, B1) => Some "1"%char
  | (B0, B0, B1, B0) => Some "2"%char
  | (B0, B0, B1, B1) => Some "3"%char
  | (B0, B1, B0, B0) => Some "4"%char
  | (B0, B1, B0, B1) => Some "5"%char
  | (B0, B1, B1, B0) => Some "6"%char
  | (B0, B1, B1, B1) => Some "7"%char
  | (B1, B0, B0, B0) => Some "8"%char
  | (B1, B0, B0, B1) => Some "9"%char
  | (B1, B0, B1, B0) => Some "A"%char
  | (B1, B0, B1, B1) => Some "B"%char
  | (B1, B1, B0, B0) => Some "C"%char
  | (B1, B1, B0, B1) => Some "D"%char
  | (B1, B1, B1, B0) => Some "E"%char
  | (B1, B1, B1, B1) => Some "F"%char
  | _ => None
  end.

Fixpoint hexstring_of_bits bs := match bs with
  | b1 :: b2 :: b3 :: b4 :: bs =>
     let n := char_of_nibble (b1, b2, b3, b4) in
     let s := hexstring_of_bits bs in
     match (n, s) with
     | (Some n, Some s) => Some (String n s)
     | _ => None
     end
  | [] => Some EmptyString
  | _ => None
  end%string.

Fixpoint binstring_of_bits bs := match bs with
  | b :: bs => String (bitU_char b) (binstring_of_bits bs)
  | [] => EmptyString
  end.

Definition show_bitlist bs :=
  match hexstring_of_bits bs with
  | Some s => String "0" (String "x" s)
  | None => String "0" (String "b" (binstring_of_bits bs))
  end.

(*** List operations *)
(*
Definition inline (^^) := append_list

val subrange_list_inc : forall a. list a -> Z -> Z -> list a*)
Definition subrange_list_inc {A} (xs : list A) i j :=
  let toJ := firstn (Z.to_nat j + 1) xs in
  let fromItoJ := skipn (Z.to_nat i) toJ in
  fromItoJ.

(*val subrange_list_dec : forall a. list a -> Z -> Z -> list a*)
Definition subrange_list_dec {A} (xs : list A) i j :=
  let top := (length_list xs) - 1 in
  subrange_list_inc xs (top - i) (top - j).

(*val subrange_list : forall a. bool -> list a -> Z -> Z -> list a*)
Definition subrange_list {A} (is_inc : bool) (xs : list A) i j :=
 if is_inc then subrange_list_inc xs i j else subrange_list_dec xs i j.

Definition splitAt {A} n (l : list A) := (firstn n l, skipn n l).

(*val update_subrange_list_inc : forall a. list a -> Z -> Z -> list a -> list a*)
Definition update_subrange_list_inc {A} (xs : list A) i j xs' :=
  let (toJ,suffix) := splitAt (Z.to_nat j + 1) xs in
  let (prefix,_fromItoJ) := splitAt (Z.to_nat i) toJ in
  prefix ++ xs' ++ suffix.

(*val update_subrange_list_dec : forall a. list a -> Z -> Z -> list a -> list a*)
Definition update_subrange_list_dec {A} (xs : list A) i j xs' :=
  let top := (length_list xs) - 1 in
  update_subrange_list_inc xs (top - i) (top - j) xs'.

(*val update_subrange_list : forall a. bool -> list a -> Z -> Z -> list a -> list a*)
Definition update_subrange_list {A} (is_inc : bool) (xs : list A) i j xs' :=
  if is_inc then update_subrange_list_inc xs i j xs' else update_subrange_list_dec xs i j xs'.

Open Scope nat.
Fixpoint nth_in_range {A} (n:nat) (l:list A) : n < length l -> A.
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
intros until d. revert n.
induction l; intros n H.
* inversion H.
* destruct n.
  + reflexivity.
  + apply IHl.
Qed.

Lemma nth_Z_nat {A} {n} {xs : list A} :
  (0 <= n)%Z -> (n < length_list xs)%Z -> Z.to_nat n < length xs.
unfold length_list.
intros nonneg bounded.
rewrite Z2Nat.inj_lt in bounded; auto using Zle_0_nat.
rewrite Nat2Z.id in bounded.
assumption.
Qed.

Close Scope nat.

(*val access_list_inc : forall a. list a -> Z -> a*)
Definition access_list_inc {A} (xs : list A) `{Inhabited A} (n : Z) : A.
refine (
  let i := Z.to_nat n in
  if sumbool_of_bool ((0 <=? n) && (i <? List.length xs)%nat) then
    nth_in_range i xs _
  else dummy_value
).
rewrite Bool.andb_true_iff in e.
rewrite Nat.ltb_lt in e.
tauto.
Defined.

(*val access_list_dec : forall a. list a -> Z -> a*)
Definition access_list_dec {A} (xs : list A) n `{Inhabited A} : A :=
  let top := (length_list xs) - 1 in
  access_list_inc xs (top - n).

(*val access_list : forall a. bool -> list a -> Z -> a*)
Definition access_list {A} (is_inc : bool) (xs : list A) n `{Inhabited A} :=
  if is_inc then access_list_inc xs n else access_list_dec xs n.

Definition access_list_opt_inc {A} (xs : list A) n := nth_error xs (Z.to_nat n).

(*val access_list_dec : forall a. list a -> Z -> a*)
Definition access_list_opt_dec {A} (xs : list A) n :=
  let top := (length_list xs) - 1 in
  access_list_opt_inc xs (top - n).

(*val access_list : forall a. bool -> list a -> Z -> a*)
Definition access_list_opt {A} (is_inc : bool) (xs : list A) n :=
  if is_inc then access_list_opt_inc xs n else access_list_opt_dec xs n.

Definition list_update {A} (xs : list A) n x := firstn n xs ++ x :: skipn (S n) xs.

(*val update_list_inc : forall a. list a -> Z -> a -> list a*)
Definition update_list_inc {A} (xs : list A) n x := list_update xs (Z.to_nat n) x.

(*val update_list_dec : forall a. list a -> Z -> a -> list a*)
Definition update_list_dec {A} (xs : list A) n x :=
  let top := (length_list xs) - 1 in
  update_list_inc xs (top - n) x.

(*val update_list : forall a. bool -> list a -> Z -> a -> list a*)
Definition update_list {A} (is_inc : bool) (xs : list A) n x :=
  if is_inc then update_list_inc xs n x else update_list_dec xs n x.

(*Definition extract_only_element := function
  | [] => failwith "extract_only_element called for empty list"
  | [e] => e
  | _ => failwith "extract_only_element called for list with more elements"
end*)

(*** Machine words *)

Section MachineWords.

Import MachineWord.

(* ISA models tend to use integers for sizes, so Sail's bitvectors are integer
   indexed.  To avoid carrying around proofs that sizes are non-negative
   everywhere we define negative sized machine words to be a trivial value. *)

Definition mword (n : Z) :=
  match n with
  | Zneg _ => word 0
  | Z0 => word 0
  | Zpos p => word (Pos.to_nat p)
  end.

#[export] Instance dummy_mword {n} : Inhabited (mword n) := {
  inhabitant := match n with
  | Zpos _ => zeros _
  | _ => zeros _
  end
}.

Definition get_word {n} : mword n -> word (Z.to_nat n) :=
  match n with
  | Zneg _ => fun x => x
  | Z0 => fun x => x
  | Zpos p => fun x => x
  end.

Lemma get_word_inj {n} (w v : mword n) : get_word w = get_word v -> w = v.
destruct n; simpl; auto.
Qed.

Definition with_word {n} {P : Type -> Type} : (word (Z.to_nat n) -> P (word (Z.to_nat n))) -> mword n -> P (mword n) :=
match n with
| Zneg _ => fun f w => f w
| Z0 => fun f w => f w
| Zpos _ => fun f w => f w
end.

Definition to_word {n} : word (Z.to_nat n) -> mword n :=
  match n with
  | Zneg _ => fun _ => zeros _
  | Z0 => fun w => w
  | Zpos _ => fun w => w
  end.

Definition to_word_nat {n} (w : word n) : mword (Z.of_nat n) :=
  to_word (cast_nat w (eq_sym (Nat2Z.id n))).

(* Establish the relationship between to_word and to_word_nat, starting with some
   reasoning using dependent equality, but ultimately finishing with a directly
   usably plain equality result. *)

Lemma to_word_eq_dep m n (w : MachineWord.word (Z.to_nat m)) (v : MachineWord.word (Z.to_nat n)) :
  m > 0 ->
  n > 0 ->
  EqdepFacts.eq_dep Z (fun n => MachineWord.word (Z.to_nat n)) m w n v ->
  EqdepFacts.eq_dep Z mword _ (to_word w) _ (to_word v).
intros M N EQ.
destruct m,n; try lia.
inversion EQ. subst.
constructor.
Qed.

Lemma cast_nat_eq_dep T m n o (x : T m) (y : T n) EQ : EqdepFacts.eq_dep _ _ _ x _ y -> EqdepFacts.eq_dep _ _ _ x o (cast_nat y EQ).
intros.
subst.
rewrite cast_nat_refl.
assumption.
Qed.

Lemma Z_nat_eq_dep T m n (x : T (Z.to_nat m)) (y : T (Z.to_nat n)) : m > 0 -> n > 0 -> EqdepFacts.eq_dep nat T _ x _ y -> EqdepFacts.eq_dep Z (fun n => T (Z.to_nat n)) _ x _ y.
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

Lemma to_word_to_word_nat n (w : MachineWord.word (Z.to_nat n)) :
  n > 0 ->
  to_word w = autocast (to_word_nat w).
intros.
apply Eqdep_dec.eq_dep_eq_dec; auto using Z.eq_dec.
eapply EqdepFacts.eq_dep_trans. 2: apply autocast_eq_dep. 2: auto with zarith.
unfold to_word_nat.
apply to_word_eq_dep; auto with zarith.
apply Z_nat_eq_dep; auto with zarith.
apply cast_nat_eq_dep.
constructor.
Qed.

Definition word_to_mword {n} (w : word (Z.to_nat n)) : mword n :=
  to_word w.

(*val length_mword : forall a. mword a -> Z*)
Definition length_mword {n} (w : mword n) := n.

Definition access_mword_dec {m} (w : mword m) n := bitU_of_bool (get_bit (get_word w) (Z.to_nat n)).

(*val access_mword_inc : forall a. mword a -> Z -> bitU*)
Definition access_mword_inc {m} (w : mword m) n :=
  let top := (length_mword w) - 1 in
  access_mword_dec w (top - n).

(*Parameter access_mword : forall {a}, bool -> mword a -> Z -> bitU.*)
Definition access_mword {a} (is_inc : bool) (w : mword a) n :=
  if is_inc then access_mword_inc w n else access_mword_dec w n.

(*val update_mword_bool_dec : forall 'a. mword 'a -> integer -> bool -> mword 'a*)
Definition update_mword_bool_dec {a} (w : mword a) n b : mword a :=
  with_word (P := id) (fun w => set_bit w (Z.to_nat n) b) w.
Definition update_mword_dec {a} (w : mword a) n b :=
 match bool_of_bitU b with
 | Some bl => Some (update_mword_bool_dec w n bl)
 | None => None
 end.

(*val update_mword_inc : forall a. mword a -> Z -> bitU -> mword a*)
Definition update_mword_inc {a} (w : mword a) n b :=
  let top := (length_mword w) - 1 in
  update_mword_dec w (top - n) b.

(*Parameter update_mword : forall {a}, bool -> mword a -> Z -> bitU -> mword a.*)
Definition update_mword {a} (is_inc : bool) (w : mword a) n b :=
  if is_inc then update_mword_inc w n b else update_mword_dec w n b.

(*val int_of_mword : forall 'a. bool -> mword 'a -> integer*)
Definition int_of_mword {a} (sign : bool) (w : mword a) :=
  if sign then word_to_Z (get_word w) else Z.of_N (word_to_N (get_word w)).


(*val mword_of_int : forall a. Size a => Z -> Z -> mword a
Definition mword_of_int len n :=
  let w := wordFromInteger n in
  if (length_mword w = len) then w else failwith "unexpected word length"
*)
Definition mword_of_int {len} n : mword len :=
match len with
| Zneg _ => zeros _
| Z0 => Z_to_word 0 n
| Zpos p => Z_to_word (Pos.to_nat p) n
end.

(*
(* Translating between a type level number (itself n) and an integer *)

Definition size_itself_int x := Z.of_nat (size_itself x)

(* NB: the corresponding sail type is forall n. atom(n) -> itself(n),
   the actual integer is ignored. *)

val make_the_value : forall n. Z -> itself n
Definition inline make_the_value x := the_value
*)

Definition mword_to_N {n} (w : mword n) : N :=
  word_to_N (get_word w).

Lemma word_to_N_cast_nat {m n w} {E : m = n} :
  word_to_N (cast_nat w E) = word_to_N w.
subst.
rewrite cast_nat_refl.
reflexivity.
Qed.

Lemma mword_to_N_cast_Z {m n w} {E : m = n} :
  mword_to_N (cast_Z w E) = mword_to_N w.
subst.
rewrite cast_Z_refl.
reflexivity.
Qed.

Definition mword_to_bools {n} (w : mword n) : list bool := word_to_bools (get_word w).
Definition bools_to_mword (l : list bool) : mword (length_list l) := to_word_nat (bools_to_word l).

Definition eq_vec_dec {n} : forall (x y : mword n), {x = y} + {x <> y} :=
  match n with
  | Z0 => @MachineWord.eq_dec _
  | Zpos m => @MachineWord.eq_dec _
  | Zneg m => @MachineWord.eq_dec _
  end.

End MachineWords.

(* Some useful tactics left over from when we did constraint solving. *)

Lemma lift_bool_exists (l r : bool) (P : bool -> Prop) :
  (l = r -> exists x, P x) ->
  (exists x, l = r -> P x).
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

(*** Bytes and addresses *)

Definition memory_byte := list bitU.

(*val byte_chunks : forall a. list a -> option (list (list a))*)
Fixpoint byte_chunks {a} (bs : list a) := match bs with
  | [] => Some []
  | a::b::c::d::e::f::g::h::rest =>
     match byte_chunks rest with
     | None => None
     | Some rest => Some ([a;b;c;d;e;f;g;h] :: rest)
     end
  | _ => None
end.
(*declare {isabelle} termination_argument byte_chunks = automatic*)

Definition bits_of {n} (v : mword n) := List.map bitU_of_bool (mword_to_bools v).
Definition of_bits {n} v : option (mword n) :=
  match just_list (List.map bool_of_bitU v) with
  | Some bl =>
    match Z.eq_dec (length_list bl) n with
    | left H => Some (cast_Z (bools_to_mword bl) H)
    | right _ => None
    end
  | None => None
  end.
Definition of_bools {n} v : mword n := autocast (bools_to_mword v).

(*val bytes_of_bits : forall a. Bitvector a => a -> option (list memory_byte)*)
Definition bytes_of_bits {n} (bs : mword n) := byte_chunks (bits_of bs).

(*val bits_of_bytes : forall a. Bitvector a => list memory_byte -> a*)
Definition bits_of_bytes (bs : list memory_byte) : list bitU := List.concat (List.map (List.map to_bitU) bs).

Definition mem_bytes_of_bits {n} (bs : mword n) := option_map (@rev (list bitU)) (bytes_of_bits bs).
Definition bits_of_mem_bytes (bs : list memory_byte) := bits_of_bytes (List.rev bs).

(*val bitv_of_byte_lifteds : list Sail_impl_base.byte_lifted -> list bitU
Definition bitv_of_byte_lifteds v :=
  foldl (fun x (Byte_lifted y) => x ++ (List.map bitU_of_bit_lifted y)) [] v

val bitv_of_bytes : list Sail_impl_base.byte -> list bitU
Definition bitv_of_bytes v :=
  foldl (fun x (Byte y) => x ++ (List.map bitU_of_bit y)) [] v

val byte_lifteds_of_bitv : list bitU -> list byte_lifted
Definition byte_lifteds_of_bitv bits :=
  let bits := List.map bit_lifted_of_bitU bits in
  byte_lifteds_of_bit_lifteds bits

val bytes_of_bitv : list bitU -> list byte
Definition bytes_of_bitv bits :=
  let bits := List.map bit_of_bitU bits in
  bytes_of_bits bits

val bit_lifteds_of_bitUs : list bitU -> list bit_lifted
Definition bit_lifteds_of_bitUs bits := List.map bit_lifted_of_bitU bits

val bit_lifteds_of_bitv : list bitU -> list bit_lifted
Definition bit_lifteds_of_bitv v := bit_lifteds_of_bitUs v


val address_lifted_of_bitv : list bitU -> address_lifted
Definition address_lifted_of_bitv v :=
  let byte_lifteds := byte_lifteds_of_bitv v in
  let maybe_address_integer :=
    match (maybe_all (List.map byte_of_byte_lifted byte_lifteds)) with
    | Some bs => Some (integer_of_byte_list bs)
    | _ => None
    end in
  Address_lifted byte_lifteds maybe_address_integer

val bitv_of_address_lifted : address_lifted -> list bitU
Definition bitv_of_address_lifted (Address_lifted bs _) := bitv_of_byte_lifteds bs

val address_of_bitv : list bitU -> address
Definition address_of_bitv v :=
  let bytes := bytes_of_bitv v in
  address_of_byte_list bytes*)

Fixpoint reverse_endianness_list (bits : list bitU) :=
  match bits with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: t =>
    reverse_endianness_list t ++ firstn 8 bits
  | _ => bits
  end.

(*** Registers *)

Definition register_field := string.
Definition register_field_index : Type := string * (Z * Z). (* name, start and end *)

Inductive register :=
  | Register : string * (* name *)
               Z * (* length *)
               Z * (* start index *)
               bool * (* is increasing *)
               list register_field_index
               -> register
  | UndefinedRegister : Z -> register (* length *)
  | RegisterPair : register * register -> register.

Record register_ref regstate regval a :=
   { name : string;
     (*is_inc : bool;*)
     read_from : regstate -> a;
     write_to : a -> regstate -> regstate;
     of_regval : regval -> option a;
     regval_of : a -> regval }.
Notation "{[ r 'with' 'name' := e ]}" := ({| name := e; read_from := read_from r; write_to := write_to r; of_regval := of_regval r; regval_of := regval_of r |}).
Notation "{[ r 'with' 'read_from' := e ]}" := ({| read_from := e; name := name r; write_to := write_to r; of_regval := of_regval r; regval_of := regval_of r |}).
Notation "{[ r 'with' 'write_to' := e ]}" := ({| write_to := e; name := name r; read_from := read_from r; of_regval := of_regval r; regval_of := regval_of r |}).
Notation "{[ r 'with' 'of_regval' := e ]}" := ({| of_regval := e; name := name r; read_from := read_from r; write_to := write_to r; regval_of := regval_of r |}).
Notation "{[ r 'with' 'regval_of' := e ]}" := ({| regval_of := e; name := name r; read_from := read_from r; write_to := write_to r; of_regval := of_regval r |}).
Arguments name [_ _ _].
Arguments read_from [_ _ _].
Arguments write_to [_ _ _].
Arguments of_regval [_ _ _].
Arguments regval_of [_ _ _].

(* Remember that these inhabitants are not used by well typed Sail
code, so it doesn't matter that it's not useful. *)
#[export] Instance dummy_register_ref {T regstate regval} `{Inhabited T} `{Inhabited regval} : Inhabited (register_ref regstate regval T) := {
  inhabitant := {| name := ""; read_from := fun _ => dummy_value; write_to := fun _ s => s; of_regval := fun _ => None; regval_of := fun _ => dummy_value |}
}.

(* Register accessors: pair of functions for reading and writing register values *)
Definition register_accessors regstate regval : Type :=
  ((string -> regstate -> option regval) *
   (string -> regval -> regstate -> option regstate)).

Record field_ref regtype a :=
   { field_name : string;
     field_start : Z;
     field_is_inc : bool;
     get_field : regtype -> a;
     set_field : regtype -> a -> regtype }.
Arguments field_name [_ _].
Arguments field_start [_ _].
Arguments field_is_inc [_ _].
Arguments get_field [_ _].
Arguments set_field [_ _].

(*
(*let name_of_reg := function
  | Register name _ _ _ _ => name
  | UndefinedRegister _ => failwith "name_of_reg UndefinedRegister"
  | RegisterPair _ _ => failwith "name_of_reg RegisterPair"
end

Definition size_of_reg := function
  | Register _ size _ _ _ => size
  | UndefinedRegister size => size
  | RegisterPair _ _ => failwith "size_of_reg RegisterPair"
end

Definition start_of_reg := function
  | Register _ _ start _ _ => start
  | UndefinedRegister _ => failwith "start_of_reg UndefinedRegister"
  | RegisterPair _ _ => failwith "start_of_reg RegisterPair"
end

Definition is_inc_of_reg := function
  | Register _ _ _ is_inc _ => is_inc
  | UndefinedRegister _ => failwith "is_inc_of_reg UndefinedRegister"
  | RegisterPair _ _ => failwith "in_inc_of_reg RegisterPair"
end

Definition dir_of_reg := function
  | Register _ _ _ is_inc _ => dir_of_bool is_inc
  | UndefinedRegister _ => failwith "dir_of_reg UndefinedRegister"
  | RegisterPair _ _ => failwith "dir_of_reg RegisterPair"
end

Definition size_of_reg_nat reg := Z.to_nat (size_of_reg reg)
Definition start_of_reg_nat reg := Z.to_nat (start_of_reg reg)

val register_field_indices_aux : register -> register_field -> option (Z * Z)
Fixpoint register_field_indices_aux register rfield :=
  match register with
  | Register _ _ _ _ rfields => List.lookup rfield rfields
  | RegisterPair r1 r2 =>
      let m_indices := register_field_indices_aux r1 rfield in
      if isSome m_indices then m_indices else register_field_indices_aux r2 rfield
  | UndefinedRegister _ => None
  end

val register_field_indices : register -> register_field -> Z * Z
Definition register_field_indices register rfield :=
  match register_field_indices_aux register rfield with
  | Some indices => indices
  | None => failwith "Invalid register/register-field combination"
  end

Definition register_field_indices_nat reg regfield=
  let (i,j) := register_field_indices reg regfield in
  (Z.to_nat i,Z.to_nat j)*)

(*let rec external_reg_value reg_name v :=
  let (internal_start, external_start, direction) :=
    match reg_name with
     | Reg _ start size dir =>
        (start, (if dir = D_increasing then start else (start - (size +1))), dir)
     | Reg_slice _ reg_start dir (slice_start, _) =>
        ((if dir = D_increasing then slice_start else (reg_start - slice_start)),
         slice_start, dir)
     | Reg_field _ reg_start dir _ (slice_start, _) =>
        ((if dir = D_increasing then slice_start else (reg_start - slice_start)),
         slice_start, dir)
     | Reg_f_slice _ reg_start dir _ _ (slice_start, _) =>
        ((if dir = D_increasing then slice_start else (reg_start - slice_start)),
         slice_start, dir)
     end in
  let bits := bit_lifteds_of_bitv v in
  <| rv_bits           := bits;
     rv_dir            := direction;
     rv_start          := external_start;
     rv_start_internal := internal_start |>

val internal_reg_value : register_value -> list bitU
Definition internal_reg_value v :=
  List.map bitU_of_bit_lifted v.rv_bits
         (*(Z.of_nat v.rv_start_internal)
         (v.rv_dir = D_increasing)*)


Definition external_slice (d:direction) (start:nat) ((i,j):(nat*nat)) :=
  match d with
  (*This is the case the thread/concurrecny model expects, so no change needed*)
  | D_increasing => (i,j)
  | D_decreasing => let slice_i = start - i in
                    let slice_j = (i - j) + slice_i in
                    (slice_i,slice_j)
  end *)

(* TODO
Definition external_reg_whole r :=
  Reg (r.name) (Z.to_nat r.start) (Z.to_nat r.size) (dir_of_bool r.is_inc)

Definition external_reg_slice r (i,j) :=
  let start := Z.to_nat r.start in
  let dir := dir_of_bool r.is_inc in
  Reg_slice (r.name) start dir (external_slice dir start (i,j))

Definition external_reg_field_whole reg rfield :=
  let (m,n) := register_field_indices_nat reg rfield in
  let start := start_of_reg_nat reg in
  let dir := dir_of_reg reg in
  Reg_field (name_of_reg reg) start dir rfield (external_slice dir start (m,n))

Definition external_reg_field_slice reg rfield (i,j) :=
  let (m,n) := register_field_indices_nat reg rfield in
  let start := start_of_reg_nat reg in
  let dir := dir_of_reg reg in
  Reg_f_slice (name_of_reg reg) start dir rfield
              (external_slice dir start (m,n))
              (external_slice dir start (i,j))*)

(*val external_mem_value : list bitU -> memory_value
Definition external_mem_value v :=
  byte_lifteds_of_bitv v $> List.reverse

val internal_mem_value : memory_value -> list bitU
Definition internal_mem_value bytes :=
  List.reverse bytes $> bitv_of_byte_lifteds*)
*)

(* The choice operations in the monads operate on a small selection of base
   types.  Normally, -undefined_gen is used to construct functions for more
   complex types. *)

Inductive ChooseType : Type :=
  | ChooseBool | ChooseBit | ChooseInt | ChooseNat | ChooseReal | ChooseString
  | ChooseRange (lo hi : Z) | ChooseBitvector (n:Z).
Scheme Equality for ChooseType.
Definition choose_type ty :=
  match ty with
  | ChooseBool => bool | ChooseBit => bitU | ChooseInt => Z | ChooseNat => Z
  | ChooseReal => R | ChooseString => string
  | ChooseRange _ _ => Z | ChooseBitvector n => mword n
  end.

(* The property that is expected to hold of the chosen value. *)
Definition choose_prop ty : choose_type ty -> Prop :=
  match ty with
  | ChooseBool
  | ChooseBit
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
destruct ty; simpl; constructor; apply inhabitant.
Defined.

(*val foreach : forall a vars.
  (list a) -> vars -> (a -> vars -> vars) -> vars*)
Fixpoint foreach {a Vars} (l : list a) (vars : Vars) (body : a -> Vars -> Vars) : Vars :=
match l with
| [] => vars
| (x :: xs) => foreach xs (body x vars) body
end.

(*declare {isabelle} termination_argument foreach = automatic

val index_list : Z -> Z -> Z -> list Z*)
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

(*val while : forall vars. vars -> (vars -> bool) -> (vars -> vars) -> vars
Fixpoint while vars cond body :=
  if cond vars then while (body vars) cond body else vars

val until : forall vars. vars -> (vars -> bool) -> (vars -> vars) -> vars
Fixpoint until vars cond body :=
  let vars := body vars in
  if cond vars then vars else until (body vars) cond body


Definition assert' b msg_opt :=
  let msg := match msg_opt with
  | Some msg => msg
  | None  => "unspecified error"
  end in
  if b then () else failwith msg

(* convert numbers unsafely to naturals *)

class (ToNatural a) val toNatural : a -> natural end
(* eta-expanded for Isabelle output, otherwise it breaks *)
instance (ToNatural Z) let toNatural := (fun n => naturalFromInteger n) end
instance (ToNatural int)     let toNatural := (fun n => naturalFromInt n)     end
instance (ToNatural nat)     let toNatural := (fun n => naturalFromNat n)     end
instance (ToNatural natural) let toNatural := (fun n => n)                    end

Definition toNaturalFiveTup (n1,n2,n3,n4,n5) :=
  (toNatural n1,
   toNatural n2,
   toNatural n3,
   toNatural n4,
   toNatural n5)

(* Let the following types be generated by Sail per spec, using either bitlists
   or machine words as bitvector representation *)
(*type regfp :=
  | RFull of (string)
  | RSlice of (string * Z * Z)
  | RSliceBit of (string * Z)
  | RField of (string * string)

type niafp :=
  | NIAFP_successor
  | NIAFP_concrete_address of vector bitU
  | NIAFP_indirect_address

(* only for MIPS *)
type diafp :=
  | DIAFP_none
  | DIAFP_concrete of vector bitU
  | DIAFP_reg of regfp

Definition regfp_to_reg (reg_info : string -> option string -> (nat * nat * direction * (nat * nat))) := function
  | RFull name =>
     let (start,length,direction,_) := reg_info name None in
     Reg name start length direction
  | RSlice (name,i,j) =>
     let i = Z.to_nat i in
     let j = Z.to_nat j in
     let (start,length,direction,_) = reg_info name None in
     let slice = external_slice direction start (i,j) in
     Reg_slice name start direction slice
  | RSliceBit (name,i) =>
     let i = Z.to_nat i in
     let (start,length,direction,_) = reg_info name None in
     let slice = external_slice direction start (i,i) in
     Reg_slice name start direction slice
  | RField (name,field_name) =>
     let (start,length,direction,span) = reg_info name (Some field_name) in
     let slice = external_slice direction start span in
     Reg_field name start direction field_name slice
end

Definition niafp_to_nia reginfo = function
  | NIAFP_successor => NIA_successor
  | NIAFP_concrete_address v => NIA_concrete_address (address_of_bitv v)
  | NIAFP_indirect_address => NIA_indirect_address
end

Definition diafp_to_dia reginfo = function
  | DIAFP_none => DIA_none
  | DIAFP_concrete v => DIA_concrete_address (address_of_bitv v)
  | DIAFP_reg r => DIA_register (regfp_to_reg reginfo r)
end
*)
*)

(* TODO: make all Sail model preludes use the Z definitions directly, preferably by having them in the standard library *)
Definition min_atom (a : Z) (b : Z) : Z := Z.min a b.
Definition max_atom (a : Z) (b : Z) : Z := Z.max a b.


(*** Generic vectors *)

Definition vec (T:Type) (n:Z) := { l : list T & List.length l = Z.to_nat n }.
Definition vec_length {T n} (v : vec T n) := n.
Definition vec_access_dec {T n} (v : vec T n) m `{Inhabited T} : T :=
  access_list_dec (projT1 v) m.

Definition vec_access_inc {T n} (v : vec T n) m `{Inhabited T} : T :=
  access_list_inc (projT1 v) m.

(* "Negative" length vectors are treated as empty, but would normally be a mistake,
   so define an opaque default value for them so that it's obvious when one appears. *)
Definition dodgy_vec {T:Type} n (NEG: n >=? 0 = false) : vec T n.
refine (@existT _ _ [] _).
destruct n; try discriminate.
reflexivity.
Qed.

Lemma vec_init_ok {T} {n} {t : T} : n >=? 0 = true -> Datatypes.length (repeat [t] n) = Z.to_nat n.
intro GE.
rewrite repeat_length.
- simpl.
  apply Nat.mul_1_r.
- auto with zarith.
Qed.

Definition vec_init {T} (t : T) `{Inhabited T} (n : Z) : vec T n :=
  match sumbool_of_bool (n >=? 0) with
  | left GE => @existT _ _ (repeat [t] n) (vec_init_ok GE)
  | right NGE => dodgy_vec n NGE
  end.

#[export] Instance dummy_vec {T:Type} `{Inhabited T} n : Inhabited (vec T n) := {| inhabitant := vec_init inhabitant n |}.

Definition vec_concat {T m n} `{Inhabited T} (v : vec T m) (w : vec T n) : vec T (m + n).
refine (
  if sumbool_of_bool ((m >=? 0) && (n >=? 0)) then
     @existT _ _ (projT1 v ++ projT1 w) _
  else dummy_value).
destruct v,w.
rewrite app_length.
rewrite Z2Nat.inj_add; auto with zarith.
Defined.

Lemma skipn_length {A n} {l: list A} : (n <= List.length l -> List.length (skipn n l) = List.length l - n)%nat.
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
rewrite app_length.
rewrite firstn_length_le; only 2:lia.
cbn -[skipn].
rewrite skipn_length;
lia.
Qed.

Lemma vec_update_dec_lemma {T n} {v : vec T n} {m t} : 0 <=? m <? n = true -> length (update_list_dec (projT1 v) m t) = Z.to_nat n.
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

Lemma vec_update_inc_lemma {T n} {v : vec T n} {m t} : 0 <=? m <? n = true -> length (update_list_inc (projT1 v) m t) = Z.to_nat n.
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
refine (@existT _ _ (List.map f (projT1 v)) _).
destruct v as [l H].
cbn.
unfold length_list.
rewrite map_length.
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
refine (if List.list_eq_dec D (projT1 x) (projT1 y) then left _ else right _).
* apply eq_sigT_hprop; auto using UIP_nat.
* contradict n0. rewrite n0. reflexivity.
Defined.

Definition vec_of_list {A} n (l : list A) : option (vec A n).
refine (
  match sumbool_of_bool (n =? length_list l) with
  | left H => Some (@existT _ _ l _)
  | right _ => None
  end
).
symmetry.
apply Z.eqb_eq in H.
rewrite H.
unfold length_list.
rewrite Nat2Z.id.
reflexivity.
Defined.

Definition vec_of_list_len {A} (l : list A) : vec A (length_list l). 
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

Require Zquot.
Lemma Z_rem_really_nonneg : forall a b : Z, 0 <= a -> 0 <= Z.rem a b.
intros.
destruct (Z.eq_dec b 0).
+ subst. rewrite Zquot.Zrem_0_r. assumption.
+ auto using Z.rem_nonneg.
Qed.

Lemma Z_rem_pow_upper_bound : forall x x0 l,
0 <= x -> 2 ^ l <= x0 -> x0 <= 2 ^ l -> 0 <= l -> Z.rem x x0 < 2 ^ l.
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
lia.
Qed.
#[export] Hint Resolve sail_lt_ge : sail.

(* Override expensive unary exponential notation for binary, fill in sizes too *)
Notation "sz ''b' a" := (MachineWord.N_to_word sz (BinaryString.Raw.to_N a N0)) (at level 50).
Notation "''b' a" := (MachineWord.N_to_word _ (BinaryString.Raw.to_N a N0) :
                       mword (ltac:(let sz := eval cbv in (Z.of_nat (String.length a)) in exact sz)))
                     (at level 50, only parsing).
Notation "'Ox' a" := (MachineWord.N_to_word _ (HexString.Raw.to_N a N0) :
                       mword (ltac:(let sz := eval cbv in (4 * (Z.of_nat (String.length a))) in exact sz)))
                     (at level 50, only parsing).
