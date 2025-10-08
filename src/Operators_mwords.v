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

Require Import TypeCasts Values Instances Prompt_monad Prompt MachineWord.
From Coq Require Import ZArith Lia Eqdep_dec.
Local Open Scope Z.

Definition autocast_m {rv rt e m n} {T : Z -> Type} `{H : Inhabited (T n)} (x : @monad rv rt (T m) e) : @monad rv rt (T n) e :=
  x >>= fun x => returnm (autocast x).

(*
(* Specialisation of operators to machine words *)

val access_vec_inc : forall 'a. Size 'a => mword 'a -> integer -> bitU*)
Definition access_vec_inc {a} : mword a -> Z -> bitU := access_mword_inc.

(*val access_vec_dec : forall 'a. Size 'a => mword 'a -> integer -> bitU*)
Definition access_vec_dec {a} : mword a -> Z -> bitU := access_mword_dec.

(*val update_vec_inc : forall 'a. Size 'a => mword 'a -> integer -> bitU -> mword 'a*)
(* TODO: probably ought to use a monadic version instead, but using bad default for
   type compatibility just now *)
Definition update_vec_inc {a} (w : mword a) i b : mword a :=
 opt_def w (update_mword_inc w i b).

(*val update_vec_dec : forall 'a. Size 'a => mword 'a -> integer -> bitU -> mword 'a*)
Definition update_vec_dec {a} (w : mword a) i b : mword a := opt_def w (update_mword_dec w i b).

Definition subrange_vec_dec {n} (v : mword n) m o : mword (m - o + 1) :=
  autocast (to_word_idx (MachineWord.slice (MachineWord.Z_idx (m - o + 1)) (get_word v) (MachineWord.Z_idx o))).

Definition subrange_vec_inc {n} (v : mword n) m o : mword (o - m + 1) := autocast (subrange_vec_dec v (n-1-m) (n-1-o)).

Definition update_subrange_vec_dec {n} (v : mword n) m o (w : mword (m - (o - 1))) : mword n :=
  autocast (to_word_idx (MachineWord.update_slice (get_word v) (MachineWord.Z_idx o) (get_word w))).

Definition update_subrange_vec_inc {n} (v : mword n) m o (w : mword (o - (m - 1))) : mword n := update_subrange_vec_dec v (n-1-m) (n-1-o) (autocast w).

(*val extz_vec : forall 'a 'b. Size 'a, Size 'b => integer -> mword 'a -> mword 'b*)
Definition extz_vec {a b} (n : Z) (v : mword a) : mword b :=
  to_word (MachineWord.zero_extend (MachineWord.Z_idx b) (get_word v)).

(*val exts_vec : forall 'a 'b. Size 'a, Size 'b => integer -> mword 'a -> mword 'b*)
Definition exts_vec {a b} (n : Z) (v : mword a) : mword b :=
  to_word (MachineWord.sign_extend (MachineWord.Z_idx b) (get_word v)).

Definition zero_extend {a} (v : mword a) (n : Z) : mword n := extz_vec n v.

Definition sign_extend {a} (v : mword a) (n : Z) : mword n := exts_vec n v.

Definition zeros (n : Z) : mword n :=
  match n with
  | Zneg p => MachineWord.zeros _
  | Z0 => MachineWord.zeros _
  | Zpos p => MachineWord.zeros _
  end.

Definition slice {n} (v : mword n) i len : mword len :=
  to_word (MachineWord.slice (MachineWord.Z_idx len) (get_word v) (MachineWord.Z_idx i)).

Definition vector_truncate {n} (v : mword n) (m : Z) : mword m := slice v 0 m.
Definition vector_truncateLSB {n} (v : mword n) (m : Z) : mword m := slice v (n - m) m.

(*val concat_vec : forall 'a 'b 'c. Size 'a, Size 'b, Size 'c => mword 'a -> mword 'b -> mword 'c*)
Definition concat_vec {a b} (w : mword a) (v : mword b) : mword (a + b) :=
 autocast (to_word_idx (MachineWord.concat (get_word w) (get_word v))).

(*val cons_vec : forall 'a 'b 'c. Size 'a, Size 'b => bitU -> mword 'a -> mword 'b*)
(*Definition cons_vec {a b} : bitU -> mword a -> mword b := cons_bv.*)

(*val bool_of_vec : mword ty1 -> bitU
Definition bool_of_vec := bool_of_bv

val cast_unit_vec : bitU -> mword ty1
Definition cast_unit_vec := cast_unit_bv

val vec_of_bit : forall 'a. Size 'a => integer -> bitU -> mword 'a
Definition vec_of_bit := bv_of_bit*)

Definition uint {a} (x : mword a) : Z := Z.of_N (MachineWord.word_to_N (get_word x)).

(* Demonstrate that uint has the range expected by the Sail type. *)
Lemma uint_range {a} (x : mword a) : a >= 0 -> 0 <= uint x <= 2 ^ a - 1.
intro a_ge_0.
split.
* apply N2Z.is_nonneg.
* unfold uint.
  assert (LELT: forall x y, x <= y - 1 <-> x < y) by lia.
  rewrite LELT.
  replace (2 ^ a) with (Z.of_N (2 ^ (Z.to_N a))). 2: {
    rewrite N2Z.inj_pow.
    rewrite Z2N.id; auto with zarith.
  }
  apply N2Z.inj_lt.
  rewrite <- (MachineWord.idx_N_Z_idx a).
  apply MachineWord.word_to_N_range.
Qed.

Definition sint {a} (x : mword a) : Z := MachineWord.word_to_Z (get_word x).

(* Demonstrate that sint has the range expected by the Sail type. *)
Lemma sint_range {a} (x : mword a) : a > 0 -> -(2^(a-1)) <= sint x <= 2 ^ (a-1) - 1.
intro a_gt_0.
unfold sint.
assert (LELT: forall x y, x <= y - 1 <-> x < y) by lia.
rewrite LELT.
set (n := a - 1).
generalize (get_word x).
rewrite <- (MachineWord.idx_Z_idx n); [ | lia].
replace a with (Z.succ n) by lia.
rewrite MachineWord.Z_idx_S; [ | lia].
apply MachineWord.word_to_Z_range.
Qed.

Lemma length_list_pos : forall {A} {l:list A}, 0 <= Z.of_nat (List.length l).
unfold length_list.
auto with zarith.
Qed.
#[export] Hint Resolve length_list_pos : sail.

Definition bool_of_bit b := match b with B0 => false | B1 => true | BU => dummy false end.

Definition vec_of_bits (l:list bitU) : mword (length_list l) := of_bools (List.map bool_of_bit l).
(*

val msb : forall 'a. Size 'a => mword 'a -> bitU
Definition msb := most_significant

val int_of_vec : forall 'a. Size 'a => bool -> mword 'a -> integer
Definition int_of_vec := int_of_bv

*)

Definition with_word' {n} (P : Type -> Type) : (forall n, MachineWord.word n -> P (MachineWord.word n)) -> mword n -> P (mword n) := fun f w => @with_word n _ (f (MachineWord.Z_idx n)) w.
Definition word_binop {n} (f : forall n, MachineWord.word n -> MachineWord.word n -> MachineWord.word n) : mword n -> mword n -> mword n := with_word' (fun x => x -> x) f.
Definition word_unop {n} (f : forall n, MachineWord.word n -> MachineWord.word n) : mword n -> mword n := with_word' (fun x => x) f.


Definition and_vec {n} : mword n -> mword n -> mword n := word_binop MachineWord.and.
Definition or_vec  {n} : mword n -> mword n -> mword n := word_binop MachineWord.or.
Definition xor_vec {n} : mword n -> mword n -> mword n := word_binop MachineWord.xor.
Definition not_vec {n} : mword n -> mword n := word_unop MachineWord.not.

Definition add_vec   {n} : mword n -> mword n -> mword n := word_binop MachineWord.add.
(*Definition sadd_vec  {n} : mword n -> mword n -> mword n := sadd_bv w.*)
Definition sub_vec   {n} : mword n -> mword n -> mword n := word_binop MachineWord.sub.
Definition mult_vec  {n m} (l : mword n) (r : mword n) : mword m :=
  word_binop MachineWord.mul (zero_extend l _) (zero_extend r _).
Definition mults_vec  {n m} (l : mword n) (r : mword n) : mword m :=
  word_binop MachineWord.mul (sign_extend l _) (sign_extend r _).

Definition add_vec_int   {a} (l : mword a) (r : Z) : mword a := add_vec l (mword_of_int r).
Definition sub_vec_int   {a} (l : mword a) (r : Z) : mword a := sub_vec l (mword_of_int r).

(* TODO: check/redefine behaviour on out-of-range n *)
Definition shiftl       {a} (v : mword a) n : mword a := with_word (P := id) (fun w => MachineWord.logical_shift_left w (MachineWord.Z_idx n)) v.
Definition shiftr       {a} (v : mword a) n : mword a := with_word (P := id) (fun w => MachineWord.logical_shift_right w (MachineWord.Z_idx n)) v.
Definition arith_shiftr {a} (v : mword a) n : mword a := with_word (P := id) (fun w => MachineWord.arith_shift_right w (MachineWord.Z_idx n)) v.

Definition replicate_bits {a} (w : mword a) (n : Z) : mword (a * n) :=
 if sumbool_of_bool (n >=? 0) then
   autocast (to_word_idx (MachineWord.replicate (Z.to_nat n) (get_word w)))
 else dummy_value.

Definition eq_vec  {n} (x : mword n) (y : mword n) : bool := MachineWord.eqb (get_word x) (get_word y).
Definition neq_vec {n} (x : mword n) (y : mword n) : bool := negb (eq_vec x y).

Lemma eq_vec_true_iff {n} (v w : mword n) :
  eq_vec v w = true <-> v = w.
unfold eq_vec.
rewrite MachineWord.eqb_true_iff.
split.
* apply get_word_inj.
* intros []. reflexivity.
Qed.

Lemma eq_vec_false_iff {n} (v w : mword n) :
  eq_vec v w = false <-> v <> w.
specialize (eq_vec_true_iff v w).
destruct (eq_vec v w); intuition congruence.
Qed.

Definition reverse_endianness {n} (bits : mword n) := with_word (P := id) (MachineWord.reverse_endian (n:=_)) bits.

Definition bools_of_int len n :=
  let w := MachineWord.Z_to_word (MachineWord.Z_idx len) n in
  MachineWord.word_to_bools w.

(* We hide this behind an eta expansion of n to prevent tactics that
   do too much computation (e.g., injection) from unfolding messily. *)
Definition get_slice_int' (len : Z) (n : Z) (lo : Z) : mword len :=
  if sumbool_of_bool (len >=? 0) then
    let hi := lo + len - 1 in
    let v : mword (hi + 1) := mword_of_int n in
    autocast (subrange_vec_dec v hi lo)
  else dummy_value.

Definition get_slice_int len n lo : mword len :=
  match n with
  | Zneg p => get_slice_int' len (Zneg p) lo
  | Z0 => get_slice_int' len Z0 lo
  | Zpos p => get_slice_int' len (Zpos p) lo
  end.

Lemma get_slice_int_eta len n lo : get_slice_int len n lo = get_slice_int' len n lo.
destruct n; reflexivity.
Qed.

Definition set_slice n m (v : mword n) x (w : mword m) : mword n :=
  update_subrange_vec_dec v (x + m - 1) x (autocast w).

Definition set_slice_int len n lo (v : mword len) : Z :=
  let hi := lo + len - 1 in
  (* We don't currently have a constraint on lo in the sail prelude, so let's
     avoid one here. *)
  if sumbool_of_bool (Z.gtb hi 0) then
    let bs : mword (hi + 1) := mword_of_int n in
    (int_of_mword true (update_subrange_vec_dec bs hi lo (autocast v)))
  else n.



Lemma slice_is_ok m (v : mword m) lo len
                  (H1 : 0 <= lo) (H2 : 0 < len) (H3: lo + len < m) :
  slice v lo len = autocast (subrange_vec_dec v (lo + len - 1) lo).
unfold slice, subrange_vec_dec.
replace (lo + len - 1 - lo + 1) with len by lia.
rewrite autocast_refl.
apply to_word_to_word_nat.
lia.
Qed.

Import ListNotations.
Definition count_leading_zeros {N : Z} (x : mword N) (* N >=? 1 *)
: Z (* n. (0 <=? n <=? N) *) :=
  foreach_Z_up 0 (N - 1) 1 N
    (fun i r =>
      (if ((eq_vec (vec_of_bits [access_vec_dec x i]  : mword 1) (vec_of_bits [B1]  : mword 1)))
       then 
            (Z.sub (Z.sub (length_mword x) i) 1)
       else r))
   .
Definition count_trailing_zeros {N : Z} (x : mword N) (* N >=? 1 *)
: Z (* n. (0 <=? n <=? N) *) :=
  foreach_Z_down (N - 1) 0 1 N
    (fun i r =>
      (if ((eq_vec (vec_of_bits [access_vec_dec x i]  : mword 1) (vec_of_bits [B1]  : mword 1)))
       then i
       else r))
   .

Definition prerr_bits {a} (s : string) (bs : mword a) : unit := tt.
Definition print_bits {a} (s : string) (bs : mword a) : unit := tt.
