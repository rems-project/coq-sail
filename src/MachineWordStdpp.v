From Sail Require TypeCasts MachineWordInterface.
From stdpp Require Import base bitvector.definitions.
Require Import ZArith.
Require Import String.

Module MachineWord <: MachineWordInterface.MachineWordInterface.

Definition idx := N.

Definition Z_idx := Z.to_N.
Definition N_idx (n : N) := n.
Definition nat_idx := N.of_nat.
Hint Unfold Z_idx N_idx nat_idx : core.
Arguments Z_idx /.
Arguments N_idx /.
Arguments nat_idx /.

Definition idx_Z := Z.of_N.
Definition idx_N (n : N) := n.
Definition idx_nat := N.to_nat.
Arguments idx_Z /.
Arguments idx_N /.
Arguments idx_nat /.

Lemma Z_idx_Z n : n = Z_idx (idx_Z n).
Proof.
  simpl.
  rewrite N2Z.id.
  reflexivity.
Qed.
Lemma idx_Z_idx z : (z >= 0)%Z -> idx_Z (Z_idx z) = z.
Proof.
  intro GE.
  simpl.
  rewrite Z2N.id; auto with zarith.
Qed.
Lemma nat_idx_Z n : nat_idx n = Z_idx (Z.of_nat n).
Proof.
  simpl.
  rewrite <- Z_nat_N.
  rewrite Nat2Z.id.
  reflexivity.
Qed.
Lemma idx_N_Z_idx z : idx_N (Z_idx z) = Z.to_N z.
Proof.
  simpl.
  reflexivity.
Qed.

Definition cast_idx {T m n} := @TypeCasts.cast_N T m n.
Lemma cast_idx_refl n T (x : T n) (e : n = n) : cast_idx x e = x.
Proof.
  apply TypeCasts.cast_N_refl.
Qed.

Definition idx_S := N.succ.
Definition idx_add := N.add.
Definition idx_mul := N.mul.
Hint Unfold idx_S idx_add idx_mul : core.
Arguments idx_S /.
Arguments idx_add /.
Arguments idx_mul /.
Lemma Z_idx_S z : (z >= 0)%Z -> Z_idx (Z.succ z) = idx_S (Z_idx z).
Proof.
  simpl.
  intro GE.
  apply Z2N.inj_succ; lia.
Qed.

Definition word := bv.

Definition zeros n : word n := bv_0 n.

Definition get_bit [n] (w : word n) i : bool := Z.testbit (bv_unsigned w) (Z.of_N i).

Lemma get_bit_eq_nat : forall [n] (w v : word (nat_idx n)),
  (forall i, i < n -> get_bit w (nat_idx i) = get_bit v (nat_idx i)) -> w = v.
intros n w v H.
apply bv_eq.
unfold get_bit in *.
apply Z.bits_inj'.
intros m LE.
destruct (Z_lt_dec m (Z.of_nat n)).
* rewrite <- (Z2Nat.id m LE).
  rewrite <- nat_N_Z.
  apply H.
  Lia.lia.
* unfold nat_idx in *.
  rewrite !bv_unsigned_spec_high; auto; Lia.lia.
Qed.

Definition word_to_Z [n] (w : word n) : Z := bv_signed w.
Definition word_to_N [n] (w : word n) : N := Z.to_N (bv_unsigned w).
Definition Z_to_word n z : word n := Z_to_bv _ z.
Definition N_to_word n nn : word n := Z_to_bv _ (Z.of_N nn).

Lemma word_to_N_range : forall [n] (w : word n), (word_to_N w < 2 ^ idx_N n)%N.
unfold idx_N.
intros.
specialize (bv_unsigned_in_range _ w).
unfold bv_modulus.
intros [LE LT].

unfold word_to_N.
rewrite <- (N2Z.id (2 ^ n)).
rewrite <- Z2N.inj_lt;  Lia.lia.
Qed.

(* TODO: this proof is generic, should be shared *)
Lemma testbit_word_to_N_high : forall [n] (w: word n) i, (i >= n)%N ->
  N.testbit (word_to_N w) i = false.
intros.
specialize (word_to_N_range w).
generalize (word_to_N w) as m.
unfold idx_N.
intros.
destruct (N.testbit_spec m i) as [l [h [H1 H2]]].
destruct (N.testbit m i).
* simpl (N.b2n true) in H2. subst.
  assert (l + (1 + 2 * h) * 2 ^ i >= 2 ^ i)%N by Lia.lia.
  specialize (N.pow_le_mono_r 2 n i).
  Lia.lia.
* reflexivity.
Qed.

Lemma word_to_Z_range : forall [n] (w : word (N.succ n)), (- 2 ^ idx_Z n <= word_to_Z w < 2 ^ idx_Z n)%Z.
unfold idx_Z.
intros.
specialize (bv_signed_in_range _ w ltac:(Lia.lia)).
unfold bv_half_modulus, bv_modulus, word_to_Z.
rewrite N2Z.inj_succ.
rewrite Z.pow_succ_r; auto with zarith.

replace (2 * 2 ^ Z.of_N n / 2)%Z with (2 ^ Z.of_N n)%Z. 2: {
  rewrite Z.mul_comm.
  rewrite Z.div_mul; auto.
}
trivial.
Qed.

Definition ones n : word n := Z_to_bv _ (-1).

Definition word_to_bools [n] (w : word n) : list bool := List.rev (bv_to_bits w).
Definition bools_to_word (l : list bool) : word (nat_idx (List.length l)) := N_to_word (N.of_nat (List.length l)) (Ascii.N_of_digits (List.rev l)).

Lemma word_to_bools_length : forall [n] (w : word n), List.length (word_to_bools w) = idx_nat n.
intros.
unfold idx_nat.
unfold word_to_bools.
rewrite List.rev_length.
rewrite bv_to_bits_length.
reflexivity.
Qed.

Lemma nth_error_lookup {A} (l : list A) (i : nat) :
  base.lookup i l = List.nth_error l i.
destruct (List.nth_error l i) eqn:H.
* assert (i < Datatypes.length l) as LEN. {
    apply List.nth_error_Some.
    congruence.
  }
  destruct (list.nth_lookup_or_length l i a) as [E|E].
  - rewrite (List.nth_error_nth l i a H) in E.
    assumption.
  - contradict E.
    Lia.lia.
* apply list.lookup_ge_None.
  apply List.nth_error_None.
  assumption.
Qed.

Lemma nth_error_rev A (l : list A) i x :
  List.nth_error l i = Some x <-> List.nth_error (List.rev l) (List.length l - i - 1) = Some x /\ i < List.length l.
destruct (lt_dec i (List.length l)) as [H|H].
* rewrite List.nth_error_nth' with (d := x); auto.
  rewrite List.nth_error_nth' with (d := x). 2: {
    rewrite List.rev_length.
    Lia.lia.
  }
  rewrite List.rev_nth. 2: Lia.lia.
  replace (List.length l - S (List.length l - i - 1)) with i by Lia.lia.
  tauto.
* apply not_lt in H.
  specialize (List.nth_error_None l i) as H'.
  intuition; solve [congruence | Lia.lia].
Qed.

Lemma word_to_bools_get_bit : forall [n] (w : word n) (i : nat) x,
  List.nth_error (word_to_bools w) i = Some x <-> get_bit w (nat_idx (idx_nat n - i - 1)) = x /\ i < idx_nat n.
unfold nat_idx, idx_nat.
intros.
unfold word_to_bools, get_bit.
specialize (bv_to_bits_lookup_Some w (N.to_nat n - i - 1) x).
rewrite nth_error_lookup.
intro H.
rewrite nth_error_rev.
rewrite List.rev_involutive, List.rev_length.
rewrite bv_to_bits_length.
rewrite H.
rewrite nat_N_Z.
firstorder.
Lia.lia.
Qed.

Lemma word_to_bools_nth_Some : forall [n] (w : word n) (i : nat) x, idx_nat n > 0 ->
  List.nth_error (word_to_bools w) i = Some x <-> x = N.testbit (word_to_N w) (N.of_nat (idx_nat n - i - 1)) /\ i < idx_nat n.
unfold idx_nat.
intros.
rewrite word_to_bools_get_bit.
unfold get_bit, word_to_N.
rewrite <- (Z2N.id (bv_unsigned w)) at 1.
rewrite Z.testbit_of_N.
intuition.
firstorder using bv_unsigned_in_range.
Qed.

Lemma N_of_digits_limit l :
  (Ascii.N_of_digits l < 2 ^ N.of_nat (List.length l))%N.
induction l.
* simpl. Lia.lia.
* simpl (List.length _).
  rewrite Nnat.Nat2N.inj_succ.
  rewrite N.pow_succ_r'.
  simpl (Ascii.N_of_digits _).
  destruct (Ascii.N_of_digits l); destruct a; Lia.lia.
Qed.

Local Lemma nth_error_N_of_digits l i b :
  List.nth_error l i = Some b <-> N.testbit (Ascii.N_of_digits l) (N.of_nat i) = b /\ i < List.length l.
revert i.
induction l.
* intros. simpl. split.
  - intro H. apply List.nth_error_In in H. inversion H.
  - intros [_ H]. inversion H.
* destruct i.
  - destruct a; simpl; destruct (Ascii.N_of_digits l); simpl; intuition; auto using Nat.lt_0_succ; congruence.
  - rewrite Nnat.Nat2N.inj_succ.
    replace (Ascii.N_of_digits (a::l)) with (2 * Ascii.N_of_digits l + N.b2n a)%N. 2: {
      simpl Ascii.N_of_digits at 2.
      destruct (Ascii.N_of_digits l).
      + destruct a; simpl; Lia.lia.
      + destruct a; simpl; Lia.lia.
    }
    rewrite N.testbit_succ_r.
    specialize (IHl i).
    simpl.
    rewrite IHl.
    intuition; Lia.lia.
Qed.

Lemma bools_to_word_get_bit : forall l i b,
  List.nth_error l i = Some b <-> get_bit (bools_to_word l) (nat_idx (List.length l - i - 1)) = b /\ i < List.length l.
unfold nat_idx.
intros.
unfold bools_to_word, get_bit, N_to_word.
rewrite Z_to_bv_unsigned.
rewrite bv_wrap_small. 2: {
  split; [Lia.lia|].
  unfold bv_modulus.
  specialize (N_of_digits_limit (List.rev l)).
  rewrite List.rev_length.
  Lia.lia.
}
rewrite Z.testbit_of_N.
rewrite nth_error_rev.
specialize (nth_error_N_of_digits (List.rev l) (List.length l - i - 1) b).
rewrite List.rev_length.
assert (i < Datatypes.length l -> Datatypes.length l - i - 1 < Datatypes.length l) by Lia.lia.
intuition.
Qed.

Lemma bools_to_word_nth_Some : forall (l : list bool) i b,
  List.nth_error l i = Some b <-> b = N.testbit (word_to_N (bools_to_word l)) (N.of_nat (List.length l - i - 1)) /\ i < List.length l.
intros.
rewrite bools_to_word_get_bit.
unfold get_bit, word_to_N.
rewrite <- (Z2N.id (bv_unsigned (bools_to_word l))) at 1. 2: {
  specialize (bv_unsigned_in_range _ (bools_to_word l)).
  intuition.
}
rewrite Z.testbit_of_N.
intuition.
Qed.

Definition slice {m} n (w : word m) i : word n := bv_extract i _ w.
Definition update_slice {m n} (w : word m) i (v : word n) : word m :=
  bv_concat m
    (slice (m - n - i) w (i + n))
    (bv_concat (i+n) v (slice i w 0)).
Definition zero_extend {m} n (w : word m) : word n := bv_zero_extend _ w.
Definition sign_extend {m} n (w : word m) : word n := bv_sign_extend _ w.
Definition concat {m n} (w : word m) (v : word n) : word (m + n) := bv_concat _ w v.

Definition set_bit [n] (w : word n) i b : word n := update_slice w i (bool_to_bv (N.of_nat 1) b).

Definition and [n] (w v : word n) : word n := bv_and w v.
Definition  or [n] (w v : word n) : word n := bv_or w v.
Definition xor [n] (w v : word n) : word n := bv_xor w v.
Definition not [n] (w : word n) : word n := bv_not w.

Definition add [n] (w v : word n) : word n := bv_add w v.
Definition sub [n] (w v : word n) : word n := bv_sub w v.
Definition mul [n] (w v : word n) : word n := bv_mul w v.

Definition logical_shift_left  [n] (w : word n) i : word n := bv_shiftl w (N_to_word n i).
Definition logical_shift_right [n] (w : word n) i : word n := bv_shiftr w (N_to_word n i).
Definition arith_shift_right   [n] (w : word n) i : word n := bv_ashiftr w (N_to_word n i).

Fixpoint replicate m [n] (w : word n) : word (N.of_nat m * n) :=
  match m with
  | O => bv_0 0
  | S m' => bv_concat _ w (replicate m' w)
  end.

Definition eq_dec [n] (w v : word n) : {w = v} + {w <> v} := base.decide (w = v).

Definition eqb [n] (w v : word n) := if eq_dec w v then true else false.
Lemma eqb_true_iff {n} (w v : word n) : eqb w v = true <-> w = v.
unfold eqb.
destruct (eq_dec w v); split; congruence.
Qed.

Definition reverse_endian [n] (w : word n) : word n :=
  let bytes := bv_to_little_endian (Z.div (Z.of_N n) 8) 8 (bv_unsigned w) in
  Z_to_word n (little_endian_to_bv 8 (List.rev bytes)).

Definition word_to_binary_string [n] (w : word n) : String.string :=
  let bits := word_to_bools w in
  let digits := List.map (fun b : bool => if b then "1" else "0")%string bits in
  String.concat "" digits.

End MachineWord.
