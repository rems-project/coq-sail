Require Import ZArith.

Module Type MachineWordInterface.

(* The underlying library's type of indices / sizes for bitvectors. *)
Parameter idx : Type.

Parameter Z_idx : Z -> idx.
Parameter N_idx : N -> idx.
Parameter nat_idx : nat -> idx.

Parameter idx_Z : idx -> Z.
Parameter idx_N : idx -> N.
Parameter idx_nat : idx -> nat.

(* Enough theory about them to define the rest of the Sail library *)
Axiom Z_idx_Z : forall n, n = Z_idx (idx_Z n).
Axiom idx_Z_idx : forall z, (z >= 0)%Z -> idx_Z (Z_idx z) = z.
Axiom nat_idx_Z : forall n, nat_idx n = Z_idx (Z.of_nat n).
Axiom idx_N_Z_idx : forall z, idx_N (Z_idx z) = Z.to_N z.

Parameter cast_idx : forall {T : idx -> Type} {m n : idx}, T m -> m = n -> T n.
Axiom cast_idx_refl : forall n T (x : T n) (e : n = n), cast_idx x e = x.

Parameter idx_S : idx -> idx.
Parameter idx_add : idx -> idx -> idx.
Parameter idx_mul : idx -> idx -> idx.
Axiom Z_idx_S : forall z, (z >= 0)%Z -> Z_idx (Z.succ z) = idx_S (Z_idx z).

(* Now the actual bitvectors. *)

Parameter word : idx -> Type.
Parameter zeros : forall n, word n.
Parameter ones : forall n, word n.
Parameter get_bit : forall [n], word n -> idx -> bool.
Parameter set_bit : forall [n], word n -> idx -> bool -> word n.

Axiom get_bit_eq_nat : forall [n] (w v : word (nat_idx n)),
  (forall i, i < n -> get_bit w (nat_idx i) = get_bit v (nat_idx i)) -> w = v.

(* These are big-endian, in keeping with the Lem backend. *)
Parameter word_to_bools : forall [n], word n -> list bool.
Parameter bools_to_word : forall l : list bool, word (nat_idx (List.length l)).

Parameter word_to_Z : forall [n], word n -> Z.
Parameter word_to_N : forall [n], word n -> N.
Parameter Z_to_word : forall n, Z -> word n.
Parameter N_to_word : forall n, N -> word n.

Axiom word_to_N_range : forall [n] (w : word n), (word_to_N w < 2 ^ idx_N n)%N.
Axiom word_to_Z_range : forall [n] (w : word (idx_S n)), (- 2 ^ idx_Z n <= word_to_Z w < 2 ^ idx_Z n)%Z.
Axiom testbit_word_to_N_high : forall [n] (w: word n) i, (i >= idx_N n)%N ->
  N.testbit (word_to_N w) i = false.

Axiom word_to_bools_length : forall [n] (w : word n), List.length (word_to_bools w) = idx_nat n.
Axiom word_to_bools_get_bit : forall [n] (w : word n) (i : nat) x,
  List.nth_error (word_to_bools w) i = Some x <-> get_bit w (nat_idx (idx_nat n - i - 1)) = x /\ i < idx_nat n.
Axiom word_to_bools_nth_Some : forall [n] (w : word n) (i : nat) x, idx_nat n > 0 ->
  List.nth_error (word_to_bools w) i = Some x <-> x = N.testbit (word_to_N w) (N.of_nat (idx_nat n - i - 1)) /\ i < idx_nat n.
Axiom bools_to_word_get_bit : forall l i b,
  List.nth_error l i = Some b <-> get_bit (bools_to_word l) (nat_idx (length l - i - 1)) = b /\ i < length l.
Axiom bools_to_word_nth_Some : forall (l : list bool) i b,
  List.nth_error l i = Some b <-> b = N.testbit (word_to_N (bools_to_word l)) (N.of_nat (length l - i - 1)) /\ i < length l.


Parameter slice : forall [m] n, word m -> idx -> word n.
Parameter update_slice : forall [m] [n], word m -> idx -> word n -> word m.
Parameter zero_extend : forall [m] n, word m -> word n.
Parameter sign_extend : forall [m] n, word m -> word n.
Parameter concat : forall [m] [n], word m -> word n -> word (idx_add m n).

Parameter and : forall [n], word n -> word n -> word n.
Parameter  or : forall [n], word n -> word n -> word n.
Parameter xor : forall [n], word n -> word n -> word n.
Parameter not : forall [n], word n -> word n.

Parameter add : forall [n], word n -> word n -> word n.
Parameter sub : forall [n], word n -> word n -> word n.
Parameter mul : forall [n], word n -> word n -> word n.

Parameter logical_shift_left  : forall [n], word n -> idx -> word n.
Parameter logical_shift_right : forall [n], word n -> idx -> word n.
Parameter arith_shift_right  : forall [n], word n -> idx -> word n.

Parameter replicate : forall m [n], word n -> word (idx_mul (nat_idx m) n).

Parameter eqb : forall [n], word n -> word n -> bool.
Axiom eqb_true_iff : forall {n} (w v : word n), eqb w v = true <-> w = v.

Parameter eq_dec : forall [n] (w v : word n), {w = v} + {w <> v}.

Parameter reverse_endian : forall [n], word n -> word n.
(*Parameter count_leading_zeros : forall {n}, word n -> nat.*)

Parameter word_to_binary_string : forall [n], word n -> String.string.
(*Parameter word_to_hex_string : forall [n], word n -> String.string.*)
End MachineWordInterface.
