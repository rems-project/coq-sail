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

Require Import Values MachineWord.
From Coq Require Import Strings.Ascii.
Local Open Scope Z.

Definition string_sub (s : string) (start : Z) (len : Z) : string :=
  String.substring (Z.to_nat start) (Z.to_nat len) s.

Definition string_startswith s expected :=
  let prefix := String.substring 0 (String.length expected) s in
  String.eqb prefix expected.

Definition string_drop s (n : Z) :=
  let n := Z.to_nat n in
  String.substring n (String.length s - n) s.

Definition string_take s (n : Z) :=
  let n := Z.to_nat n in
  String.substring 0 n s.

Definition string_length s : Z := Z.of_nat (String.length s).

Definition string_append := String.append.

Local Open Scope char_scope.
Local Definition hex_char (c : Ascii.ascii) : option Z :=
match c with
| "0" => Some 0
| "1" => Some 1
| "2" => Some 2
| "3" => Some 3
| "4" => Some 4
| "5" => Some 5
| "6" => Some 6
| "7" => Some 7
| "8" => Some 8
| "9" => Some 9
| "a" | "A" => Some 10
| "b" | "B" => Some 11
| "c" | "C" => Some 12
| "d" | "D" => Some 13
| "e" | "E" => Some 14
| "f" | "F" => Some 15
| _ => None
end.
Local Close Scope char_scope.
Local Fixpoint more_digits (s : string) (base : Z) (acc : Z) (len : nat) : Z * nat :=
match s with
| EmptyString => (acc, len)
| String "_" t => more_digits t base acc (S len)
| String h t =>
  match hex_char h with
  | None => (acc, len)
  | Some i => 
    if i <? base
    then more_digits t base (base * acc + i) (S len)
    else (acc, len)
  end
end.
Local Definition int_of (s : string) (base : Z) (len : nat) : option (Z * Z) :=
match s with
| EmptyString => None
| String h t =>
  match hex_char h with
  | None => None
  | Some i =>
    if i <? base
    then
    let (i, len') := more_digits t base i (S len) in
    Some (i, Z.of_nat len')
    else None
  end
end.

(* I've stuck closely to OCaml's int_of_string, because that's what's currently
   used elsewhere. *)

Definition maybe_int_of_prefix (s : string) : option (Z * Z) :=
match s with
| EmptyString => None
| String "0" (String ("x"|"X") t) => int_of t 16 2
| String "0" (String ("o"|"O") t) => int_of t 8 2
| String "0" (String ("b"|"B") t) => int_of t 2 2
| String "0" (String "u" t) => int_of t 10 2
| String "-" t =>
  match int_of t 10 1 with
  | None => None
  | Some (i,len) => Some (-i,len)
  end
| _ => int_of s 10 0
end.

Definition maybe_int_of_string (s : string) : option Z :=
match maybe_int_of_prefix s with
| None => None
| Some (i,len) =>
  if len =? string_length s then Some i else None
end.

Fixpoint n_leading_spaces (s:string) : nat :=
  match s with
  | EmptyString => 0
  | String " " t => S (n_leading_spaces t)
  | _ => 0
  end.

Definition n_leading_spaces_Z (s:string) : Z := Z.of_nat (n_leading_spaces s).

Definition opt_spc_matches_prefix s : option (unit * Z) :=
  Some (tt, Z.of_nat (n_leading_spaces s)).

Definition spc_matches_prefix s : option (unit * Z) :=
  match n_leading_spaces s with
  | O => None
  | S n => Some (tt, Z.of_nat (S n))
  end.

Definition parse_hex_bits_opt sz s : option (mword sz) :=
  match s with
  | String "0" (String "x" t) =>
    match int_of t 16 2 with
    | None => None
    | Some (i, consumed) =>
        if ((i <? 2 ^ sz) && (consumed =? Z.of_nat (String.length s)))%bool then
          Some (mword_of_int i)
        else
          None
    end
  | _ => None
  end.

Definition valid_hex_bits sz s := match parse_hex_bits_opt sz s with None => false | Some _ => true end.
Definition parse_hex_bits sz s : mword sz :=
  match parse_hex_bits_opt sz s with None => TypeCasts.dummy_value | Some v => v end.

Definition parse_dec_bits_opt sz s : option (mword sz) :=
  match maybe_int_of_string s with
  | Some i => if andb (i >=? 0) (i <? 2 ^ sz) then Some (mword_of_int i) else None
  | None => None
  end.

Definition valid_dec_bits sz s := match parse_dec_bits_opt sz s with None => false | Some _ => true end.
Definition parse_dec_bits sz s : mword sz :=
  match parse_dec_bits_opt sz s with None => TypeCasts.dummy_value | Some v => v end.

Definition hex_bits_n_matches_prefix sz s : option (mword sz * Z) :=
  match maybe_int_of_prefix s with
  | None => None
  | Some (n, len) =>
    if andb (0 <=? n) (n <? pow 2 sz)
    then Some (mword_of_int n, len)
    else None
  end.

Definition hex_bits_1_matches_prefix s := hex_bits_n_matches_prefix 1 s.
Definition hex_bits_2_matches_prefix s := hex_bits_n_matches_prefix 2 s.
Definition hex_bits_3_matches_prefix s := hex_bits_n_matches_prefix 3 s.
Definition hex_bits_4_matches_prefix s := hex_bits_n_matches_prefix 4 s.
Definition hex_bits_5_matches_prefix s := hex_bits_n_matches_prefix 5 s.
Definition hex_bits_6_matches_prefix s := hex_bits_n_matches_prefix 6 s.
Definition hex_bits_7_matches_prefix s := hex_bits_n_matches_prefix 7 s.
Definition hex_bits_8_matches_prefix s := hex_bits_n_matches_prefix 8 s.
Definition hex_bits_9_matches_prefix s := hex_bits_n_matches_prefix 9 s.
Definition hex_bits_10_matches_prefix s := hex_bits_n_matches_prefix 10 s.
Definition hex_bits_11_matches_prefix s := hex_bits_n_matches_prefix 11 s.
Definition hex_bits_12_matches_prefix s := hex_bits_n_matches_prefix 12 s.
Definition hex_bits_13_matches_prefix s := hex_bits_n_matches_prefix 13 s.
Definition hex_bits_14_matches_prefix s := hex_bits_n_matches_prefix 14 s.
Definition hex_bits_15_matches_prefix s := hex_bits_n_matches_prefix 15 s.
Definition hex_bits_16_matches_prefix s := hex_bits_n_matches_prefix 16 s.
Definition hex_bits_17_matches_prefix s := hex_bits_n_matches_prefix 17 s.
Definition hex_bits_18_matches_prefix s := hex_bits_n_matches_prefix 18 s.
Definition hex_bits_19_matches_prefix s := hex_bits_n_matches_prefix 19 s.
Definition hex_bits_20_matches_prefix s := hex_bits_n_matches_prefix 20 s.
Definition hex_bits_21_matches_prefix s := hex_bits_n_matches_prefix 21 s.
Definition hex_bits_22_matches_prefix s := hex_bits_n_matches_prefix 22 s.
Definition hex_bits_23_matches_prefix s := hex_bits_n_matches_prefix 23 s.
Definition hex_bits_24_matches_prefix s := hex_bits_n_matches_prefix 24 s.
Definition hex_bits_25_matches_prefix s := hex_bits_n_matches_prefix 25 s.
Definition hex_bits_26_matches_prefix s := hex_bits_n_matches_prefix 26 s.
Definition hex_bits_27_matches_prefix s := hex_bits_n_matches_prefix 27 s.
Definition hex_bits_28_matches_prefix s := hex_bits_n_matches_prefix 28 s.
Definition hex_bits_29_matches_prefix s := hex_bits_n_matches_prefix 29 s.
Definition hex_bits_30_matches_prefix s := hex_bits_n_matches_prefix 30 s.
Definition hex_bits_31_matches_prefix s := hex_bits_n_matches_prefix 31 s.
Definition hex_bits_32_matches_prefix s := hex_bits_n_matches_prefix 32 s.
Definition hex_bits_33_matches_prefix s := hex_bits_n_matches_prefix 33 s.
Definition hex_bits_48_matches_prefix s := hex_bits_n_matches_prefix 48 s.
Definition hex_bits_64_matches_prefix s := hex_bits_n_matches_prefix 64 s.

Local Definition zero : N := Ascii.N_of_ascii "0".
Local Fixpoint string_of_N (limit : nat) (n : N) (acc : string) : string :=
match limit with
| O => acc
| S limit' =>
  let (d,m) := N.div_eucl n 10 in
  let acc := String (Ascii.ascii_of_N (m + zero)) acc in
  if N.ltb 0 d then string_of_N limit' d acc else acc
end.
Local Fixpoint pos_limit p :=
match p with
| xH => S O
| xI p | xO p => S (pos_limit p)
end.
Definition string_of_int (z : Z) : string :=
match z with
| Z0 => "0"
| Zpos p => string_of_N (pos_limit p) (Npos p) ""
| Zneg p => String "-" (string_of_N (pos_limit p) (Npos p) "")
end.

Local Definition asciia : N := Ascii.N_of_ascii "a".
Local Definition asciiA : N := Ascii.N_of_ascii "A".
Local Fixpoint hex_string_of_N (upper : bool) (limit : nat) (n : N) (acc : string) : string :=
match limit with
| O => acc
| S limit' =>
  let (d,m) := N.div_eucl n 16 in
  let digit := if 10 <=? m then m - 10 + (if upper then asciiA else asciia) else m + zero in
  let acc := String (Ascii.ascii_of_N digit) acc in
  if N.ltb 0 d then hex_string_of_N upper limit' d acc else acc
end%N.
Local Definition hex_string_of_int (prefix : string) (upper : bool) (z : Z) : string :=
match z with
| Z0 => append prefix "0"
| Zpos p => append prefix (hex_string_of_N upper (pos_limit p) (Npos p) "")
| Zneg p => String "-" (append prefix (hex_string_of_N upper (pos_limit p) (Npos p) ""))
end.

Definition decimal_string_of_bits {n} (bv : mword n) : string := string_of_int (int_of_mword false bv).

Local Fixpoint pad0 (n : nat) s :=
  match n with
  | O => s
  | S m => String "0" (pad0 m s)
  end%string.

Definition binary_string_of_word {n} (bv : MachineWord.word n) := String "0" (String "b" (MachineWord.word_to_binary_string bv)).
Definition string_of_bits {n} (w : mword n) : string :=
  if Z.modulo n 4 =? 0 then
    let s := hex_string_of_int "" true (int_of_mword false w) in
    String "0" (String "x" (pad0 (Z.to_nat (Z.div n 4) - String.length s) s))
  else
    binary_string_of_word (get_word w).

(* Some aliases for compatibility. *)
Definition dec_str := string_of_int.
Definition hex_str x := hex_string_of_int "0x" false x.
Definition hex_str_upper x := hex_string_of_int "0x" true x.
Definition concat_str := String.append.
