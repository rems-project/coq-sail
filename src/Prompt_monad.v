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

From Coq Require Import String.
Require Import Instr_kinds Values Instances.
Import ListNotations.
Local Open Scope Z.

Definition address := N.

Inductive monad reg_type a e :=
  | Done : a -> monad reg_type a e
  (* Read a number of bytes from memory, returned in little endian order,
     with or without a tag.  The first nat specifies the address, the second
     the number of bytes. *)
  | Read_mem : read_kind -> N -> nat -> (list memory_byte -> monad reg_type a e) -> monad reg_type a e
  | Read_memt : read_kind -> N -> nat -> ((list memory_byte * bitU) -> monad reg_type a e) -> monad reg_type a e
  (* Tell the system a write is imminent, at the given address and with the
     given size. *)
  | Write_ea : write_kind -> N -> nat -> monad reg_type a e -> monad reg_type a e
  (* Request the result : store-exclusive *)
  | Excl_res : (bool -> monad reg_type a e) -> monad reg_type a e
  (* Request to write a memory value of the given size at the given address,
     with or without a tag. *)
  | Write_mem : write_kind -> N -> nat -> list memory_byte -> (bool -> monad reg_type a e) -> monad reg_type a e
  | Write_memt : write_kind -> N -> nat -> list memory_byte -> bitU -> (bool -> monad reg_type a e) -> monad reg_type a e
  | Write_tag : write_kind -> N -> bitU -> (bool -> monad reg_type a e) -> monad reg_type a e
  (* Tell the system to dynamically recalculate dependency footprint *)
  | Footprint : monad reg_type a e -> monad reg_type a e
  (* Request a memory barrier *)
  | Barrier : barrier_kind -> monad reg_type a e -> monad reg_type a e
  (* Request to read register, will track dependency when mode.track_values *)
  | Read_reg : forall T, reg_type T -> (T -> monad reg_type a e) -> monad reg_type a e
  (* Request to write register *)
  | Write_reg : forall T, reg_type T -> T -> monad reg_type a e -> monad reg_type a e
  (* Request to choose a Boolean, e.g. to resolve an undefined bit. The string
     argument may be used to provide information to the system about what the
     Boolean is going to be used for. *)
  | Choose : string -> forall ty, (choose_type ty -> monad reg_type a e) -> monad reg_type a e
  (* Print debugging or tracing information *)
  | Print : string -> monad reg_type a e -> monad reg_type a e
  (*Result of a failed assert with possible error message to report*)
  | Fail : string -> monad reg_type a e
  (* Exception of type e *)
  | Exception : e -> monad reg_type a e.

Arguments Done [_ _ _].
Arguments Read_mem [_ _ _].
Arguments Read_memt [_ _ _].
Arguments Write_ea [_ _ _].
Arguments Excl_res [_ _ _].
Arguments Write_mem [_ _ _].
Arguments Write_memt [_ _ _].
Arguments Write_tag [_ _ _].
Arguments Footprint [_ _ _].
Arguments Barrier [_ _ _].
Arguments Read_reg [_ _ _ _].
Arguments Write_reg [_ _ _ _].
Arguments Choose [_ _ _].
Arguments Print [_ _ _].
Arguments Fail [_ _ _].
Arguments Exception [_ _ _].

(* The injectivity tactic can be confused by dependent types when some of the types
   involved don't quite match syntactically.  Sometimes it's easier to apply a lemma
   to a hypothesis instead. *)
Lemma Choose_injective {rv A E} s ty (x y : choose_type ty -> monad rv A E) :
  Choose s ty x = Choose s ty y ->
  x = y.
intros [=].
assumption.
Qed.

Inductive event {reg_type} :=
  | E_read_mem : read_kind -> N -> nat -> list memory_byte -> event
  | E_read_memt : read_kind -> N -> nat -> (list memory_byte * bitU) -> event
  | E_write_mem : write_kind -> N -> nat -> list memory_byte -> bool -> event
  | E_write_memt : write_kind -> N -> nat -> list memory_byte -> bitU -> bool -> event
  | E_write_tag : write_kind -> N -> nat -> bitU -> bool -> event
  | E_write_ea : write_kind -> N -> nat -> event
  | E_excl_res : bool -> event
  | E_barrier : barrier_kind -> event
  | E_footprint : event
  | E_read_reg : forall {T}, reg_type T -> T -> event
  | E_write_reg : forall {T}, reg_type T -> T -> event
  | E_choose : string -> forall ty, choose_type ty -> event
  | E_print : string -> event.
Arguments event : clear implicits.

Definition trace regval := list (event regval).

(*val return : forall rv a e. a -> monad rv a e*)
Definition returnm {rv A E} (a : A) : monad rv A E := Done a.

(*val bind : forall rv a b e. monad rv a e -> (a -> monad rv b e) -> monad rv b e*)
Fixpoint bind {rv A B E} (m : monad rv A E) (f : A -> monad rv B E) := match m with
  | Done a => f a
  | Read_mem rk a sz k =>       Read_mem rk a sz       (fun v => bind (k v) f)
  | Read_memt rk a sz k =>      Read_memt rk a sz      (fun v => bind (k v) f)
  | Write_mem wk a sz v k =>    Write_mem wk a sz v    (fun v => bind (k v) f)
  | Write_memt wk a sz v t k => Write_memt wk a sz v t (fun v => bind (k v) f)
  | Write_tag wk a t k =>       Write_tag wk a t       (fun v => bind (k v) f)
  | Read_reg descr k =>         Read_reg descr         (fun v => bind (k v) f)
  | Excl_res k =>               Excl_res               (fun v => bind (k v) f)
  | Choose descr ty k =>        Choose descr ty        (fun v => bind (k v) f)
  | Write_ea wk a sz k =>       Write_ea wk a sz       (bind k f)
  | Footprint k =>              Footprint              (bind k f)
  | Barrier bk k =>             Barrier bk             (bind k f)
  | Write_reg r v k =>          Write_reg r v          (bind k f)
  | Print msg k =>              Print msg              (bind k f)
  | Fail descr =>               Fail descr
  | Exception e =>              Exception e
end.

Notation "m >>= f" := (bind m f) (at level 50, left associativity).
(*val (>>) : forall rv b e. monad rv unit e -> monad rv b e -> monad rv b e*)
Definition bind0 {rv A E} (m : monad rv unit E) (n : monad rv A E) :=
  m >>= fun (_ : unit) => n.
Notation "m >> n" := (bind0 m n) (at level 50, left associativity).

(*val exit : forall rv a e. unit -> monad rv a e*)
Definition exit {rv A E} (_ : unit) : monad rv A E := Fail "exit".

(*val maybe_fail : forall 'rv 'a 'e. string -> maybe 'a -> monad 'rv 'a 'e*)
Definition maybe_fail {rv A E} msg (x : option A) : monad rv A E :=
match x with
  | Some a => returnm a
  | None => Fail msg
end.

Section Choose.
Context {rt : Type -> Type} {E : Type}.

Definition choose_bool descr : monad rt bool E := Choose descr ChooseBool returnm.
Definition choose_bit descr : monad rt bitU E := Choose descr ChooseBit returnm.
Definition choose_int descr : monad rt Z E := Choose descr ChooseInt returnm.
Definition choose_nat descr : monad rt Z E := Choose descr ChooseNat returnm.
Definition choose_real descr : monad rt _ E := Choose descr ChooseReal returnm.
Definition choose_string descr : monad rt string E := Choose descr ChooseString returnm.
Definition choose_range descr lo hi : monad rt Z E :=
  if lo <=? hi
  then Choose descr (ChooseRange lo hi) (fun v => if sumbool_of_bool ((lo <=? v) && (v <=? hi)) then returnm v else Fail "choose_range: Bad value")
  else Fail "choose_range: Bad range".
Definition choose_bitvector descr n : monad rt (mword n) E := Choose descr (ChooseBitvector n) returnm.

End Choose.

(*val assert_exp : forall rv e. bool -> string -> monad rv unit e*)
Definition assert_exp {rv E} (exp :bool) msg : monad rv unit E :=
 if exp then Done tt else Fail msg.

Definition assert_exp' {rv E} (exp :bool) msg : monad rv (exp = true) E :=
 if exp return monad rv (exp = true) E then Done eq_refl else Fail msg.
Definition bindH {rv A P E} (m : monad rv P E) (n : monad rv A E) :=
  m >>= fun (H : P) => n.
Notation "m >>> n" := (bindH m n) (at level 50, left associativity).

(*val throw : forall rv a e. e -> monad rv a e*)
Definition throw {rv A E} e : monad rv A E := Exception e.

(*val try_catch : forall rv a e1 e2. monad rv a e1 -> (e1 -> monad rv a e2) -> monad rv a e2*)
Fixpoint try_catch {rv A E1 E2} (m : monad rv A E1) (h : E1 -> monad rv A E2) := match m with
  | Done a =>                   Done a
  | Read_mem rk a sz k =>       Read_mem rk a sz       (fun v => try_catch (k v) h)
  | Read_memt rk a sz k =>      Read_memt rk a sz      (fun v => try_catch (k v) h)
  | Write_mem wk a sz v k =>    Write_mem wk a sz v    (fun v => try_catch (k v) h)
  | Write_memt wk a sz v t k => Write_memt wk a sz v t (fun v => try_catch (k v) h)
  | Write_tag wk a t k =>       Write_tag wk a t       (fun v => try_catch (k v) h)
  | Read_reg descr k =>         Read_reg descr         (fun v => try_catch (k v) h)
  | Excl_res k =>               Excl_res               (fun v => try_catch (k v) h)
  | Choose descr ty k =>        Choose descr ty        (fun v => try_catch (k v) h)
  | Write_ea wk a sz k =>       Write_ea wk a sz       (try_catch k h)
  | Footprint k =>              Footprint              (try_catch k h)
  | Barrier bk k =>             Barrier bk             (try_catch k h)
  | Write_reg r v k =>          Write_reg r v          (try_catch k h)
  | Print msg k =>              Print msg              (try_catch k h)
  | Fail descr =>               Fail descr
  | Exception e =>              h e
end.

(* For early return, we abuse exceptions by throwing and catching
   the return value. The exception type is "either r e", where "inr e"
   represents a proper exception and "inl r" an early return : value "r". *)
Definition monadR rv a r e := monad rv a (sum r e).

(*val early_return : forall rv a r e. r -> monadR rv a r e*)
Definition early_return {rv A R E} (r : R) : monadR rv A R E := throw (inl r).

(*val catch_early_return : forall rv a e. monadR rv a a e -> monad rv a e*)
Definition catch_early_return {rv A E} (m : monadR rv A A E) :=
  try_catch m
    (fun r => match r with
      | inl a => returnm a
      | inr e => throw e
     end).

(* Pure functions with early return using a sum: *)

Definition pure_early_return_bind {A B E} (v : E + A) (f : A -> E + B) : E + B :=
  match v with
  | inl e => inl e
  | inr a => f a
  end.

Notation "m >>$= f" := (pure_early_return_bind m f) (at level 50, left associativity).
Notation "m >>$ n" := (m >>$= fun _ => n) (at level 50, left associativity).

Definition pure_early_return {A} (v : A + A) : A :=
  match v with
  | inl v' => v'
  | inr v' => v'
  end.

Definition pure_early_return_embed {rv A R E} (v : R + A) : monadR rv A R E :=
  match v with
  | inl v' => early_return v'
  | inr v' => Done v'
  end.

(* Lift to monad with early return by wrapping exceptions *)
(*val liftR : forall rv a r e. monad rv a e -> monadR rv a r e*)
Definition liftR {rv A R E} (m : monad rv A E) : monadR rv A R E :=
 try_catch m (fun e => throw (inr e)).

(* Catch exceptions in the presence : early returns *)
(*val try_catchR : forall rv a r e1 e2. monadR rv a r e1 -> (e1 -> monadR rv a r e2) ->  monadR rv a r e2*)
Definition try_catchR {rv A R E1 E2} (m : monadR rv A R E1) (h : E1 -> monadR rv A R E2) :=
  try_catch m
    (fun r => match r with
      | inl r => throw (inl r)
      | inr e => h e
     end).

(*val read_memt_bytes : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monad 'rv (list memory_byte * bitU) 'e*)
Definition read_memt_bytes {rv A E} rk (addr : mword A) sz : monad rv (list memory_byte * bitU) E :=
  Read_memt rk (mword_to_N addr) (Z.to_nat sz) returnm.

(*val read_memt : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monad 'rv ('b * bitU) 'e*)
Definition read_memt {rv A E} rk (addr : mword A) sz : monad rv (mword (8 * sz) * bitU) E :=
  bind
    (read_memt_bytes rk addr sz)
    (fun '(bytes, tag) =>
       match of_bits (bits_of_mem_bytes bytes) with
       | Some v => returnm (v, tag)
       | None => Fail "bits_of_mem_bytes"
       end).

(*val read_mem_bytes : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monad 'rv (list memory_byte) 'e*)
Definition read_mem_bytes {rv A E} rk (addr : mword A) sz : monad rv (list memory_byte) E :=
  Read_mem rk (mword_to_N addr) (Z.to_nat sz) returnm.

(*val read_mem : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monad 'rv 'b 'e*)
Definition read_mem {rv A E} rk (addrsz : Z) (addr : mword A) sz : monad rv (mword (8 * sz)) E :=
  bind
    (read_mem_bytes rk addr sz)
    (fun bytes =>
       maybe_fail "bits_of_mem_bytes" (of_bits (bits_of_mem_bytes bytes))).

(*val excl_result : forall rv e. unit -> monad rv bool e*)
Definition excl_result {rv e} (_:unit) : monad rv bool e :=
  let k successful := (returnm successful) in
  Excl_res k.

Definition write_mem_ea {rv a E} wk (addrsz : Z) (addr: mword a) sz : monad rv unit E :=
 Write_ea wk (mword_to_N addr) (Z.to_nat sz) (Done tt).

(*val write_mem : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b =>
  write_kind -> integer -> 'a -> integer -> 'b -> monad 'rv bool 'e*)
Definition write_mem {rv a E} wk (addrsz : Z) (addr : mword a) sz (v : mword (8 * sz)) : monad rv bool E :=
  match (mem_bytes_of_bits v, mword_to_N addr) with
    | (Some v, addr) =>
       Write_mem wk addr (Z.to_nat sz) v returnm
    | _ => Fail "write_mem"
  end.

(*val write_memt : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b =>
  write_kind -> 'a -> integer -> 'b -> bitU -> monad 'rv bool 'e*)
Definition write_memt {rv a E} wk (addr : mword a) sz (v : mword (8 * sz)) tag : monad rv bool E :=
  match (mem_bytes_of_bits v, mword_to_N addr) with
    | (Some v, addr) =>
       Write_memt wk addr (Z.to_nat sz) v tag returnm
    | _ => Fail "write_mem"
  end.

Definition write_tag {rv a E} wk (addr : mword a) tag : monad rv bool E :=
  let addr := mword_to_N addr in
       Write_tag wk addr tag returnm.

(* This alternate version is used in a few places, but should probably disappear *)
Definition write_tag_bool {rv a E} (addr : mword a) tag : monad rv bool E :=
  let addr := mword_to_N addr in
       Write_tag Write_plain addr (bitU_of_bool tag) returnm.

Definition read_reg {rt a e} (reg : rt a) : monad rt a e :=
  let k v := Done v in
  Read_reg reg k.

Definition read_reg_ref {rt a e} (ref : register_ref rt a) : monad rt a e :=
  let k v := Done v in
  Read_reg ref.(reg) k.

Definition reg_deref {rt a e} := @read_reg_ref rt a e.

Definition write_reg {rt a e} (reg : rt a) (v : a) : monad rt unit e :=
 Write_reg reg v (Done tt).

Definition write_reg_ref {rt a e} (ref : register_ref rt a) (v : a) : monad rt unit e :=
 Write_reg ref.(reg) v (Done tt).

(*val barrier : forall rv e. barrier_kind -> monad rv unit e*)
Definition barrier {rv e} bk : monad rv unit e := Barrier bk (Done tt).

(*val footprint : forall rv e. unit -> monad rv unit e*)
Definition footprint {rv e} (_ : unit) : monad rv unit e := Footprint (Done tt).

(* Event traces *)

Section EventTraces.

Context (register : Type -> Type).
Context (register_eq_cast : forall {T T'} (P : Type -> Type) (r : register T) (r' : register T'), P T -> option (P T')).
Context (regval_eqb : forall {T} (r : register T), T -> T -> bool).

Local Open Scope bool_scope.

(*val emitEvent : forall 'regval 'a 'e. Eq 'regval => monad 'regval 'a 'e -> event 'regval -> maybe (monad 'regval 'a 'e)*)
Definition emitEvent {A E}  (m : monad register A E) (e : event register) : option (monad register A E) :=
 match (e, m) with
  | (E_read_mem rk a sz v, Read_mem rk' a' sz' k) =>
     if read_kind_beq rk' rk && N.eqb a' a && Nat.eqb sz' sz then Some (k v) else None
  | (E_read_memt rk a sz vt, Read_memt rk' a' sz' k) =>
     if read_kind_beq rk' rk && N.eqb a' a && Nat.eqb sz' sz then Some (k vt) else None
  | (E_write_mem wk a sz v r, Write_mem wk' a' sz' v' k) =>
     if write_kind_beq wk' wk && N.eqb a' a && Nat.eqb sz' sz && generic_eq v' v then Some (k r) else None
  | (E_write_memt wk a sz v tag r, Write_memt wk' a' sz' v' tag' k) =>
     if write_kind_beq wk' wk && N.eqb a' a && Nat.eqb sz' sz && generic_eq v' v && generic_eq tag' tag then Some (k r) else None
  | (E_read_reg r v, Read_reg r' k) =>
     match register_eq_cast _ _ _ r r' v with
     | Some v1 => Some (k v1)
     | None => None
     end
  | (E_write_reg r v, @Write_reg _ _ _ T r' v' k) =>
     match register_eq_cast _ _ _ r r' v with
     | Some v1 => if regval_eqb _ r' v' v1 then Some k else None
     | None => None
     end
  | (E_write_ea wk a sz, Write_ea wk' a' sz' k) =>
     if write_kind_beq wk' wk && N.eqb a' a && Nat.eqb sz' sz then Some k else None
  | (E_barrier bk, Barrier bk' k) =>
     if barrier_kind_beq bk' bk then Some k else None
  | (E_print m, Print m' k) =>
     if generic_eq m' m then Some k else None
  | (E_excl_res v, Excl_res k) => Some (k v)
  | (E_choose descr ty v, Choose descr' ty' k) =>
     match ChooseType_eq_dec ty' ty with
     | left EQ => if generic_eq descr' descr then Some (k (eq_rect_r choose_type v EQ)) else None
     | right _ => None
     end
  | (E_footprint, Footprint k) => Some k
  | _ => None
end.

Definition option_bind {A B : Type} (a : option A) (f : A -> option B) : option B :=
match a with
| Some x => f x
| None => None
end.

Fixpoint runTrace {A E} (t : trace register) (m : monad register A E) : option (monad register A E) :=
match t with
  | [] => Some m
  | e :: t' => option_bind (emitEvent m e) (runTrace t')
end.

Definition final {A E} (m : monad register A E) : bool :=
match m with
  | Done _ => true
  | Fail _ => true
  | Exception _ => true
  | _ => false
end.

Definition hasTrace {A E} (t : trace register) (m : monad register A E) : bool :=
match runTrace t m with
  | Some m => final m
  | None => false
end.

Definition hasException {A E} (t : trace register) (m : monad register A E) :=
match runTrace t m with
  | Some (Exception _) => true
  | _ => false
end.

Definition hasFailure {A E} (t : trace register) (m : monad register A E) :=
match runTrace t m with
  | Some (Fail _) => true
  | _ => false
end.

End EventTraces.
