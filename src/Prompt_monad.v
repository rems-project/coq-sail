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

Section WithRegisterType.
Context {register : Type} {reg_to_type : register -> Type}.

Inductive monad a e :=
  | Done : a -> monad a e
  (* Read a number of bytes from memory, returned in little endian order,
     with or without a tag.  The first nat specifies the address, the second
     the number of bytes. *)
  | Read_mem : read_kind -> N -> nat -> (list (mword 8) -> monad a e) -> monad a e
  | Read_memt : read_kind -> N -> nat -> ((list (mword 8) * bool) -> monad a e) -> monad a e
  (* Tell the system a write is imminent, at the given address and with the
     given size. *)
  | Write_ea : write_kind -> N -> nat -> monad a e -> monad a e
  (* Request the result : store-exclusive *)
  | Excl_res : (bool -> monad a e) -> monad a e
  (* Request to write a memory value of the given size at the given address,
     with or without a tag. *)
  | Write_mem : write_kind -> N -> nat -> list (mword 8) -> (bool -> monad a e) -> monad a e
  | Write_memt : write_kind -> N -> nat -> list (mword 8) -> bool -> (bool -> monad a e) -> monad a e
  | Write_tag : write_kind -> N -> bool -> (bool -> monad a e) -> monad a e
  (* Tell the system to dynamically recalculate dependency footprint *)
  | Footprint : monad a e -> monad a e
  (* Request a memory barrier *)
  | Barrier : barrier_kind -> monad a e -> monad a e
  (* Request to read register, will track dependency when mode.track_values *)
  | Read_reg : forall (r : register), (reg_to_type r -> monad a e) -> monad a e
  (* Request to write register *)
  | Write_reg : forall (r : register), reg_to_type r -> monad a e -> monad a e
  (* Request to choose a Boolean, e.g. to resolve an undefined bit. The string
     argument may be used to provide information to the system about what the
     Boolean is going to be used for. *)
  | Choose : string -> forall ty, (choose_type ty -> monad a e) -> monad a e
  (* Print debugging or tracing information *)
  | Print : string -> monad a e -> monad a e
  (*Result of a failed assert with possible error message to report*)
  | Fail : string -> monad a e
  (* Exception of type e *)
  | Exception : e -> monad a e.

Arguments Done [_ _].
Arguments Read_mem [_ _].
Arguments Read_memt [_ _].
Arguments Write_ea [_ _].
Arguments Excl_res [_ _].
Arguments Write_mem [_ _].
Arguments Write_memt [_ _].
Arguments Write_tag [_ _].
Arguments Footprint [_ _].
Arguments Barrier [_ _].
Arguments Read_reg [_ _].
Arguments Write_reg [_ _].
Arguments Choose [_ _].
Arguments Print [_ _].
Arguments Fail [_ _].
Arguments Exception [_ _].

(* The injectivity tactic can be confused by dependent types when some of the types
   involved don't quite match syntactically.  Sometimes it's easier to apply a lemma
   to a hypothesis instead. *)
Lemma Choose_injective {A E} s ty (x y : choose_type ty -> monad A E) :
  Choose s ty x = Choose s ty y ->
  x = y.
intros [=].
assumption.
Qed.

Inductive event :=
  | E_read_mem : read_kind -> N -> nat -> list (mword 8) -> event
  | E_read_memt : read_kind -> N -> nat -> (list (mword 8) * bool) -> event
  | E_write_mem : write_kind -> N -> nat -> list (mword 8) -> bool -> event
  | E_write_memt : write_kind -> N -> nat -> list (mword 8) -> bool -> bool -> event
  | E_write_tag : write_kind -> N -> nat -> bool -> bool -> event
  | E_write_ea : write_kind -> N -> nat -> event
  | E_excl_res : bool -> event
  | E_barrier : barrier_kind -> event
  | E_footprint : event
  | E_read_reg : forall (r : register), reg_to_type r -> event
  | E_write_reg : forall (r : register), reg_to_type r -> event
  | E_choose : string -> forall ty, choose_type ty -> event
  | E_print : string -> event.
Arguments event : clear implicits.

Definition trace := list event.

(*val return : forall rv a e. a -> monad rv a e*)
Definition returnm {A E} (a : A) : monad A E := Done a.

(*val bind : forall rv a b e. monad rv a e -> (a -> monad rv b e) -> monad rv b e*)
Fixpoint bind {A B E} (m : monad A E) (f : A -> monad B E) := match m with
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

(*val (>>) : forall rv b e. monad rv unit e -> monad rv b e -> monad rv b e*)
Definition bind0 {A E} (m : monad unit E) (n : monad A E) :=
  bind m (fun (_ : unit) => n).

(*val exit : forall rv a e. unit -> monad rv a e*)
Definition exit {A E} (_ : unit) : monad A E := Fail "exit".

(*val maybe_fail : forall 'rv 'a 'e. string -> maybe 'a -> monad 'rv 'a 'e*)
Definition maybe_fail {A E} msg (x : option A) : monad A E :=
match x with
  | Some a => returnm a
  | None => Fail msg
end.

(* Helper for value definitions that may contain an assertion or incomplete pattern match.  If the
   computation reduces immediately to a value it will return that, otherwise there will be a
   typechecking failure. *)
Definition unwrap_value {A E} (m : monad A E) : match m with Done _ => A | _ => True end :=
  match m with
  | Done a => a
  | _ => I
  end.

Section Choose.
Context {E : Type}.

Definition choose_bool descr : monad bool E := Choose descr ChooseBool returnm.
Definition choose_int descr : monad Z E := Choose descr ChooseInt returnm.
Definition choose_nat descr : monad Z E := Choose descr ChooseNat returnm.
Definition choose_real descr : monad _ E := Choose descr ChooseReal returnm.
Definition choose_string descr : monad string E := Choose descr ChooseString returnm.
Definition choose_range descr lo hi : monad Z E :=
  if lo <=? hi
  then Choose descr (ChooseRange lo hi) (fun v => if sumbool_of_bool ((lo <=? v) && (v <=? hi)) then returnm v else Fail "choose_range: Bad value")
  else Fail "choose_range: Bad range".
Definition choose_bitvector descr n : monad (mword n) E := Choose descr (ChooseBitvector n) returnm.

End Choose.

(*val assert_exp : forall rv e. bool -> string -> monad rv unit e*)
Definition assert_exp {E} (exp :bool) msg : monad unit E :=
 if exp then Done tt else Fail msg.

Definition assert_exp' {E} (exp :bool) msg : monad (exp = true) E :=
 if exp return monad (exp = true) E then Done eq_refl else Fail msg.
Definition bindH {A P E} (m : monad P E) (n : monad A E) :=
  bind m (fun (H : P) => n).

(*val throw : forall rv a e. e -> monad rv a e*)
Definition throw {A E} e : monad A E := Exception e.

(*val try_catch : forall rv a e1 e2. monad rv a e1 -> (e1 -> monad rv a e2) -> monad rv a e2*)
Fixpoint try_catch {A E1 E2} (m : monad A E1) (h : E1 -> monad A E2) := match m with
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
Definition monadR a r e := monad a (sum r e).

(*val early_return : forall rv a r e. r -> monadR rv a r e*)
Definition early_return {A R E} (r : R) : monadR A R E := throw (inl r).

(*val catch_early_return : forall rv a e. monadR rv a a e -> monad rv a e*)
Definition catch_early_return {A E} (m : monadR A A E) :=
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

Definition pure_early_return {A} (v : A + A) : A :=
  match v with
  | inl v' => v'
  | inr v' => v'
  end.

Definition pure_early_return_embed {A R E} (v : R + A) : monadR A R E :=
  match v with
  | inl v' => early_return v'
  | inr v' => Done v'
  end.

(* Lift to monad with early return by wrapping exceptions *)
(*val liftR : forall rv a r e. monad rv a e -> monadR rv a r e*)
Definition liftR {A R E} (m : monad A E) : monadR A R E :=
 try_catch m (fun e => throw (inr e)).

(* Catch exceptions in the presence : early returns *)
(*val try_catchR : forall rv a r e1 e2. monadR rv a r e1 -> (e1 -> monadR rv a r e2) ->  monadR rv a r e2*)
Definition try_catchR {A R E1 E2} (m : monadR A R E1) (h : E1 -> monadR A R E2) :=
  try_catch m
    (fun r => match r with
      | inl r => throw (inl r)
      | inr e => h e
     end).

(*val read_memt_bytes : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monad 'rv (list (mword 8) * bool) 'e*)
Definition read_memt_bytes {A E} rk (addr : mword A) sz : monad (list (mword 8) * bool) E :=
  Read_memt rk (mword_to_N addr) (Z.to_nat sz) returnm.

(*val read_memt : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monad 'rv ('b * bool) 'e*)
Definition read_memt {A E} rk (addr : mword A) sz : monad (mword (8 * sz) * mword 1) E :=
  bind
    (read_memt_bytes rk addr sz)
    (fun '(bytes, tag) => returnm (TypeCasts.autocast (mword_of_bytes bytes), bit_of_bool tag)).

(*val read_mem_bytes : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monad 'rv (list (mword 8)) 'e*)
Definition read_mem_bytes {A E} rk (addr : mword A) sz : monad (list (mword 8)) E :=
  Read_mem rk (mword_to_N addr) (Z.to_nat sz) returnm.

(*val read_mem : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b => read_kind -> 'a -> integer -> monad 'rv 'b 'e*)
Definition read_mem {A E} rk (addrsz : Z) (addr : mword A) sz : monad (mword (8 * sz)) E :=
  bind
    (read_mem_bytes rk addr sz)
    (fun bytes => returnm (TypeCasts.autocast (mword_of_bytes bytes))).

(*val excl_result : forall rv e. unit -> monad rv bool e*)
Definition excl_result {e} (_:unit) : monad bool e :=
  let k successful := (returnm successful) in
  Excl_res k.

Definition write_mem_ea {a E} wk (addrsz : Z) (addr: mword a) sz : monad unit E :=
 Write_ea wk (mword_to_N addr) (Z.to_nat sz) (Done tt).

(*val write_mem : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b =>
  write_kind -> integer -> 'a -> integer -> 'b -> monad 'rv bool 'e*)
Definition write_mem {a E} wk (addrsz : Z) (addr : mword a) sz (v : mword (8 * sz)) : monad bool E :=
  let v := bytes_of_mword v in
  let addr := mword_to_N addr in
  Write_mem wk addr (Z.to_nat sz) v returnm.

(*val write_memt : forall 'rv 'a 'b 'e. Bitvector 'a, Bitvector 'b =>
  write_kind -> 'a -> integer -> 'b -> bool -> monad 'rv bool 'e*)
Definition write_memt {a E} wk (addr : mword a) sz (v : mword (8 * sz)) tag : monad bool E :=
  let v := bytes_of_mword v in
  let addr := mword_to_N addr in
  Write_memt wk addr (Z.to_nat sz) v (bool_of_bit tag) returnm.

Definition write_tag {a E} wk (addr : mword a) (tag : mword 1) : monad bool E :=
  let addr := mword_to_N addr in
       Write_tag wk addr (bool_of_bit tag) returnm.

(* This alternate version is used in a few places, but should probably disappear *)
Definition write_tag_bool {a E} (addr : mword a) tag : monad bool E :=
  let addr := mword_to_N addr in
       Write_tag Write_plain addr tag returnm.

Definition read_reg {e} (reg : register) : monad (reg_to_type reg) e :=
  let k v := Done v in
  Read_reg reg k.

Definition read_reg_ref {a e} (ref : @register_ref register reg_to_type a) : monad a e :=
  let k v := Done (ref.(to_ty) v) in
  Read_reg ref.(reg) k.

Definition reg_deref {a e} := @read_reg_ref a e.

Definition write_reg {e} (reg : register) (v : reg_to_type reg) : monad unit e :=
 Write_reg reg v (Done tt).

Definition write_reg_ref {a e} (ref : @register_ref register reg_to_type a) (v : a) : monad unit e :=
 Write_reg ref.(reg) (ref.(from_ty) v) (Done tt).

(*val barrier : forall rv e. barrier_kind -> monad rv unit e*)
Definition barrier {e} bk : monad unit e := Barrier bk (Done tt).

(*val footprint : forall rv e. unit -> monad rv unit e*)
Definition footprint {e} (_ : unit) : monad unit e := Footprint (Done tt).

(* Event traces *)

Section EventTraces.

Context (register_eq_cast : forall (P : Type -> Type) (r r' : register), P (reg_to_type r) -> option (P (reg_to_type r'))).
Context (regval_eqb : forall (r : register), reg_to_type r -> reg_to_type r -> bool).

Local Open Scope bool_scope.

(*val emitEvent : forall 'regval 'a 'e. Eq 'regval => monad 'regval 'a 'e -> event 'regval -> maybe (monad 'regval 'a 'e)*)
Definition emitEvent {A E}  (m : monad A E) (e : event) : option (monad A E) :=
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
     match register_eq_cast (fun x => x) r r' v with
     | Some v1 => Some (k v1)
     | None => None
     end
  | (E_write_reg r v, @Write_reg _ _ r' v' k) =>
     match register_eq_cast (fun x => x) r r' v with
     | Some v1 => if regval_eqb r' v' v1 then Some k else None
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

Fixpoint runTrace {A E} (t : trace) (m : monad A E) : option (monad A E) :=
match t with
  | [] => Some m
  | e :: t' => option_bind (emitEvent m e) (runTrace t')
end.

Definition final {A E} (m : monad A E) : bool :=
match m with
  | Done _ => true
  | Fail _ => true
  | Exception _ => true
  | _ => false
end.

Definition hasTrace {A E} (t : trace) (m : monad A E) : bool :=
match runTrace t m with
  | Some m => final m
  | None => false
end.

Definition hasException {A E} (t : trace) (m : monad A E) :=
match runTrace t m with
  | Some (Exception _) => true
  | _ => false
end.

Definition hasFailure {A E} (t : trace) (m : monad A E) :=
match runTrace t m with
  | Some (Fail _) => true
  | _ => false
end.

End EventTraces.

End WithRegisterType.

Notation "m >>= f" := (bind m f) (at level 50, left associativity).
Notation "m >> n" := (bind0 m n) (at level 50, left associativity).
Notation "m >>> n" := (bindH m n) (at level 50, left associativity).

Notation "m >>$= f" := (pure_early_return_bind m f) (at level 50, left associativity).
Notation "m >>$ n" := (m >>$= fun _ => n) (at level 50, left associativity).

Arguments Done [_ _ _ _].
Arguments Read_mem [_ _ _ _].
Arguments Read_memt [_ _ _ _].
Arguments Write_ea [_ _ _ _].
Arguments Excl_res [_ _ _ _].
Arguments Write_mem [_ _ _ _].
Arguments Write_memt [_ _ _ _].
Arguments Write_tag [_ _ _ _].
Arguments Footprint [_ _ _ _].
Arguments Barrier [_ _ _ _].
Arguments Read_reg [_ _ _ _].
Arguments Write_reg [_ _ _ _].
Arguments Choose [_ _ _ _].
Arguments Print [_ _ _ _].
Arguments Fail [_ _ _ _].
Arguments Exception [_ _ _ _].
