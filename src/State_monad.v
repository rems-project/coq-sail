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

Require Import Instr_kinds Values.
From Coq Require FMapAVL OrderedType OrderedTypeEx.
From Coq Require Import List.
From Coq Require Import Rbase.  (* TODO would like to avoid this in models without reals *)
Import ListNotations.
Local Open Scope Z.
From Coq Require OrderedTypeEx.

Module NMap := FMapAVL.Make(OrderedTypeEx.N_as_OT).

Definition Memstate : Type := NMap.t (mword 8).
Definition Tagstate : Type := NMap.t bool.

(* To avoid infinite sets in this state monad we parametrise on a choice
   operator for (e.g.) undefined values.  For executability, we define a
   default operator which always returns the same value for a given type,
   but we could also have oracle strings to provide real non-determinism.
 *)
Record ChoiceSource := {
  choice_t : Type;
  choice_state : choice_t;
  choice_choose : forall ty, choice_t -> choice_t * choose_type ty;
}.
Definition choose (cs : ChoiceSource) ty : ChoiceSource * choose_type ty :=
  let '(state, result) := cs.(choice_choose) ty cs.(choice_state) in
  let cs' := {| choice_t := cs.(choice_t); choice_state := state; choice_choose := cs.(choice_choose) |} in
  (cs', result).

Definition default_choice_fn ty (_:unit) : unit * choose_type ty :=
  match ty return unit * choose_type ty with
  | ChooseBool        => (tt, false)
  | ChooseInt         => (tt, 0)
  | ChooseNat         => (tt, 0)
  | ChooseReal        => (tt, R0)
  | ChooseString      => (tt, ""%string)
  | ChooseRange lo _  => (tt, lo)
  | ChooseBitvector n => (tt, mword_of_int 0)
  end.
Definition default_choice : ChoiceSource := {|
  choice_t := unit;
  choice_state := tt;
  choice_choose := default_choice_fn;
|}.

(* We deviate from the Lem library and prefix the fields with ss_ to avoid
   name clashes. *)
Record sequential_state {Regs} :=
  { ss_regstate : Regs;
    ss_memstate : Memstate;
    ss_tagstate : Tagstate;
    ss_output : string;
  }.
Arguments sequential_state : clear implicits.

(*val init_state : forall 'regs. 'regs -> sequential_state 'regs*)
Definition init_state {Regs} regs : sequential_state Regs :=
  {| ss_regstate := regs;
     ss_memstate := NMap.empty _;
     ss_tagstate := NMap.empty _;
     ss_output := ""%string;
  |}.

Inductive ex E :=
  | Failure : string -> ex E
  | Throw : E -> ex E.
Arguments Failure {E} _.
Arguments Throw {E} _.

Inductive result A E :=
  | Value : A -> result A E
  | Ex : ex E -> result A E.
Arguments Value {A} {E} _.
Arguments Ex {A} {E} _.

(* State, nondeterminism and exception monad with result value type 'a
   and exception type 'e. *)
(* TODO: the list was originally a set, can we reasonably go back to a set? *)
Definition monadS Regs a e : Type :=
 sequential_state Regs -> ChoiceSource -> list (result a e * sequential_state Regs * ChoiceSource).

(*val returnS : forall 'regs 'a 'e. 'a -> monadS 'regs 'a 'e*)
Definition returnS {Regs A E} (a:A) : monadS Regs A E := fun s cs => [(Value a,s,cs)].

(*val bindS : forall 'regs 'a 'b 'e. monadS 'regs 'a 'e -> ('a -> monadS 'regs 'b 'e) -> monadS 'regs 'b 'e*)
Definition bindS {Regs A B E} (m : monadS Regs A E) (f : A -> monadS Regs B E) : monadS Regs B E :=
 fun (s : sequential_state Regs) cs =>
  List.flat_map (fun v => match v with
             | (Value a, s', cs') => f a s' cs'
             | (Ex e, s', cs') => [(Ex e, s', cs')]
             end) (m s cs).

(*val seqS: forall 'regs 'b 'e. monadS 'regs unit 'e -> monadS 'regs 'b 'e -> monadS 'regs 'b 'e*)
Definition seqS {Regs B E} (m : monadS Regs unit E) (n : monadS Regs B E) : monadS Regs B E :=
 bindS m (fun (_ : unit) => n).
(*
let inline (>>$=) = bindS
let inline (>>$) = seqS
*)

Declare Scope state_monad.

Notation "m >>$= f" := (bindS m f) (at level 50, left associativity) : state_monad.
Notation "m >>$ n" := (seqS m n) (at level 50, left associativity) : state_monad.

Open Scope state_monad.

(*val chooseS : forall 'regs 'a 'e. SetType 'a => list 'a -> monadS 'regs 'a 'e*)
Definition choose_listS {Regs A E} (xs : list A) : monadS Regs A E :=
 fun s cs => (List.map (fun x => (Value x, s, cs)) xs).

Definition chooseS {Regs E} ty : monadS Regs (choose_type ty) E :=
  fun s cs =>
    let (cs',v) := choose cs ty in
    [(Value v, s, cs')].

Definition nondet_boolS {Regs E} : monadS Regs bool E :=
  fun s cs => [(Value false, s, cs); (Value true, s, cs)].

(*val readS : forall 'regs 'a 'e. (sequential_state 'regs -> 'a) -> monadS 'regs 'a 'e*)
Definition readS {Regs A E} (f : sequential_state Regs -> A) : monadS Regs A E :=
 (fun s => returnS (f s) s).

(*val updateS : forall 'regs 'e. (sequential_state 'regs -> sequential_state 'regs) -> monadS 'regs unit 'e*)
Definition updateS {Regs E} (f : sequential_state Regs -> sequential_state Regs) : monadS Regs unit E :=
 (fun s => returnS tt (f s)).

(*val failS : forall 'regs 'a 'e. string -> monadS 'regs 'a 'e*)
Definition failS {Regs A E} msg : monadS Regs A E :=
 fun s cs => [(Ex (Failure msg), s, cs)].

(*val exitS : forall 'regs 'e 'a. unit -> monadS 'regs 'a 'e*)
Definition exitS {Regs A E} (_:unit) : monadS Regs A E := failS "exit".

(*val throwS : forall 'regs 'a 'e. 'e -> monadS 'regs 'a 'e*)
Definition throwS {Regs A E} (e : E) :monadS Regs A E :=
 fun s cs => [(Ex (Throw e), s, cs)].

(*val try_catchS : forall 'regs 'a 'e1 'e2. monadS 'regs 'a 'e1 -> ('e1 -> monadS 'regs 'a 'e2) ->  monadS 'regs 'a 'e2*)
Definition try_catchS {Regs A E1 E2} (m : monadS Regs A E1) (h : E1 -> monadS Regs A E2) : monadS Regs A E2 :=
fun s cs =>
  List.flat_map (fun v => match v with
                | (Value a, s', cs') => returnS a s' cs'
                | (Ex (Throw e), s', cs') => h e s' cs'
                | (Ex (Failure msg), s', cs') => [(Ex (Failure msg), s', cs')]
                end) (m s cs).

(*val assert_expS : forall 'regs 'e. bool -> string -> monadS 'regs unit 'e*)
Definition assert_expS {Regs E} (exp : bool) (msg : string) : monadS Regs unit E :=
 if exp then returnS tt else failS msg.

Definition assert_expS' {Regs E} (exp : bool) (msg : string) : monadS Regs (exp = true) E :=
 if exp return monadS Regs (exp = true) E then returnS eq_refl else failS msg.

(* For early return, we abuse exceptions by throwing and catching
   the return value. The exception type is "either 'r 'e", where "Right e"
   represents a proper exception and "Left r" an early return of value "r". *)
Definition monadRS Regs A R E := monadS Regs A (sum R E).

(*val early_returnS : forall 'regs 'a 'r 'e. 'r -> monadRS 'regs 'a 'r 'e*)
Definition early_returnS {Regs A R E} (r : R) : monadRS Regs A R E := throwS (inl r).

(*val catch_early_returnS : forall 'regs 'a 'e. monadRS 'regs 'a 'a 'e -> monadS 'regs 'a 'e*)
Definition catch_early_returnS {Regs A E} (m : monadRS Regs A A E) : monadS Regs A E :=
  try_catchS m
    (fun v => match v with
      | inl a => returnS a
      | inr e => throwS e
     end).

(* Lift to monad with early return by wrapping exceptions *)
(*val liftRS : forall 'a 'r 'regs 'e. monadS 'regs 'a 'e -> monadRS 'regs 'a 'r 'e*)
Definition liftRS {A R Regs E} (m : monadS Regs A E) : monadRS Regs A R E :=
 try_catchS m (fun e => throwS (inr e)).

(* Catch exceptions in the presence of early returns *)
(*val try_catchRS : forall 'regs 'a 'r 'e1 'e2. monadRS 'regs 'a 'r 'e1 -> ('e1 -> monadRS 'regs 'a 'r 'e2) ->  monadRS 'regs 'a 'r 'e2*)
Definition try_catchRS {Regs A R E1 E2} (m : monadRS Regs A R E1) (h : E1 -> monadRS Regs A R E2) : monadRS Regs A R E2 :=
  try_catchS m
    (fun v => match v with
      | inl r => throwS (inl r)
      | inr e => h e
     end).

(*val maybe_failS : forall 'regs 'a 'e. string -> maybe 'a -> monadS 'regs 'a 'e*)
Definition maybe_failS {Regs A E} msg (v : option A) : monadS Regs A E :=
match v with
  | Some a  => returnS a
  | None => failS msg
end.

(*val read_tagS : forall 'regs 'a 'e. Bitvector 'a => 'a -> monadS 'regs bitU 'e*)
Definition read_tagS {Regs A E} (addr : mword A) : monadS Regs bool E :=
  let addr := mword_to_N addr in
  readS (fun s => opt_def false (NMap.find addr s.(ss_tagstate))).

Fixpoint genlist_acc {A:Type} (f : nat -> A) n acc : list A :=
  match n with
    | O => acc
    | S n' => genlist_acc f n' (f n' :: acc)
  end.
Definition genlist {A} f n := @genlist_acc A f n [].


(* Read bytes from memory and return in little endian order *)
Definition get_mem_bytes {Regs} addr sz (s : sequential_state Regs) : option (list (mword 8) * bool) :=
  let addrs := genlist (fun n => addr + N_of_nat n)%N sz in
  let read_byte s addr := NMap.find addr s.(ss_memstate) in
  let read_tag s addr := opt_def false (NMap.find addr s.(ss_tagstate)) in
  option_map
    (fun mem_val => (mem_val, List.fold_left andb (List.map (read_tag s) addrs) true))
    (just_list (List.map (read_byte s) addrs)).

Definition read_memt_bytesS {Regs E} (_ : read_kind) addr sz : monadS Regs (list (mword 8) * bool) E :=
  readS (get_mem_bytes addr sz) >>$=
  maybe_failS "read_memS".

Definition read_mem_bytesS {Regs E} (rk : read_kind) addr sz : monadS Regs (list (mword 8)) E :=
  read_memt_bytesS rk addr sz >>$= (fun '(bytes, _) =>
  returnS bytes).

Definition read_memtS {Regs E A} (rk : read_kind) (a : mword A) sz : monadS Regs (mword (8 * sz) * mword 1) E :=
  let a := mword_to_N a in
  read_memt_bytesS rk a (Z.to_nat sz) >>$= (fun '(bytes, tag) =>
  let mem_val := mword_of_bytes bytes in
  returnS (TypeCasts.autocast mem_val, bit_of_bool tag)).

Definition read_memS {Regs E A} rk (a : mword A) sz : monadS Regs (mword (8 * sz)) E :=
  read_memtS rk a sz >>$= (fun '(bytes, _) =>
  returnS bytes).

Definition excl_resultS {Regs E} : unit -> monadS Regs bool E :=
  (* TODO: This used to be more deterministic, checking a flag in the state
     whether an exclusive load has occurred before.  However, this does not
     seem very precise; it might be safer to overapproximate the possible
     behaviours by always making a nondeterministic choice. *)
  fun _ => nondet_boolS.

(* Write little-endian list of bytes to given address *)
Definition put_mem_bytes {Regs} addr sz (v : list (mword 8)) (tag : bool) (s : sequential_state Regs) : sequential_state Regs :=
  let addrs := genlist (fun n => addr + N_of_nat n)%N sz in
  let a_v := List.combine addrs v in
  let write_byte mem '(addr, v) := NMap.add addr v mem in
  let write_tag mem addr := NMap.add addr tag mem in
  {| ss_regstate := s.(ss_regstate);
     ss_memstate := List.fold_left write_byte a_v s.(ss_memstate);
     ss_tagstate := List.fold_left write_tag addrs s.(ss_tagstate);
     ss_output := s.(ss_output);
  |}.

Definition put_tag {Regs} addr (tag : bool) (s : sequential_state Regs) : sequential_state Regs :=
  let write_tag mem addr := NMap.add addr tag mem in
  {| ss_regstate := s.(ss_regstate);
     ss_memstate := s.(ss_memstate);
     ss_tagstate := write_tag s.(ss_tagstate) addr;
     ss_output := s.(ss_output);
  |}.

Definition write_memt_bytesS {Regs E} (_ : write_kind) addr sz (v : list (mword 8)) (t : bool) : monadS Regs bool E :=
  updateS (put_mem_bytes addr sz v t) >>$
  returnS true.

Definition write_mem_bytesS {Regs E} wk addr sz (v : list (mword 8)) : monadS Regs bool E :=
 write_memt_bytesS wk addr sz v false.

Definition write_memtS {Regs E A} wk (addr : mword A) sz (v : mword (8 * sz)) (t : mword 1) : monadS Regs bool E :=
  let addr := mword_to_N addr in
  let v := bytes_of_mword v in
  write_memt_bytesS wk addr (Z.to_nat sz) v (bool_of_bit t).

Definition write_tag_rawS {Regs E} (wk:write_kind) (addr : N) (tag : bool) : monadS Regs bool E :=
  updateS (put_tag addr tag) >>$
  returnS true.

Definition write_tagS {Regs E A} (wk:write_kind) (addr : mword A) (tag : bool) : monadS Regs bool E :=
  let addr := mword_to_N addr in
  write_tag_rawS wk addr tag.

Definition write_tag_boolS {Regs E A} (addr : mword A) (tag : bool) : monadS Regs bool E :=
  let addr := mword_to_N addr in
  write_tag_rawS Write_plain addr tag.

Definition write_memS {Regs E A} wk (addr : mword A) sz (v : mword (8 * sz)) : monadS Regs bool E :=
 write_memtS wk addr sz v (mword_of_int 0).

Definition read_regS {Regs rt rtype} {register_lookup : Regs -> forall (r : rt), rtype r} {E} (reg : rt) : monadS Regs (rtype reg) E :=
 readS (fun s => register_lookup s.(ss_regstate) reg).

Definition read_reg_refS {Regs rt rtype A} {register_lookup : Regs -> forall (r : rt), rtype r} {E} (ref : @register_ref rt rtype A) : monadS Regs A E :=
 readS (fun s => ref.(to_ty) (register_lookup s.(ss_regstate) ref.(reg))).

(*val read_regvalS : forall 'regs 'rv 'e.
  register_accessors 'regs 'rv -> string -> monadS 'regs 'rv 'e*)
Definition read_regvalS {Regs reg_type reg_to_type E} (acc : register_accessors Regs reg_type reg_to_type) (reg : reg_type) : monadS Regs (reg_to_type reg) E :=
  let '(read, _) := acc in
  readS (fun s => read reg s.(ss_regstate)).

(*val write_regvalS : forall 'regs 'rv 'e.
  register_accessors 'regs 'rv -> string -> 'rv -> monadS 'regs unit 'e*)
Definition write_regvalS {Regs reg_type reg_to_type E} (acc : register_accessors Regs reg_type reg_to_type) (reg : reg_type) (v : reg_to_type reg) : monadS Regs unit E :=
  let '(_, write) := acc in
  readS (fun s => write reg v s.(ss_regstate)) >>$= (fun rs' =>
      updateS (fun s =>
                 {| ss_regstate := rs';
                    ss_memstate := s.(ss_memstate);
                    ss_tagstate := s.(ss_tagstate);
                    ss_output := s.(ss_output);
                 |})).

Definition write_regS {Regs rt rtype} {register_set : Regs -> forall (r : rt), rtype r -> Regs} {E} (reg : rt) (v:rtype reg) : monadS Regs unit E :=
  updateS (fun s =>
             {| ss_regstate := register_set s.(ss_regstate) reg v;
                ss_memstate := s.(ss_memstate);
                ss_tagstate := s.(ss_tagstate);
                ss_output := s.(ss_output);
             |}).

Definition write_reg_refS {Regs rt rtype A} {register_set : Regs -> forall (r : rt), rtype r -> Regs} {E} (ref : @register_ref rt rtype A) (v:A) : monadS Regs unit E :=
  updateS (fun s =>
             {| ss_regstate := register_set s.(ss_regstate) ref.(reg) (ref.(from_ty) v);
                ss_memstate := s.(ss_memstate);
                ss_tagstate := s.(ss_tagstate);
                ss_output := s.(ss_output);
             |}).

(* TODO Add Show typeclass for value and exception type *)
(*val show_result : forall 'a 'e. result 'a 'e -> string*)
Definition show_result {A E} (x : result A E) : string := match x with
  | Value _ => "Value ()"
  | Ex (Failure msg) => "Failure " ++ msg
  | Ex (Throw _) => "Throw"
end.

Definition print_effectS {Regs E} (str : string) : monadS Regs unit E :=
  updateS (fun s =>
             {| ss_regstate := s.(ss_regstate);
                ss_memstate := s.(ss_memstate);
                ss_tagstate := s.(ss_tagstate);
                ss_output := s.(ss_output) ++ str;
             |}).
