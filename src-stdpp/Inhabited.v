From Coq Require Import ZArith String List.
From stdpp Require Import base strings.

(* To avoid carrying around proofs that vector sizes are correct everywhere,
   we extend many operations to cover nonsensical sizes.  To help, we have a
   typeclass of inhabited types so that we can pick a default value, and an
   opaque function that returns it - well typed Sail code reduction
   should never reach this definition. *)

(* Here, we can just use the existing stdpp one. *)

Notation Inhabited := base.Inhabited.
Notation inhabitant := base.inhabitant.

(* The default instances are all provided by stdpp. *)
