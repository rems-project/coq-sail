From Coq Require Import ZArith String List.

(* To avoid carrying around proofs that vector sizes are correct everywhere,
   we extend many operations to cover nonsensical sizes.  To help, we have a
   typeclass of inhabited types so that we can pick a default value, and an
   opaque function that returns it - well typed Sail code reduction
   should never reach this definition. *)

(* This definition is intended to mirror the one in stdpp. *)

Class Inhabited (T:Type) := populate { inhabitant : T }.
#[global] Arguments populate {_} _.

#[export] Instance unit_inhabited : Inhabited unit := { inhabitant := tt }.
#[export] Instance z_inhabited : Inhabited Z := { inhabitant := 0 }.
#[export] Instance string_inhabited : Inhabited string := { inhabitant := "" }.
#[export] Instance bool_inhabited : Inhabited bool := { inhabitant := false }.
#[export] Instance pair_inhabited {X Y} `{Inhabited X} `{Inhabited Y} : Inhabited (X * Y) := {
  inhabitant := (inhabitant, inhabitant)
}.
#[export] Instance list_inhabited {X} : Inhabited (list X) := { inhabitant := List.nil }.
#[export] Instance option_inhabited {X} : Inhabited (option X) := { inhabitant := None }.
#[export] Instance impl_inhabited {S T} `{Inhabited T} : Inhabited (S -> T) := {
  inhabitant := fun _ => inhabitant
}.
