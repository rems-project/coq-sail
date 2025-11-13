From Coq Require Import ZArith String List.
Require Import Values String.

(** A simple datastructure to represent values taken from a toml file *)

Inductive generic_value :=
| GVNumber (z : Z)
| GVString (s : string)
| GVArray (l : list generic_value)
| GVStruct (l : list (string * generic_value)).

Local Open Scope string.

Definition update_Z (prev : Z) gv : result Z string :=
  match gv with
  | GVNumber z => Ok z
  | _ => Err "value not an integer"%string
  end.

Definition update_bitvector {n} (prev : mword n) gv : result (mword n) string :=
  match gv with
  | GVNumber z => Ok (mword_of_int z) (* TODO: check range? *)
  | GVString s =>
      match parse_hex_bits_opt n s with
      | Some bv => Ok bv
      | None =>
          match parse_dec_bits_opt n s with
          | Some bv => Ok bv
          | None => Err "value not a bitvector"
          end
      end
  | _ => Err "value not a bitvector"
  end.

Definition field_in_generic_value gv field : result generic_value string :=
  match gv with
  | GVStruct fields =>
      match List.find (fun '(name, _) => String.eqb name field) fields with
      | Some (_, v) => Ok v
      | None => Err (String.append "no field called " field)
      end
  | _ => Err "value not a struct"
  end.
