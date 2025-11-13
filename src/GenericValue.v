From Coq Require Import ZArith String List.
Require Import Values String.

(** A simple datastructure to represent values taken from a toml file *)

Inductive generic_value :=
| GVNumber (z : Z)
| GVString (s : string)
| GVArray (l : list generic_value)
| GVStruct (l : list (string * generic_value)).

Local Open Scope string.

Definition update_Z gv (_prev : Z) : result Z string :=
  match gv with
  | GVNumber z => Ok z
  | _ => Err "value not an integer"%string
  end.

Definition update_bitvector {n} gv (prev : mword n) : result (mword n) string :=
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

Definition update_enum_type {T} gv (members : list (string * T)) (_prev : T) : result T string :=
  match gv with
  | GVString s =>
      match List.find (fun '(n, _) => String.eqb s n) members with
      | Some (_, v) => Ok v
      | None => Err ("Unknown enumeration element " ++ s)%string
      end
  | _ => Err "Enumeration value not a string"
  end.

Definition update_bool gv (_prev : bool) : result bool string :=
  match gv with
  | GVNumber 0 => Ok false
  | GVNumber 1 => Ok true
  | GVString "false" => Ok false
  | GVString "true" => Ok true
  | _ => Err "Boolean value not 0,1,false,true"
  end.
