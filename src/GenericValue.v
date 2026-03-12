From Coq Require Import ZArith String List.
Require Import Inhabited.
Require Import Values String.

Import ListNotations.

(** A simple datastructure to represent values taken from a toml file *)

Inductive generic_value :=
| GVNumber (z : Z)
| GVString (s : string)
| GVArray (l : list generic_value)
| GVStruct (l : list (string * generic_value)).

Local Open Scope string.

(* A typeclass of functions to update a value of a given type using a
(potentially partial) toml value. *)

Class GenericUpdate (T : Type) := {
  generic_update : generic_value -> T -> result T string
}.

#[export] Instance update_unit : GenericUpdate unit := {
  generic_update gv _prev :=
    match gv with
    | GVString "()"
    | GVString "tt"
    | GVString ""
    | GVArray []
    | GVStruct []
      => Ok tt
    | _ => Err "value not unit"
    end
}.

#[export] Instance update_Z : GenericUpdate Z := {
  generic_update gv _prev :=
    match gv with
    | GVNumber z => Ok z
    | _ => Err "value not an integer"%string
    end
}.

#[export] Instance update_bitvector {n} : GenericUpdate (mword n) := {
  generic_update gv _prev :=
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
    end
}.

Definition update_enum_type {T} gv (members : list (string * T)) (_prev : T) : result T string :=
  match gv with
  | GVString s =>
      match List.find (fun '(n, _) => String.eqb s n) members with
      | Some (_, v) => Ok v
      | None => Err ("Unknown enumeration element " ++ s)%string
      end
  | _ => Err "Enumeration value not a string"
  end.

#[export] Instance update_bool : GenericUpdate bool := {
  generic_update gv _prev :=
    match gv with
    | GVNumber 0 => Ok false
    | GVNumber 1 => Ok true
    | GVString "false" => Ok false
    | GVString "true" => Ok true
    | _ => Err "Boolean value not 0,1,false,true"
    end
}.


#[export] Instance update_prod2 {T1 T2} `{GenericUpdate T1, GenericUpdate T2} : GenericUpdate (T1 * T2) | 10 := {
  generic_update gv prev :=
    match gv with
    | GVArray [t1'; t2'] =>
        match prev with (t1, t2) =>
                          result_bind (fun t1'' =>
                                         result_bind (fun t2'' =>
                                                        Ok (t1'', t2''))
                                           (generic_update t2' t2))
                            (generic_update t1' t1)
        end
    | _ => Err "Pair value not a pair"
    end
}.

#[export] Instance update_prod3 {T1 T2 T3} `{GenericUpdate T1, GenericUpdate T2, GenericUpdate T3} : GenericUpdate (T1 * T2 * T3) | 9 := {
  generic_update gv prev :=
    match gv with
    | GVArray [t1'; t2'; t3'] =>
        match prev with (t1, t2, t3) =>
                          result_bind (fun t1'' =>
                                         result_bind (fun t2'' =>
                                                        result_bind (fun t3'' =>
                                                        Ok (t1'', t2'', t3''))
                                                          (generic_update t3' t3))
                                           (generic_update t2' t2))
                            (generic_update t1' t1)
        end
    | _ => Err "Triple value not a triple"
    end
}.

#[export] Instance update_prod4 {T1 T2 T3 T4} `{GenericUpdate T1, GenericUpdate T2, GenericUpdate T3, GenericUpdate T4} : GenericUpdate (T1 * T2 * T3 * T4) | 8 := {
  generic_update gv prev :=
    match gv with
    | GVArray [t1'; t2'; t3'; t4'] =>
        match prev with (t1, t2, t3, t4) =>
          result_bind (fun t1'' => result_bind (fun t2'' => result_bind (fun t3'' => result_bind (fun t4'' =>
            Ok (t1'', t2'', t3'', t4''))
          (generic_update t4' t4))
          (generic_update t3' t3))
          (generic_update t2' t2))
          (generic_update t1' t1)
        end
    | _ => Err "4-tuple value not a 4-tuple"
    end
}.

#[export] Instance update_prod5 {T1 T2 T3 T4 T5} `{GenericUpdate T1, GenericUpdate T2, GenericUpdate T3, GenericUpdate T4, GenericUpdate T5} : GenericUpdate (T1 * T2 * T3 * T4 * T5) | 7 := {
  generic_update gv prev :=
    match gv with
    | GVArray [t1'; t2'; t3'; t4'; t5'] =>
        match prev with (t1, t2, t3, t4, t5) =>
          result_bind (fun t1'' => result_bind (fun t2'' => result_bind (fun t3'' => result_bind (fun t4'' => result_bind (fun t5'' =>
            Ok (t1'', t2'', t3'', t4'', t5''))
          (generic_update t5' t5))
          (generic_update t4' t4))
          (generic_update t3' t3))
          (generic_update t2' t2))
          (generic_update t1' t1)
        end
    | _ => Err "5-tuple value not a 5-tuple"
    end
}.

#[export] Instance update_prod6 {T1 T2 T3 T4 T5 T6} `{GenericUpdate T1, GenericUpdate T2, GenericUpdate T3, GenericUpdate T4, GenericUpdate T5, GenericUpdate T6} : GenericUpdate (T1 * T2 * T3 * T4 * T5 * T6) | 6 := {
  generic_update gv prev :=
    match gv with
    | GVArray [t1'; t2'; t3'; t4'; t5'; t6'] =>
        match prev with (t1, t2, t3, t4, t5, t6) =>
          result_bind (fun t1'' => result_bind (fun t2'' => result_bind (fun t3'' => result_bind (fun t4'' => result_bind (fun t5'' => result_bind (fun t6'' =>
            Ok (t1'', t2'', t3'', t4'', t5'', t6''))
          (generic_update t6' t6))
          (generic_update t5' t5))
          (generic_update t4' t4))
          (generic_update t3' t3))
          (generic_update t2' t2))
          (generic_update t1' t1)
        end
    | _ => Err "6-tuple value not a 6-tuple"
    end
}.

#[export] Instance update_option {T} `{Inhabited T, GenericUpdate T} : GenericUpdate (option T) := {
  generic_update gv prev :=
    match gv with
    | GVString "None" => Ok None
    | GVArray [GVString "Some"; gv'] =>
        result_bind (fun v => Ok (Some v)) (generic_update gv' (match prev with Some v => v | None => inhabitant end))
    | _ => result_bind (fun v => Ok (Some v)) (generic_update gv (match prev with Some v => v | None => inhabitant end))
    end
}.

Local Fixpoint update_list_aux {T} `{Inhabited T, GenericUpdate T} (l : list generic_value) (prev : list T) : result (list T) string :=
  match (l, prev) with
  | (gv::gvs, p::ps) => result_bind (fun v => result_bind (fun vs => Ok (v::vs)) (update_list_aux gvs ps)) (generic_update gv p)
  | (gv::gvs, []) => result_bind (fun v => result_bind (fun vs => Ok (v::vs)) (update_list_aux gvs [])) (generic_update gv inhabitant)
  | ([], _) => Ok []
  end.

#[export] Instance update_list {T} `{Inhabited T, GenericUpdate T} : GenericUpdate (list T) := {
  generic_update gv prev :=
    match gv with
    | GVArray l => update_list_aux l prev
    | _ => Err "list value isn't an array"
    end
}.

Local Fixpoint update_vec_aux {T} `{GenericUpdate T} (l : list generic_value) (prev : list T) : result (list T) string :=
  match (l, prev) with
  | (gv::gvs, p::ps) => result_bind (fun v => result_bind (fun vs => Ok (v::vs)) (update_vec_aux gvs ps)) (generic_update gv p)
  | (_::_, []) => Err "vec value is too long"
  | ([], prev) => Ok prev
  end.

Local Lemma update_vec_aux_length {T} `{GenericUpdate T} {n l} {prev : vec T n} {l'} :
  update_vec_aux l (projT1 prev) = Ok l' ->
  List.length l' = Z.to_nat n.
Proof.
  destruct prev as [prev <-].
  revert l l'.
  induction prev as [ | p ps]; intros l l'.
  - destruct l; simpl; inversion 1; reflexivity.
  - destruct l as [ | gv gvs].
    + simpl. inversion 1; subst. reflexivity.
    + simpl. intros EQ.
      destruct (result_bind_inv _ _ _ EQ) as [v [EQ1 EQ2]].
      destruct (result_bind_inv _ _ _ EQ2) as [vs [EQ3 [= <-]]].
      apply IHps in EQ3.
      rewrite <- EQ3.
      reflexivity.
Qed.

#[export] Instance update_vec {T n} `{GenericUpdate T} : GenericUpdate (vec T n) := {
    generic_update gv prev :=
      match gv with
      | GVArray l =>
        result_bind_pf (update_vec_aux l (projT1 prev)) (fun l' P => Ok (@existT _ _ l' (update_vec_aux_length P)))
      | _ => Err "vec value wasn't an array"
      end
}.

#[export] Instance update_string : GenericUpdate string := {
  generic_update gv prev :=
    match gv with
    | GVString s => Ok s
    | _ => Err "string value not a string"
    end
}.
