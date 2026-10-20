From SailStdpp Require Import Values.

(* These proofs should not depend on Eqdep.Eq_rect_eq.  Check the exported
   lemma as well as its cast consumer, so reintroducing the axiom fails runtest. *)
Print Assumptions Z_idx_eq_dep.
Print Assumptions to_word_idx_cast.
