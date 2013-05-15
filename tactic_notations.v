Require Export Sflib.


(* The order of the cases is determined by the
   order of the constructors in the inductive definition.

  The order can easily be switched once (brittle) proofs
  have been started. We'll leave them out of order until
  we can amend them.
*)

Tactic Notation "trace_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "read"	| Case_aux c "readarr"
  | Case_aux c "write" 	| Case_aux c "writearr"
  | Case_aux c "fetch" 	| Case_aux c "orambank"
  | Case_aux c "concat" | Case_aux c "epsilon"
  ].



Tactic Notation "trace_pattern_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Read"       | Case_aux c "Write"
  | Case_aux c "Readarr"    | Case_aux c "Writearr"
  | Case_aux c "Loop" 	    | Case_aux c "Fetch"
  | Case_aux c "Orambank"   | Case_aux c "Concat"
  | Case_aux c "TracePplus" | Case_aux c "Epsilon"
  ].

Tactic Notation "trace_equiv_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "equal_equiv" | Case_aux c "refl_equiv"
  | Case_aux c "assoc_equiv" | Case_aux c "trans_equiv"
  | Case_aux c "epsilon_ident_equivl"
  | Case_aux c "epsilon_ident_equivr"
  | Case_aux c "concat_decomp_equiv"
  ].

Tactic Notation "trace_pattern_equiv_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Epsilon_equiv" | Case_aux c "O_equiv"
  | Case_aux c "Read_equiv"    | Case_aux c "Fetch_equiv"
  | Case_aux c "Assoc_equiv"   | Case_aux c "Trans_equiv"
  | Case_aux c "Epsilon_ident_equivl" | Case_aux c "Epsilon_ident_equivr"
  | Case_aux c "Concat_decomp_equiv"
  ].
