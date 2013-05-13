Require Export Sflib.


(* The order of the cases is determined by the
	order of the constructors in the inductive definition.

	The order can easily be switched once (brittle) proofs
		have been started. We'll leave them out of order until
		we can amend them.
	*)

Tactic Notation "trace_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "read" | Case_aux c "readarr"
  | Case_aux c "write" | Case_aux c "writearr"
  | Case_aux c "fetch" | Case_aux c "orambank"
  | Case_aux c "concat" | Case_aux c "epsilon"].



Tactic Notation "trace_pattern_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Read" | Case_aux c "Write"
  | Case_aux c "Readarr" | Case_aux c "Writearr"
  | Case_aux c "Loop" | Case_aux c "Fetch"
  | Case_aux c "Orambank" | Case_aux c "Concat"
  | Case_aux c "TracePplus" | Case_aux c "Epsilon"].