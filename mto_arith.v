(*
	Reproving some properties from Coq.Arith.Max
	because we were having trouble including those properties
	in our project

	Once those including issues are resolved, this file can be removed
	in place of a dependency.
*)

(* these are well known properties of max, they are theorems in the standard library,
but were having trouble *)

Fixpoint max n m : nat :=
  match n, m with
    | O, _ => m
    | S n', O => n
    | S n', S m' => S (max n' m')
  end.

Lemma le_max_l : forall n m, n <= max n m.
Proof.
Admitted.

Lemma le_max_r : forall n m, m <= max n m.
Proof.
Admitted.

Lemma le_max_or : forall n m, (n = max n m)\/(m = max n m).
Proof.
Admitted.