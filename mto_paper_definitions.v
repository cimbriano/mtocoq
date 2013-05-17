Require Export semantics.
Require Export typing.

(* Definition 1 : Low Equivalence *)

Definition lowEquivalentMem (M1 M2: memory):  Prop :=
 (forall x v,
 		(M1 x = Some (vint v low)) <-> (M2 x = Some (vint v low)))
 	/\
 (forall x v,
		(M1 x = Some (varr v low)) <-> (M2 x = Some (varr v low))).


(* Definition 2 : Gamma Validity *)

Definition gammavalid (gamma:environment) (M:memory) : Prop :=
	forall x l,
	((gamma x = Some (lnat l)) <-> (exists n, (M x = Some (vint n l))))
	/\
	((gamma x = Some (larr l)) <-> (exists a, (M x = Some (varr a l)))).



(* Definition 3 : Memory Trace Obliviousness *)

Definition memTraceObliv (gamma:environment) (S:program) : Prop :=
	forall M1 M2 t1 M1' t2 M2',
	(lowEquivalentMem M1 M2) ->
	(gammavalid gamma M1) ->
	(gammavalid gamma M2) ->
	(progSem M1 S t1 M1') ->
	(progSem M2 S t2 M2') ->

		((traceequiv t1 t2) /\ (lowEquivalentMem M1' M2')).