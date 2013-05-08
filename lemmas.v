Require Export Sflib.

Require Export FSets.

Require Export Peano.

Require Export core.

Require Export semantics.

Require Export typing.

Definition gammavalid (gamma:environment) (M:memory) : Prop :=
forall x l, ((gamma x = Some (lnat l)) <-> (exists n, (M x = Some (vint n l))))
/\ ((gamma x = Some (larr l)) <-> (exists a, (M x = Some (varr a l)))).


Definition memTraceObliv (gamma:environment) (S:program) : Prop :=
forall M1 M2 t1 M1' t2 M2', (lowEquivalentMem M1 M2) ->
(progSem M1 S t1 M1') -> (progSem M2 S t2 M2') ->
((traceequiv t1 t2) /\ (lowEquivalentMem M1' M2')).