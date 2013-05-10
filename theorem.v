Require Export Sflib.

Require Export FSets.

Require Export Peano.

Require Export core.

Require Export semantics.

Require Export typing.

Require Export lemmas.


Theorem Theoremone : forall S, exists gamma:environment, exists l:label, exists T:TracePat,
(progTyping gamma l S T) -> 
(memTraceObliv gamma S).
Proof.
Admitted.
