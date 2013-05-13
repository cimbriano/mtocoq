Require Export Sflib.

Require Export FSets.

Require Export Peano.

Require Export core.

Require Export semantics.

Require Export typing.

Definition gammavalid (gamma:environment) (M:memory) : Prop :=
  forall x l, ((gamma x = Some (lnat l)) <-> 
    (exists n, (M x = Some (vint n l)))) /\ 
    ((gamma x = Some (larr l)) <-> (exists a, (M x = Some (varr a l)))).


Definition memTraceObliv (gamma:environment) (S:program) : Prop :=
  forall M1 M2 t1 M1' t2 M2',
   (lowEquivalentMem M1 M2) ->
   (progSem M1 S t1 M1') ->
   (progSem M2 S t2 M2') ->
   ((traceequiv t1 t2) /\ (lowEquivalentMem M1' M2')).

Fixpoint tracelen (t:trace) : nat :=
  match t with
  | epsilon      => 0
  | concat t1 t2 => plus (tracelen t1) (tracelen t2)
  | _ => 1
  end.

Lemma lemmaone : forall t1 t2,
  (traceequiv t1 t2) -> ((tracelen t1) = (tracelen t2)).
Proof.
  intros t1 t2 H.
  induction H.
  Case "equal_equiv". reflexivity.
  Case "refl_equiv". symmetry. apply IHtraceequiv.
  Case "assoc_equiv". 
    simpl.
    rewrite plus_assoc.
    reflexivity.
  Case "trans_equiv".
    rewrite  <- IHtraceequiv2.
    apply IHtraceequiv1.
  Case "epsilon_ident_equivl".
    simpl. apply IHtraceequiv.
  Case "epsilon_ident_equiv2".
    simpl. 
    rewrite plus_0_r.
    apply IHtraceequiv.
  Case "concat_decomp_equiv".
    simpl.
    rewrite IHtraceequiv1.
    rewrite IHtraceequiv2.
    reflexivity.
Qed.

Fixpoint ithelement (t:trace) (i:nat) : trace :=
match i with
|O => epsilon
|S O =>(
match t with
|read _ _ => t
|write _ _ => t
|readarr _ _ _ => t
|writearr _ _ _ => t
|fetch _ => t
|concat t1 t2 => (match t1 with 
    |epsilon => ithelement t2 i 
    | _ =>ithelement t1 i end)
|_ => epsilon
end
)
|S (S n) =>(
match t with 
|concat t1 t2 =>
if (ble_nat i (tracelen t1)) 
then (ithelement t1 i) 
else (ithelement t2 (minus i (tracelen t1)))
|_ => epsilon
end
)
end.

Lemma lemmatwo
