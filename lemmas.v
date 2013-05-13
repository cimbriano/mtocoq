Require Export Sflib.
Require Export FSets.
Require Export Peano.
Require Export core.
Require Export semantics.
Require Export typing.
Require Export Decidable.

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
  | O => epsilon
  | S O =>

    match t with
    | read _ _ => t
    | write _ _ => t
    | readarr _ _ _ => t
    | writearr _ _ _ => t
    | fetch _ => t
    | orambank _ => t
    | concat t1 t2 => (if( ble_nat 1 (tracelen t1) ) then
                      ithelement t1 i else
                      ithelement t2 i)
    |_ => epsilon
    end

  | S (S n) =>
    match t with 
    | concat t1 t2 =>
      if (ble_nat i (tracelen t1)) 
      then (ithelement t1 i) 
      else (ithelement t2 (minus i (tracelen t1)))
    | _ => epsilon
    end
end.

Check ithelement.

Tactic Notation "trace_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "read" | Case_aux c "readarr" 
  | Case_aux c "write" | Case_aux c "writearr" 
  | Case_aux c "fetch" | Case_aux c "orambank" 
  | Case_aux c "concat" | Case_aux c "epsilon"].


Lemma lemmatwo_1 : forall t i, ((tracelen t)=0) -> (ithelement t i = epsilon).
Proof.
intros t i.
intros H.
induction ( t).
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
inversion H.
simpl in H.
apply plus_is_O in H.
simpl.
destruct i.
reflexivity.
destruct i.
destruct H as [H1 H2].
destruct t1.
inversion H1.
inversion H1.
inversion H1.
inversion H1.
inversion H1.
inversion H1.
inversion H1.
remember H1 as HH1.
rewrite H1.
simpl in H1.
rewrite H1.
apply IHt2.
apply H2.
apply IHt2.
apply H2.
assert ((ble_nat (S (S i)) (tracelen t1)) = false).
inversion H as [H1 H2].
rewrite H1.
simpl.
reflexivity.
rewrite H0.
inversion H as [H1 H2].
rewrite H1.
simpl.
apply IHt2.
apply H2.
simpl.
destruct i.
reflexivity.
destruct i.
reflexivity.
reflexivity.
Qed.

Lemma lemmatwo_2 : forall t, ithelement t 0 = epsilon.
Proof.
intros t.
induction t.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
Qed.

Lemma lemmatwo_3 : forall t n, (tracelen t = S (S n)) -> (exists t1, exists t2, t = concat t1 t2).
Proof.
intros t n.
unfold tracelen.
destruct t.

intros H.
inversion H.
intros H.
inversion H.
intros H.
inversion H.
intros H.
inversion H.
intros H.
inversion H.
intros H.
inversion H.
simpl.
intros H.
exists t1.
exists t2.
reflexivity.
intros H.
inversion H.
Qed.

(* Parameter P : nat -> Prop. *)

Fixpoint numconcat t : nat :=
match t with 
|concat a b => S (plus (numconcat a) (numconcat b))
| _ => O
end.

Lemma le_S :
  forall n m : nat,
    n <= S m -> n <= m \/ n = S m.
Proof.
  intros.
  inversion H.
  right. reflexivity.
  left. assumption.
Qed.

Theorem strongind_aux :forall (P : nat -> Prop),
  P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, (forall m, ((m <= n) -> P m)).
Proof.
  induction n as [ | n' IHn' ].
    intros m H1.
    inversion H1.
    assumption.
    intros.
    assert (m <= n' \/ m = S n'). apply le_S. assumption.
    inversion H2.
    apply IHn'; assumption.
    rewrite H3.
    apply (H0 n'); assumption.
Qed.

Lemma weaken :
  forall (P : nat -> Prop), (forall (n:nat), (forall m, ((m <= n) -> P m))) -> (forall n, P n).
Proof.
  intros P H n.
  apply (H n n).
  apply le_n.
Qed.

Theorem strongind : forall (P : nat -> Prop),
  P 0 ->
  (forall n, (forall m, m <= n -> P m) -> P (S n)) ->
  forall n, P n.
Proof.
  intros.
  apply weaken.
  apply strongind_aux; assumption.
Qed.


Lemma lemma_plusright : forall a b, a<=a+b.
Proof.
induction a.
apply le_O_n.
intros b.
rewrite plus_Sn_m.
apply le_n_S.
apply IHa.
Qed.

Lemma cancelminus : forall a b, (a<=b) -> (b-a+a=b).
Proof.
intros a b H.
induction a.
rewrite minus_n_O.
rewrite plus_n_O.
reflexivity.
Admitted.

Lemma lemmatwo : forall i t, (ithelement t i <> epsilon) <-> ((le 1 i) /\ (le i (tracelen t))).
Proof.
intros i t.
remember (tracelen t).
generalize Heqn.
generalize t i.
apply strongind with (P:=(fun n => forall t0 i0, n=tracelen t0 -> (ithelement t0 i0 <> epsilon <-> 1<= i0 <=n))).
intros t0 i0.
intros FOO.


split.

intros HFOO.
remember lemmatwo_1.
symmetry in Heqn.
assert (ithelement t0 i0 = epsilon).
apply e.
symmetry.
apply FOO.
rewrite H in HFOO.
unfold not in HFOO.
assert (epsilon = epsilon).
reflexivity.
apply HFOO in H0.
inversion H0.
intros H.
inversion H as [H1 H2].
assert (1 <=0).
generalize H1 H2.
apply le_trans.
inversion H0.

intros n0.
intros Hyp.
intros HH.
destruct n0.
split.
intros HHH.
assert (i0=1).
assert (epsilon= epsilon).
reflexivity.
destruct i0.
rewrite lemmatwo_2 in HHH.
apply HHH in H0.
inversion H0.
destruct i0.
reflexivity.
assert(forall t0 n0, ((S O) = tracelen t0) ->(ithelement t0 (S (S n0)) = epsilon)).
intros t0 n0.
intros HHHH.
induction t0.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl.
reflexivity.
simpl in HHHH.
simpl.
destruct (tracelen t0_1).
simpl in HHHH.
apply IHt0_2.
apply HHHH.
assert (tracelen t0_2 = 0).
rewrite plus_Sn_m in HHHH.
inversion  HHHH.
symmetry in H2.
apply plus_is_O in H2.
apply H2.
rewrite H1 in HHHH.
rewrite  plus_0_r in HHHH.
inversion HHHH.
apply lemmatwo_1.
apply H1.
simpl.
reflexivity.
apply HHH in H1.
inversion H1.
apply H.
rewrite H0.
split.
apply le_refl.
apply le_refl.
intros HHH.
assert (i0=1).
inversion HHH as [HHH1 HHH2].
apply le_antisym.
apply HHH2.
apply HHH1.
rewrite H0.
assert (forall t, (tracelen t = 1) -> (ithelement t 1 <> epsilon)).
intros t0.
intros HHHH.
induction t0.
simpl.
intros HHHHH.
inversion HHHHH.
simpl.
intros HHHHH.
inversion HHHHH.
simpl.
intros HHHHH.
inversion HHHHH.
simpl.
intros HHHHH.
inversion HHHHH.
simpl.
intros HHHHH.
inversion HHHHH.
simpl.
intros HHHHH.
inversion HHHHH.
simpl in  HHHH.
remember (tracelen t0_1).
simpl.
destruct (n0).
simpl in HHHH.
simpl.
destruct t0_1.
simpl.
intros HHHHH.
inversion HHHHH.
simpl.
intros HHHHH.
inversion HHHHH.
simpl.
intros HHHHH.
inversion HHHHH.
simpl.
intros HHHHH.
inversion HHHHH.
simpl.
intros HHHHH.
inversion HHHHH.
simpl.
intros HHHHH.
inversion HHHHH.
rewrite <- Heqn0.
apply IHt0_2.
apply HHHH.
simpl.
apply IHt0_2.
apply HHHH.
assert (n0 = 0).
destruct (tracelen t0_2).
rewrite plus_0_r in HHHH.
inversion HHHH.
reflexivity.
rewrite plus_Sn_m in HHHH.
inversion HHHH.
rewrite <- plus_n_Sm in H2.
inversion H2.
rewrite H1 in Heqn0.
rewrite <- Heqn0.
apply IHt0_1.
rewrite <- H1.
reflexivity.
simpl in HHHH.
inversion HHHH.
apply H1.
symmetry.
apply H.

(* base case done*)

remember lemmatwo_3.
intros i0.
intros HFOO.
remember HFOO as HHH.
clear HeqHHH.
symmetry in HFOO.
rewrite -> HHH.
clear Heqe.
remember (tracelen HH).
rewrite Heqn1.
rewrite Heqn1 in HFOO.
induction HH.
apply e in HFOO.
inversion HFOO.
inversion H.
clear H HFOO.
inversion H0.
apply e in HFOO.
inversion HFOO.
inversion H.
clear H HFOO.
inversion H0.
apply e in HFOO.
inversion HFOO.
inversion H.
clear H HFOO.
inversion H0.
apply e in HFOO.
inversion HFOO.
inversion H.
clear H HFOO.
inversion H0.
apply e in HFOO.
inversion HFOO.
inversion H.
clear H HFOO.
inversion H0.
apply e in HFOO.
inversion HFOO.
inversion H.
clear H HFOO.
inversion H0.
apply e in HFOO.
inversion HFOO.
inversion H.
clear H HFOO.




simpl.
destruct i0.
split.
intros H1.
assert (epsilon = epsilon).
reflexivity.
apply H1 in H.
inversion H.
intros H1.
inversion H1.
inversion H.

remember (tracelen x) as trlnx.
remember (tracelen HH1) as trlnHH1.



rewrite HeqtrlnHH1 in IHHH1.
rewrite HeqtrlnHH1.



destruct i0.
simpl in Heqn.
simpl in Hyp.
simpl in HHH.
inversion H0.
rewrite H1 in *.
rewrite H2 in *.
assert ((tracelen x0 = O) ->(exists t1 : trace, exists t2 : trace, x=concat t1 t2)).
intros H3.
rewrite Heqn1 in HHH.
simpl in HHH.
rewrite H3 in HHH.
rewrite <- plus_n_O in HHH.
apply lemmatwo_3 with n0.
symmetry.
apply HHH.

simpl in Heqn1.
rewrite <- Heqtrlnx.
rewrite <- Heqtrlnx in Heqn1.
rewrite <- Heqtrlnx in IHHH1.
destruct (trlnx).
simpl in Heqn1.
apply IHHH2.
apply Heqn1.
rewrite HHH.
symmetry.
apply Heqn1.
(**apply Hyp.
simpl in HHH.
apply lemmatwo_3 with n0.
symmetry.
apply HHH.**)
destruct (tracelen x0).
rewrite <- plus_n_O.
apply IHHH1.
rewrite <- plus_n_O in Heqn1.
apply Heqn1.
rewrite Heqn1 in HHH.
rewrite <- plus_n_O in HHH.
symmetry.
apply HHH.
assert (trlnHH1 <= S n0) as HlengHH1.
simpl in  Heqn1.
rewrite Heqn1 in HHH.
inversion HHH.
rewrite <- plus_n_Sm in H4.
rewrite <- plus_Sn_m in H4.
rewrite Heqtrlnx in H4.
rewrite <- HeqtrlnHH1 in H4.
rewrite H4.
apply lemma_plusright.
assert (ithelement x 1 <> epsilon <-> 1<= 1<= (tracelen x)).
apply Hyp.
rewrite Heqn1 in HHH.
rewrite <- plus_n_Sm in HHH.
rewrite <- Heqtrlnx.
inversion HHH.
apply le_n_S.
apply lemma_plusright.
reflexivity.
split.
intros HH4.
apply H3 in HH4.


inversion HH4.
split.
apply le_refl.
assert (tracelen x <= S (S n0)).
rewrite HHH.
rewrite Heqn1.
rewrite Heqtrlnx.
apply lemma_plusright.
apply le_n_S.
apply le_O_n.
intros HH4.
apply H3.
rewrite <- Heqtrlnx.
split.
apply le_refl.
apply le_n_S.
apply le_O_n.


remember (ble_nat (S (S i0)) (tracelen HH1)).
destruct b.


remember (tracelen HH2) as trlnHH2.
destruct (trlnHH2).
rewrite <- plus_n_O.
apply IHHH1.
simpl in Heqn1.
rewrite <- HeqtrlnHH2 in Heqn1.
rewrite <- plus_n_O in Heqn1.
apply Heqn1.
simpl in Heqn1.
rewrite <- HeqtrlnHH2 in Heqn1.
rewrite <- plus_n_O in Heqn1.
rewrite Heqn1 in HHH.
symmetry.
apply HHH.



split.
intros HH4.
split.
apply le_n_S.
apply le_O_n.
assert (S (S i0) <= tracelen HH1).
apply ble_nat_true.
symmetry.
apply Heqb.
assert ( tracelen HH1 <=  tracelen HH1+  S trlnHH2).
apply lemma_plusright.
apply le_trans with  (tracelen HH1).
apply H.
apply H1.
intros HH4.
inversion HH4.
assert (S (S i0) <= tracelen HH1).
apply ble_nat_true.
symmetry.
apply Heqb.
assert (1<= S (S i0) <= tracelen HH1).
split.
apply H.
apply H2.


assert ((ithelement HH1 (S (S i0)) <> epsilon) <-> (1<= S (S i0) <= tracelen HH1)).
apply Hyp.
rewrite Heqn1 in HHH.
simpl in HHH.
rewrite <- HeqtrlnHH2 in HHH.
rewrite <- plus_n_Sm in HHH.
inversion HHH.
rewrite H5.
apply lemma_plusright.
reflexivity.
apply H4 in H3.
apply H3.
destruct trlnHH1.
rewrite <- HeqtrlnHH1.
rewrite  plus_O_n.
rewrite <- minus_n_O.
apply IHHH2.
simpl in Heqn1.
rewrite <- HeqtrlnHH1 in Heqn1.
rewrite plus_O_n in Heqn1.
apply Heqn1.
simpl in Heqn1.
rewrite <- HeqtrlnHH1 in Heqn1.
rewrite plus_O_n in Heqn1.
rewrite Heqn1 in HHH.
symmetry.
apply HHH.

remember (S i0 - tracelen HH1) as FOO.
assert (FOO + tracelen HH1 = S i0).


assert (tracelen HH1 <= S i0).
symmetry in Heqb.
apply ble_nat_false in Heqb.
apply not_le in Heqb.
unfold gt in Heqb.
apply lt_n_Sm_le in Heqb.
apply Heqb.
rewrite HeqFOO.
apply cancelminus.
apply H.
rewrite <- H.



assert (ithelement HH2 (S FOO) <> epsilon <-> 1<= S FOO <= tracelen HH2).
apply Hyp.
simpl in Heqn1.
rewrite <- HeqtrlnHH1 in Heqn1.
rewrite plus_Sn_m in Heqn1.
rewrite Heqn1 in HHH.
inversion HHH.
rewrite plus_comm in H2.
rewrite H2.
apply lemma_plusright.
reflexivity.
assert (S FOO + tracelen HH1 - tracelen HH1 = S FOO).
rewrite plus_comm.
apply minus_plus.
assert ((1<=  S FOO <= tracelen HH2) <-> (1<= S FOO + tracelen HH1 <= tracelen HH1 + tracelen HH2)).
split.
intros H4.
split.
rewrite <- HeqtrlnHH1.
rewrite <- plus_n_Sm.
apply le_n_S.
apply le_O_n.
inversion H4.
rewrite plus_comm.
apply plus_le_compat_l.
apply H5.
intros H4.
split.
inversion H4.

apply le_n_S.
apply le_O_n.
inversion H4.
rewrite <- plus_comm in H5.
admit.
rewrite <- plus_Sn_m.

rewrite H2.
apply iff_trans with (1<= S FOO <= tracelen HH2).
apply H1.
apply H3.
simpl in HFOO.
inversion HFOO.
Qed.

