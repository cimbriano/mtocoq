Require Export strong_induction.
Require Export mto_paper_definitions.
Require Export semantics.
Require Export typing.

(* Lemmas From the Paper *)

Lemma lemmatwelve :
	forall gamma l0 S1 S2 T1 T2 M1 M2 M1' M2' t1 t2,
	(progTyping gamma l0 S1 T1) ->
	(progTyping gamma l0 S2 T2) ->
	(TracePatEquiv T1 T2) ->
	(gammavalid gamma M1) ->
	(gammavalid gamma M2) ->
	(progSem M1 S1 t1 M1') ->
	(progSem M2 S2 t2 M2') ->
		((traceequiv t1 t2) /\ (lowEquivalentMem M1' M2')).
Proof.
Admitted.

Lemma lemmasix :
	forall gamma e T M1 M2 t1 t2 n1 n2,
	(exprTyping gamma e (lnat low) T) ->
	(gammavalid gamma M1) ->
	(gammavalid gamma M2) ->
	(exprSem M1 e t1 n1) ->
	(exprSem M2 e t2 n2) -> ((t1 = t2) /\ (n1 = n2)).
Proof.
Admitted.

Lemma lemmaseven :
	forall gamma e l T M1 M2 t1 t2 n1 n2,
	(exprTyping gamma e (lnat (o_high l)) T) ->
	(gammavalid gamma M1) ->
	(gammavalid gamma M2) ->
	(exprSem M1 e t1 n1) ->
	(exprSem M2 e t2 n2) -> (t1 = t2).
Proof.
Admitted.


(* Auxiliary Lemma *)

Lemma stayvalid :
	forall gamma M p t M',
	(gammavalid gamma M) ->
	(progSem M p t M') -> (gammavalid gamma M').
Proof.
Admitted.



(*
	From TracePattern analogs to trace lemmas
	included here because the proof is not complete


  It is commented instead of Admitted
  since it wasn't used in proving Theorem 1.

Lemma lemma_two_tracepat : forall (i:nat) (T:TracePat),
  (ithelement_tp T i <> Epsilon) <-> ((le 1 i) /\ (le i (tracepat_len T))).
Proof.
  intros i T.
  remember (tracepat_len T) as n.
  generalize Heqn.
  generalize T i.
  apply strongind with
      (P:=(fun n =>
      forall t0 i0,
        n=tracepat_len t0 ->
        (ithelement_tp t0 i0 <> Epsilon <-> 1 <= i0 <= n))).
  intros t0 i0.
  intros FOO.

  split.

  Case "->".
    intros HFOO.
    remember lemma_two_1_tracepat.
    symmetry in Heqn.

    assert (ithelement_tp t0 i0 = Epsilon).
       apply e. symmetry.
       apply FOO.

    rewrite H in HFOO.
    unfold not in HFOO.
    assert (Epsilon = Epsilon).
    reflexivity.
    apply HFOO in H0.
    inversion H0.
    intros H.
    inversion H as [H1 H2].
    assert (1 <=0).
    generalize H1 H2.
    apply le_trans.
    inversion H0.
    (* TracePat Proof Complete up to here *)

Admitted.

(* Copied over trace lemma_two stuff *)

  Case "<-".
  intros n0.
  intros Hyp.
  intros HH.
  destruct n0.
  split.
  intros HHH.
  assert (i0=1).
    assert (Epsilon = Epsilon). reflexivity.
    destruct i0.
    rewrite lemma_two_2_tracepat in HHH.
    apply HHH in H0.
    inversion H0.
    destruct i0.
    reflexivity.
    assert(forall t0 n0, ((S O) = tracepat_len t0) ->(ithelement_tp t0 (S (S n0)) = Epsilon)).
      intros t0 n0.
      intros HHHH.

      trace_pattern_cases

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
*)