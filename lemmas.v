Require Export tactic_notations.
Require Export unproven_lemmas.
Require Export mto_arith.
Require Export low_equivalence_properties.

Lemma lemmaone :
  forall t1 t2,
  (traceequiv t1 t2) -> ((tracelen t1) = (tracelen t2)).
Proof.
  intros t1 t2 H.

  trace_equiv_cases (induction H) Case;
  try (reflexivity).

  Case "refl_equiv".
    symmetry. apply IHtraceequiv.

  Case "assoc_equiv".
    simpl.  rewrite plus_assoc.  reflexivity.

  Case "trans_equiv".
    rewrite  <- IHtraceequiv2.  apply IHtraceequiv1.

  Case "epsilon_ident_equivr".
    simpl.  rewrite plus_0_r. reflexivity.

  Case "concat_decomp_equiv".
    simpl.
    rewrite IHtraceequiv1.
    rewrite IHtraceequiv2.
    reflexivity.
Qed.


Lemma lemmatwo_1 :
  forall t i,
  ((tracelen t)=0) -> (ithelement t i = epsilon).
Proof.
  intros t i.
  intros H.
  induction ( t).
  Case "read". inversion H.
  Case "readarr". inversion H.
  Case "write". inversion H.
  Case "writearr". inversion H.
  Case "fetch". inversion H.
  Case "orambank". inversion H.
  Case "concat".
    simpl in H.
    apply plus_is_O in H.
    simpl.
    destruct i as [| i'].
    SCase "i = 0'".
      reflexivity.
    SCase "i = S i'".
      destruct i'.
      SSCase "i = 1".
      destruct H as [H1 H2].
      destruct t1.
      SSSCase "read". inversion H1.
      SSSCase "readarr". inversion H1.
      SSSCase "write". inversion H1.
      SSSCase "writearr". inversion H1.
      SSSCase "fetch". inversion H1.
      SSSCase "orambank". inversion H1.
      SSSCase "concat".
        inversion H1.
        remember H1 as HH1.
        rewrite H1.
        simpl in H1.
        rewrite H1.
        apply IHt2.
        apply H2.
      SSSCase "epsilon".
        apply IHt2.
        apply H2.


      assert ((ble_nat (S (S i')) (tracelen t1)) = false).
        inversion H as [H1 H2].
        rewrite H1.
        simpl. reflexivity.




      rewrite H0.
      inversion H as [H1 H2].
      rewrite H1.
      simpl.
      apply IHt2.
      apply H2.

  Case "epsilon".
    simpl.
    destruct i.
    SCase "i = O".
      reflexivity.
    SCase "i = S n".
      destruct i.
      SSCase "i = 1". reflexivity.
      SSCase " i > 1". reflexivity.
Qed.

Lemma lemmatwo_2 :
  forall t, ithelement t 0 = epsilon.
Proof.
  intros t.
  trace_cases (induction t) Case;
  try(simpl; reflexivity).
Qed.

Lemma lemmatwo_3 :
  forall t n,
  (tracelen t = S (S n)) -> (exists t1, exists t2, t = concat t1 t2).
Proof.
  intros t n.
  unfold tracelen.

  trace_cases (destruct t) Case;
  try(intros H; inversion H).

  Case "concat".
    exists t1.
    exists t2.
    reflexivity.
Qed.


(*
A standard library version of plusright
  and cancel minus may exist.
*)

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
  rewrite plus_comm.
  symmetry.
  apply le_plus_minus.
  apply H.
Qed.


Lemma lemmatwo :
  forall i t,
  (ithelement t i <> epsilon) <-> ((le 1 i) /\ (le i (tracelen t))).
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
  rewrite -> plus_comm in H5.
  assert (forall a b c, (a+b<=a+c)-> (b<=c)).
  intros a b c.
  induction a.
  rewrite plus_O_n.
  rewrite plus_O_n.
  intros Hsub.
  apply Hsub.
  intros Hsub.
  rewrite plus_Sn_m in Hsub.
  rewrite plus_Sn_m in Hsub.
  inversion Hsub.
  apply IHa.
  rewrite H7.
  apply le_refl.
  apply IHa.
  assert (a+b <= S (a+b)).
  apply le_n_Sn.
  apply le_trans with (S (a+b)).
  apply H8.
  apply H7.
  apply H6 with (tracelen HH1).
  apply H5.
  rewrite <- plus_Sn_m.

  rewrite H2.
  apply iff_trans with (1<= S FOO <= tracelen HH2).
  apply H1.
  apply H3.
  simpl in HFOO.
  inversion HFOO.
Qed.


Lemma combo_six_seven :
  forall gamma e l T M1 M2 t1 t2 n1 n2,
  (exprTyping gamma e (lnat l) T) ->
  (gammavalid gamma M1) ->
  (gammavalid gamma M2) ->
  (exprSem M1 e t1 n1) ->
  (exprSem M2 e t2 n2) -> (t1 = t2).
Proof.
  intros gamma e l.
  destruct l.
  intros T M1 M2 t1 t2 n1 n2 HH1 HH2 HH3 HH4 HH5.
  assert (t1 = t2 /\ n1 = n2).
  apply lemmasix with gamma e T M1 M2; assumption.
  apply H.
  apply lemmaseven.
Qed.

Lemma sameExpr_sameStuff : forall M1 e, forall t1 t2 n1 n2,
  (exprSem M1 e t1 n1) -> (exprSem M1 e t2 n2) ->
  (t1 = t2 /\ n1 = n2).
Proof.
  intros M1 e.
  induction e.
  intros t1 t2 n1 n2.
  intros H1 H2.
  inversion H1.
  inversion H2.
  rewrite H8 in H0.
  inversion H0.
  rewrite H14 in *.
  rewrite H15 in *.
  rewrite <- H4 in H10.
  rewrite H10.
  split;
  reflexivity.
  intros t1 t2 n1 n2.
  intros H1 H2.
  inversion H1.
  inversion H2.
  assert (t0 = t4 /\ n0 = n4).
  apply IHe1;
  assumption.
  assert (t3 = t5 /\ n3 = n5).
  apply IHe2;
  assumption.
  rewrite H9.
  rewrite H18.
  inversion H19.
  inversion H20.
  rewrite H21.
  rewrite H22.
  rewrite H23.
  rewrite H24.
  split.
  reflexivity.
  reflexivity.
  intros t1 t2 n1 n2.
  intros H1 H2.
  inversion H1.
  inversion H2.
  rewrite H13 in H4.
  inversion H4.
  rewrite H20 in *.
  assert (t = t3 /\ n = n3).
  apply IHe.
  assumption.
  assumption.
  inversion H19.
  rewrite H22 in *.
  rewrite H23 in *.

  assert (n1 = n2).
  rewrite H15.
  rewrite H6.
  reflexivity.
  assert (t0 = t4).
  rewrite H18.
  rewrite H9.
  rewrite H24.
  rewrite H21.
  reflexivity.
  rewrite H25.
  split.
  reflexivity.
  apply H24.
  intros t1 t2 n1 n2 H1 H2.
  inversion H1.
  inversion H2.
  rewrite <- H8.
  rewrite <- H4.
  split;
  reflexivity.
Qed.


Lemma nonzerolength_prog : forall  p M1 M2 t ,
  (progSem M1 p t M2) -> ( 0 <> tracelen_withepsilon t).
Proof.
  intros p.
  induction p.
  intros  M1 M2 t.
  destruct l.
  intros H.
  destruct s.
  inversion H.
  intros HH.
  simpl in HH.
  inversion HH.
  inversion H.
  intros HH.
  simpl in HH.
  inversion HH.
  inversion H.
  intros HH.
  simpl in HH.
  inversion HH.
  inversion H.
  intros HH.
  simpl in HH.
  inversion HH.
  inversion H.
  intros HH.
  simpl in HH.
  inversion HH.
  intros t M1 M2.
  intros H.
  inversion H.
  intros HH.
  simpl in HH.
  symmetry in HH.
  apply plus_is_O in HH.
  inversion HH.
  apply IHp1 in H3.
  symmetry in H7.
  apply H3 in H7.
  inversion H7.
Qed.

Lemma nonzerolength_expr :
  forall M e t n,
  (exprSem M e t n) -> (0<> tracelen_withepsilon t).
Proof.
  intros M e.
  induction e.
  intros t n.
  intros H.
  inversion H.
  rewrite H3.
  destruct l.
  simpl.
  trivial.
  simpl.
  trivial.
  intros t n H.
  inversion H.
  intros HH.
  simpl in HH.
  symmetry in HH.
  apply plus_is_O in HH.
  inversion HH.
  apply IHe1 in H4.
  symmetry in H9.
  apply H4 in H9.
  inversion H9.
  intros t n H.
  inversion H.
  intros HH.
  simpl in HH.
  symmetry in HH.
  apply plus_is_O in HH.
  inversion HH.
  apply IHe in H2.
  symmetry in H9.
  apply H2 in H9.
  inversion H9.
  intros t n H.
  inversion H.
  simpl.
  trivial.
Qed.

Lemma atleastone : forall S2, 1 <= num_statements S2 .
Proof.
  intros S2.
  induction S2.
  destruct l.
  destruct s.
  simpl.
  apply le_refl.
  simpl.
  apply le_refl.
  simpl.
  apply le_refl.
  simpl.
  apply le_n_S.
  apply le_O_n.
  apply le_n_S.
  apply le_O_n.
  simpl.
  apply le_plus_trans.
  apply IHS2_1.
Qed.


Lemma whilecase :
  forall  n p p0 e t1 t2 M1 M1' M2 M2' l T gamma,
    tracelen_withepsilon t1 <= n ->
    tracelen_withepsilon t2 <= n ->
    (lowEquivalentMem M1 M2) ->
    (stmtSem M1 (labline p (stwhile e p0)) t1 M1') ->
    (stmtSem M2 (labline p (stwhile e p0)) t2 M2') ->
    (statementTyping gamma l (labline p (stwhile e p0)) T) ->
    (gammavalid gamma M1) ->
    (gammavalid gamma M2) ->
    (memTraceObliv gamma p0) ->

        ( traceequiv t1 t2 /\ lowEquivalentMem M1' M2' ).
Proof.
  intros n.
  apply strongind with
  (P:=(fun n:nat =>forall p p0 e t1 t2 M1 M1' M2 M2' l T gamma,
   tracelen_withepsilon t1 <= n->
   tracelen_withepsilon t2 <= n->
   (lowEquivalentMem M1 M2) ->
   (stmtSem M1 (labline p (stwhile e p0)) t1 M1') ->
   (stmtSem M2 (labline p (stwhile e p0)) t2 M2') ->
   (statementTyping gamma l (labline p (stwhile e p0)) T) ->
   (gammavalid gamma M1) ->
   (gammavalid gamma M2) ->
   (memTraceObliv gamma p0) ->
  (
  traceequiv t1 t2 /\ lowEquivalentMem M1' M2'
  ))).
  intros p p0 e t1 t2 M1 M1' M2 M2' l T gamma HH1 HH2 HH3 HH4 HH5 HH6 HH7 HH9.
  inversion HH4.
  rewrite <- H4 in HH1.
  simpl in HH1.
  inversion HH1.
  rewrite <- H1 in HH1.
  simpl in HH1.
  inversion HH1.
  (* for S n instead of n in base case *)
  (**
  rewrite <- H4 in HH1.
  simpl in HH1.
  inversion HH1.
  apply nonzerolength_expr in H3.
  apply plus_is_O in H9.
  inversion H9.
  symmetry in H8.
  apply H3 in H8.
  inversion H8.
  rewrite <- H1 in HH1.
  simpl in HH1.
  inversion HH1.
  symmetry in H7.
  apply nonzerolength_expr in H5.
  apply H5 in H7.
  inversion H7.
  **)
  intros n0.
  intros mm.
  intros p p0 e t1 t2 M1 M1' M2 M2' l T gamma HH1 HH2 HH3 HH4 HH5 HH6 HH7 HH8 HH9.

  inversion HH4.
  inversion HH5.
  inversion H7.
  inversion H16.
  assert (t = t3).
  inversion HH6.
  apply combo_six_seven with gamma e l0 T1 M1 M2 n1 n2;assumption.

  assert (traceequiv t5 t7 /\ lowEquivalentMem M6 M9).
  unfold memTraceObliv in HH9.
  apply HH9 with M1 M2;assumption.
  inversion H32.

  inversion H23.
  inversion H30.

  assert (traceequiv t9 t10 /\ lowEquivalentMem M1' M2').
  apply mm with (max (tracelen_withepsilon t9) (tracelen_withepsilon t10)) p p0 e M6 M9 l T gamma.
  assert ( (tracelen_withepsilon t9) =
  max (tracelen_withepsilon t9) (tracelen_withepsilon t10)\/
  (tracelen_withepsilon t10) =
   max (tracelen_withepsilon t9) (tracelen_withepsilon t10)).
  apply le_max_or.
  inversion H47.
  rewrite <- H48.
  rewrite <- H4 in HH1.
  apply nonzerolength_expr in H3.
  simpl in HH1.
  apply le_S_n in HH1.
  apply le_trans with (tracelen_withepsilon t + tracelen_withepsilon t0).
  destruct (tracelen_withepsilon t).
  assert (0=0).
  reflexivity.
  simpl.
  apply H3 in H49.
  inversion H49.
  rewrite <- H21.
  rewrite <- H37.
  simpl.
  rewrite plus_assoc.
  rewrite <- plus_Sn_m.
  rewrite <- plus_n_Sm.
  rewrite <- plus_Sn_m.
  apply le_plus_r.
  assumption.
  rewrite <- H48.
  rewrite <- H13 in HH2.
  apply nonzerolength_expr in H12.
  simpl in HH2.
  apply le_S_n in HH2.
  apply le_trans with (tracelen_withepsilon t3 + tracelen_withepsilon t4).
  destruct (tracelen_withepsilon t3).
  assert (0=0).
  reflexivity.
  simpl.
  apply H12 in H49.
  inversion H49.
  rewrite <- H28.
  rewrite <- H43.
  simpl.
  rewrite plus_assoc.
  rewrite <- plus_Sn_m.
  rewrite <- plus_n_Sm.
  rewrite <- plus_Sn_m.
  apply le_plus_r.
  assumption.
  apply le_max_l.
  apply le_max_r.

  assumption.
  assumption.
  assumption.
  assumption.
  apply stayvalid with M1 p0 t5.
  assumption.
  assumption.
  apply stayvalid with M2 p0 t7.
  assumption.
  assumption.
  assumption.
  split.
  apply concat_decomp_equiv.
  apply equal_equiv.
  apply concat_decomp_equiv.
  assert (t = t3).
  inversion HH6.
  apply combo_six_seven with gamma e l0 T1 M1 M2 n1 n2;
  assumption.
  rewrite H48.
  apply equal_equiv.
  apply concat_decomp_equiv.
  apply H33.
  apply concat_decomp_equiv.
  apply equal_equiv.
  inversion H47.
  assumption.
  inversion H47.
  assumption.
  assert ( t = t3 /\ n1 = 0).
  inversion HH6.
  destruct l0.
  apply lemmasix with gamma e T1 M1 M2.
  assumption.
  assumption.
  assumption.
  assumption.
  rewrite H13.
  assumption.
  inversion H23.
  inversion H15.
  apply H6 in H17.
  inversion H17.

  inversion HH5.
  assert ( t = t0 /\ 0 = n1).
  inversion HH6.
  destruct l0.
  apply lemmasix with gamma e T1 M1' M2.
  assumption.
  rewrite <- H4.
  assumption.
  assumption.
  assumption.
  assumption.
  inversion H23.
  inversion H15.
  symmetry in H17.
  apply H13 in H17.
  inversion H17.
  assert (t = t0).
  inversion HH6.
  apply combo_six_seven with gamma e l0 T1 M1' M2' 0 0.
  assumption.
  rewrite <- H4.
  assumption.
  rewrite <- H11.
  assumption.
  assumption.
  assumption.
  rewrite H13.
  rewrite <- H4.
  rewrite <- H11.
  split.
  apply equal_equiv.
  assumption.
Qed.


(* TracePattern analogs to trace lemmas  *)

Lemma lemma_one_tracepat :
  forall (T1 T2:TracePat),
  TracePatEquiv T1 T2 ->
  (tracepat_len T1) = (tracepat_len T2).
Proof.
  intros.

  trace_pattern_equiv_cases (induction H) Case;
  try (reflexivity).

  Case "Assoc_equiv".
  simpl. rewrite plus_assoc. reflexivity.

  Case "Trans_equiv".
    rewrite <- IHTracePatEquiv2. apply IHTracePatEquiv1.

  Case "Epsilon_ident_equivr".
    simpl. rewrite plus_0_r. reflexivity.

  Case "Concat_decomp_equiv".
    simpl.
    rewrite IHTracePatEquiv1.
    rewrite IHTracePatEquiv2.
    reflexivity.
Qed.

Lemma lemma_two_1_tracepat :
  forall (T:TracePat) (i:nat),
  ((tracepat_len T) = 0) ->
  (ithelement_tp T i = Epsilon).
Proof.
  intros.

  trace_pattern_cases (induction T) Case;
  try (inversion H).

  Case "Concat".
    destruct i.
    SCase "i = 0". reflexivity.

    SCase "i > 0".
      destruct i.

      SSCase "i = 1".

        trace_pattern_cases (destruct T1) SSSCase;
        try (intuition).

        SSSCase "Concat". intuition.
  Case "Epsilon".
    destruct i.
    SCase "i = 0". reflexivity.
    SCase "i > 0".
      destruct i.
      SSCase "i = 1". reflexivity.
      SSCase "i > 1". reflexivity.
Qed.

Lemma lemma_two_2_tracepat :
  forall (T:TracePat),
  ithelement_tp T 0 = Epsilon.
Proof.
  intros T.
  trace_pattern_cases (induction T) Case;
  try (simpl; reflexivity).
Qed.

Lemma lemma_two_3_tracepat :
  forall (T:TracePat) (n:nat),
  (tracepat_len T = S (S n)) ->
  (exists T1, exists T2, T = Concat T1 T2).
Proof.
  intros T n.
  unfold tracepat_len.

  trace_pattern_cases (destruct T) Case;
  try (intros H; inversion H).

  Case "Concat".
    exists T1.
    exists T2.
    reflexivity.
Qed.