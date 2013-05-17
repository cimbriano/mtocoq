Require Export Sflib.
Require Export FSets.
Require Export Peano.
Require Export core.
Require Export semantics.
Require Export typing.
Require Export lemmas.
Require Export mto_arith.
Require Export low_equivalence_properties.


Theorem Theoremone :
	forall S (gamma:environment) (l:label) (T:TracePat),
	((progTyping gamma l S T) ->
	(memTraceObliv gamma S)).
Proof.
	intros S.
	remember (num_statements S).
	generalize Heqn.
	generalize S.
	apply strongind with
	(P:=(fun n => forall S, n=num_statements S -> (
	forall gamma l T, progTyping gamma l S T -> memTraceObliv gamma S
	))).
	intros SS H.
	unfold num_statements in H.
	assert (False).
	induction SS.
	destruct l.
	destruct s;
	inversion H.
	symmetry in H.
	apply plus_is_O in H.
	inversion H.
	symmetry in H0.
	apply IHSS1 in H0.
	inversion H0.
	inversion H0.
	(*base case on length done *)
	intros nn mm.
	intros SS.
	intros DEFLEN.

	intros gamma l T.
	intros H.

	clear S n Heqn.


	induction H.
	induction s.
	(*epsilon case *)
	intros M1 M2 t1 M1' t2 M2'.
	intros HH1 HH4 HH5 HH2 HH3.
	inversion HH2.
	inversion H6.
	inversion HH3.
	inversion H16.
	split.
	apply equal_equiv.
	rewrite <- H20.
	rewrite <- H10.
	apply HH1.
	(*assign case*)
	intros M1 M2 t1 M1' t2 M2'.
	intros HH1 HH2 HH3 HH4 HH5.
	inversion HH1.
	inversion HH4.
	inversion H8.
	inversion HH5.
	inversion H22.
	inversion H.
	assert (t0 = t4).
	destruct l2.
	remember lemmasix.
	apply a with gamma e T0 M1 M2 t0 t4 n n0 in H36.
	inversion H36.
	apply H40.
	assumption.
	assumption.
	assumption.
	assumption.
	remember lemmaseven.
	apply e3 with gamma e o T0 M1 M2 t0 t4 n n0 in H36;
	repeat assumption.
	assert (l = l4).
	unfold gammavalid in HH2.
	assert (((gamma v = Some (lnat l)) <-> (exists n, M1 v = Some (vint n l))) /\(
	 (gamma v = Some (larr l)) <-> (exists n, M1 v = Some (varr n l)))).
	apply HH2.
	apply proj1 in H41.
	apply proj2 in H41.
	assert (gamma v = Some( lnat l)).
	apply H41.
	exists n1.
	assumption.
	assert (Some (lnat l4) = Some (lnat l)).
	rewrite <- H42.
	rewrite <- H38.
	reflexivity.
	inversion H43.
	reflexivity.
	rewrite <- H41 in *.
	assert (l = l1).
	unfold gammavalid in HH3.
	assert (((gamma v = Some (lnat l1)) <-> (exists n, M2 v = Some (vint n l1))) /\(
	 (gamma v = Some (larr l1)) <-> (exists n, M2 v = Some (varr n l1)))).
	apply HH3.
	apply proj1 in H42.
	apply proj2 in H42.
	assert (gamma v = Some( lnat l1)).
	apply H42.
	exists n2.
	assumption.
	assert (Some (lnat l1) = Some (lnat l)).
	rewrite <- H43.
	rewrite <- H38.
	reflexivity.
	inversion H44.
	reflexivity.
	rewrite <- H42 in *.
	rewrite H40 in *.
	destruct l.


	assert (l2 = low).
	inversion H39.
	unfold mtojoin in H44.
	destruct l0.
	symmetry.
	assumption.
	inversion H44.
	rewrite H43 in *.


	remember lemmasix.
	apply a with gamma e T0 M1 M2 t0 t4 n n0 in H36.
	inversion H36.
	rewrite H45.
	split.
	apply equal_equiv.
	apply lowEquiv_persist.
	assumption.
	assumption.
	assumption.
	rewrite H40.
	assumption.


	assumption.
	split.
	unfold evttrace.
	apply equal_equiv.
	apply lowEquiv_trans with M1.
	apply lowEquiv_persist_high_int.
	exists n1.
	apply H16.
	apply lowEquiv_trans with M2.
	assumption.
	apply lowEquiv_sym.
	apply lowEquiv_persist_high_int.
	exists n2.
	apply H30.

	(*array assign case*)
	intros M1 M2 t1 M1' t2 M2'.
	intros HH1 HH2 HH3 HH4 HH5.
	inversion HH1.
	inversion HH4.
	inversion H8.
	inversion HH5.
	inversion H25.
	inversion H.

	assert (l = l5).
	unfold gammavalid in HH2.
	assert (((gamma v = Some (lnat l)) <-> (exists n, M1 v = Some (vint n l))) /\(
	 (gamma v = Some (larr l)) <-> (exists n, M1 v = Some (varr n l)))).
	apply HH2.
	apply proj2 in H48.
	apply proj2 in H48.
	assert (gamma v = Some( larr l)).
	apply H48.
	exists m.
	assumption.
	assert (Some (larr l5) = Some (larr l)).
	rewrite <- H49.
	rewrite <- H46.
	reflexivity.
	inversion H50.
	reflexivity.
	rewrite <- H48 in *.

	assert (l = l1).
	unfold gammavalid in HH3.
	assert (((gamma v = Some (lnat l1)) <-> (exists n, M2 v = Some (vint n l1))) /\(
	 (gamma v = Some (larr l1)) <-> (exists n, M2 v = Some (varr n l1)))).
	apply HH3.
	apply proj2 in H49.
	apply proj2 in H49.
	assert (gamma v = Some( larr l1)).
	apply H49.
	exists m0.
	assumption.
	assert (Some (larr l1) = Some (larr l)).
	rewrite <- H50.
	rewrite <- H46.
	reflexivity.
	inversion H51.
	reflexivity.
	rewrite <- H49 in *.

	destruct l.
	assert (l2 = low).
	inversion H47.
	unfold mtojoin in H51.
	simpl in H51.
	destruct l2.
	reflexivity.
	inversion H51.

	assert (l3 = low).
	inversion H47.
	rewrite H50 in H52.
	simpl in H52.
	unfold mtojoin in H52.
	destruct l3.
	reflexivity.
	inversion H52.
	rewrite H51 in *.
	rewrite H50 in *.

	assert (n0 = n1 /\ t0 = t5).
	remember lemmasix.
	apply a with gamma e T1 M1 M2 t0 t5 n1 n0 in H43.
	inversion H43.
	split.
	symmetry.
	apply H53.
	apply H52.
	assumption.
	assumption.
	assumption.
	assumption.

	assert (n2 = n3 /\ t3 = t6).
	remember lemmasix.
	apply a with gamma e0 T2 M1 M2 t3 t6 n2 n3 in H45.
	inversion H45.
	split.
	apply H54.
	apply H53.
	assumption.
	assumption.
	assumption.
	assumption.
	inversion H52.
	inversion H53.
	rewrite H54 in *.
	rewrite H55 in *.
	rewrite H56 in *.
	rewrite H57 in *.

	split.
	apply equal_equiv.
	assert (m1 = m2).
	rewrite H36.
	rewrite H19.
	assert (m = m0).
	unfold lowEquivalentMem in HH1.
	inversion HH1.
	assert ((M1 v = Some (varr m low)) <->(M2 v = Some (varr m low))).
	apply H59.
	apply H60 in H18.
	rewrite H18 in H35.
	inversion H35.
	reflexivity.
	rewrite H58.
	reflexivity.
	rewrite H58.
	apply lowEquiv_persist.
	assumption.


	assert (t0 = t5).
	destruct l2.
	remember lemmasix.
	apply a  with gamma e T1 M1 M2 t0 t5 n1 n0 in H43.
	inversion H43.
	apply H50.
	assumption.
	assumption.
	assumption.
	assumption.
	remember lemmaseven.
	apply e7 with gamma e o0 T1 M1 M2 t0 t5 n1 n0 in H43.
	apply H43.
	assumption.
	assumption.
	assumption.
	assumption.
	rewrite H50 in *.

	assert (t3 = t6).
	destruct l3.
	remember lemmasix.
	apply a  with gamma e0 T2 M1 M2 t3 t6 n2 n3 in H45.
	inversion H45.
	apply H51.
	assumption.
	assumption.
	assumption.
	assumption.
	remember lemmaseven.
	apply e7 with gamma e0 o0 T2 M1 M2 t3 t6 n2 n3 in H45.
	apply H45.
	assumption.
	assumption.
	assumption.
	assumption.
	rewrite H51 in *.
	split.
	apply equal_equiv.

	apply lowEquiv_trans with M1.
	apply lowEquiv_persist_high_arr.
	exists m.
	apply H18.
	apply lowEquiv_trans with M2.
	assumption.
	apply lowEquiv_sym.
	apply lowEquiv_persist_high_arr.
	exists m0.
	apply H35.

	(*if case *)
	intros M1 M2 t1 M1' t2 M2'.
	intros HH1 HH2 HH3 HH4 HH5.
	inversion H.

	remember (mtojoin l l0).
	destruct (l2).
	unfold mtojoin in Heql2.
	destruct l.
	inversion HH4.
	inversion HH5.
	inversion H18.
	inversion H24.


	assert (t3=t5 /\ n = n0).
	remember lemmasix.
	apply a with gamma e T0 M1 M2 t3 t5 n n0 in H5;
	repeat assumption.
	assert (traceequiv t4 t6 /\ lowEquivalentMem M1' M2' ).
	assert (progTyping gamma low p0 T1 -> memTraceObliv gamma p0).
	apply mm with (m:= num_statements p0).
	unfold num_statements in DEFLEN.
	inversion DEFLEN.
	apply le_plus_l.
	reflexivity.
	assert (memTraceObliv gamma p0).
	apply H46.
	assumption.
	unfold memTraceObliv in H47.
	apply H47 with M1 M2 ;
	assumption.
	inversion H46.
	split.
	inversion H45.
	rewrite H49.
	apply concat_decomp_equiv.
	apply equal_equiv.
	apply concat_decomp_equiv.
	apply equal_equiv.
	assumption.
	assumption.


	assert (t3=t5 /\ n = n0).
	remember lemmasix.
	apply a with gamma e T0 M1 M2 t3 t5 n n0 in H5;
	repeat assumption.
	inversion H45.
	rewrite H47 in *.
	rewrite H43 in H33.
	assert (0=0).
	reflexivity.
	apply H33 in H48.
	inversion H48.

	inversion H24.

	assert (t3=t5 /\ n = n0).
	remember lemmasix.
	apply a with gamma e T0 M1 M2 t3 t5 n n0 in H5;
	repeat assumption.
	inversion H45.
	rewrite H47 in *.
	rewrite H33 in H43.
	assert (0=0).
	reflexivity.
	apply H43 in H48.
	inversion H48.


	assert (t3=t5 /\ n = n0).
	remember lemmasix.
	apply a with gamma e T0 M1 M2 t3 t5 n n0 in H5;
	repeat assumption.
	assert (traceequiv t4 t6 /\ lowEquivalentMem M1' M2' ).
	assert (progTyping gamma low p1 T2 -> memTraceObliv gamma p1).
	apply mm with (m:= num_statements p1).
	unfold num_statements in DEFLEN.
	inversion DEFLEN.
	apply le_plus_r.
	reflexivity.
	assert (memTraceObliv gamma p1).
	apply H46.
	assumption.
	unfold memTraceObliv in H47.
	apply H47 with M1 M2 ;
	assumption.
	inversion H46.
	split.
	inversion H45.
	rewrite H49.
	apply concat_decomp_equiv.
	apply equal_equiv.
	apply concat_decomp_equiv.
	apply equal_equiv.
	assumption.
	assumption.
	inversion Heql2.

	(*high if case*)

	remember lemmatwelve.
	inversion H.
	inversion HH4.
	inversion H30.
	inversion HH5.
	inversion H46.
	assert (traceequiv t3 t6 /\ lowEquivalentMem M1' M2').
	assert (progTyping gamma (o_high o) p0 T1 -> memTraceObliv gamma p0).
	apply mm with (m:= num_statements p0).
	unfold num_statements in DEFLEN.
	rewrite plus_Sn_m in DEFLEN.
	inversion DEFLEN.
	unfold num_statements.
	apply le_plus_l.
	reflexivity.
	assert (memTraceObliv gamma p0).
	apply H57.
	assumption.
	unfold memTraceObliv in H58.
	apply H58 with M1 M2;
	assumption.
	assert (t0 = t5).
	apply combo_six_seven with gamma e l2 T6 M1 M2 n n0; assumption.
	rewrite H58.
	split.
	apply concat_decomp_equiv.
	apply equal_equiv.
	apply concat_decomp_equiv.
	apply equal_equiv.
	inversion H57.
	assumption.
	inversion H57.
	assumption.

	assert (traceequiv t3 t6 /\ lowEquivalentMem M1' M2').
	apply a with gamma (o_high o) p0 p1 T1 T2 M1 M2.
	assumption.
	assumption.
	apply H11.
	intros HH.
	inversion HH.
	assumption.
	assumption.
	assumption.
	assumption.


	assert (t0 = t5).
	apply combo_six_seven with gamma e l2 T6 M1 M2 n n0; assumption.
	split.
	apply concat_decomp_equiv.
	apply equal_equiv.
	apply concat_decomp_equiv.
	rewrite H58.
	apply equal_equiv.
	inversion H57.
	assumption.
	inversion H57.
	assumption.

	inversion HH5.
	inversion H46.

	assert (traceequiv t3 t6 /\ lowEquivalentMem M1' M2').
	apply a with gamma (o_high o) p1 p0 T2 T1 M1 M2.
	assumption.
	assumption.
	apply TracePatEquiv_sym.
	apply H11.
	intros HH.
	inversion HH.
	assumption.
	assumption.
	assumption.
	assumption.


	assert (t0 = t5).
	apply combo_six_seven with gamma e l2 T6 M1 M2 n n0; assumption.
	split.
	apply concat_decomp_equiv.
	apply equal_equiv.
	apply concat_decomp_equiv.
	rewrite H58.
	apply equal_equiv.
	inversion H57.
	assumption.
	inversion H57.
	assumption.

	assert (traceequiv t3 t6 /\ lowEquivalentMem M1' M2').
	assert (progTyping gamma (o_high o) p1 T2 -> memTraceObliv gamma p1).
	apply mm with (m:= num_statements p1).
	unfold num_statements in DEFLEN.
	rewrite plus_Sn_m in DEFLEN.
	inversion DEFLEN.
	unfold num_statements.
	apply le_plus_r.
	reflexivity.
	assert (memTraceObliv gamma p1).
	apply H57.
	assumption.
	unfold memTraceObliv in H58.
	apply H58 with M1 M2;
	assumption.

	assert (t0 = t5).
	apply combo_six_seven with gamma e l2 T6 M1 M2 n n0; assumption.
	split.
	apply concat_decomp_equiv.
	apply equal_equiv.
	apply concat_decomp_equiv.
	rewrite H58.
	apply equal_equiv.
	inversion H57.
	assumption.
	inversion H57.
	assumption.

	(* beginning while case *)

	intros M1 M2 t1 M1' t2 M2'.
	intros HH1 HH2 HH3 HH4 HH5.
	inversion HH4.
	inversion HH5.
	inversion H.
	assert (l = low).
	destruct l.
	reflexivity.
	destruct l0.
	simpl in H21.
	inversion H21.
	simpl in H21.
	inversion H21.
	assert (l0 = low).
	destruct l0.
	reflexivity.
	destruct l.
	simpl in H21.
	inversion H21.
	simpl in H21.
	inversion H21.
	rewrite H22 in *.
	rewrite H23 in *.
	clear H22 H23 l l0 H17 H21 l.

	assert (forall t1 t2 n1 n2, (exprSem M1 e t1 n1)-> (exprSem M2 e t2 n2) -> (t1 = t2 /\ n1 = n2)).
	intros tt1 tt2 nn1 nn2.

	intros HHH1 HHH2.
	apply lemmasix with gamma e T1 M1 M2 tt1 tt2 nn1 nn2 in H18 .
	apply H18.
	repeat assumption.
	assumption.
	assumption.
	assumption.

	assert (traceequiv t t0/\ lowEquivalentMem M1' M2').
	apply whilecase  with (max (tracelen_withepsilon t) (tracelen_withepsilon t0)) p p0 e M1 M2 low T gamma.
	apply le_max_l.
	apply le_max_r.
	assumption.
	assumption.
	assumption.
	assumption.
	assumption.
	assumption.
	apply mm with (num_statements p0) low T2.
	apply le_S_n.
	rewrite DEFLEN.
	simpl.
	apply le_refl.
	reflexivity.
	assumption.

	split.
	apply concat_decomp_equiv.
	apply equal_equiv.
	inversion H21.
	assumption.
	inversion H21.
	assumption.

	(*program concatenation*)
	intros M1 M2 t1 M1' t2 M2'.
	intros HH1 HH2 HH3 HH4 HH5.
	inversion HH4.
	inversion HH5.
	assert (memTraceObliv gamma S1).
	assert (1 <= num_statements S2).
	apply atleastone.
	simpl in DEFLEN.
	assert ( num_statements S1<=nn).
	apply le_S_n.
	rewrite DEFLEN.
	assert (S (num_statements S1) = num_statements S1 +1).
	omega.
	rewrite H16.
	apply plus_le_compat_l.
	assumption.

	apply mm with (num_statements S1) l0 T1.
	assumption.
	reflexivity.
	assumption.
	assert (memTraceObliv gamma S2).
	assert (1 <= num_statements S1).
	apply atleastone.
	simpl in DEFLEN.
	assert ( num_statements S2<=nn).
	apply le_S_n.
	rewrite DEFLEN.
	assert (S (num_statements S2) = 1+ num_statements S2 ).
	omega.
	rewrite H17.
	apply plus_le_compat_r.
	assumption.

	apply mm with (num_statements S2) l0 T2.
	assumption.
	reflexivity.
	assumption.
	assert (traceequiv t0 t4 /\ lowEquivalentMem M0 M5).
	unfold memTraceObliv in H15.
	apply H15 with M1 M2; assumption.
	inversion H17.
	assert(gammavalid gamma M0).
	apply stayvalid with M1 S1 t0;
	assumption.
	assert (gammavalid gamma M5).
	apply stayvalid with M2 S1 t4;
	assumption.
	assert (traceequiv t3 t5 /\ lowEquivalentMem M1' M2').
	unfold memTraceObliv in H16.
	apply H16 with M0 M5;
	assumption.

	split.
	inversion H17.
	inversion H22.
	apply concat_decomp_equiv.
	apply H23.
	apply H25.
	inversion H22.
	apply H24.
Qed.