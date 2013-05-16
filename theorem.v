Require Export Sflib.

Require Export FSets.

Require Export Peano.

Require Export core.

Require Export semantics.

Require Export typing.

Require Export lemmas.

(**
Lemma labelequal_int : forall M1 M2 x l1 l2 n1 n2, (lowEquivalentMem M1 M2) ->
(M1 x = Some (vint n1 l1)) -> (M2 x = Some (vint n2 l2)) ->
(l1 = l2).
Proof.
Admitted.
**)

Lemma sameExpr_sameStuff : forall M1 e, forall t1 t2 n1 n2,
(exprSem M1 e t1 n1) -> (exprSem M1 e t2 n2) ->
(t1 = t2 /\ n1 = n2).
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

Lemma sameProg_sameTrace : forall M1 M1' p1 t1 t2,
(progSem M1 p1 t1 M1') -> (progSem M1 p1 t2 M1') ->
(t1 = t2).
Proof.
intros M1 M1' p1.
induction p1.
destruct l.
induction s.
intros t1 t2 H1 H2.
inversion H1.
inversion H2.
inversion H6.
inversion H12.
reflexivity.
intros t1 t2 H1 H2.
inversion H1.
inversion H2.
inversion H6.
inversion H12.
assert (t3 = t4 /\ n = n0).
apply sameExpr_sameStuff with M1 e;
assumption.
inversion H29.
rewrite H20 in H28.
inversion H28.
rewrite H31.
rewrite H30.
reflexivity.
intros t1 t2 H1 H2.
inversion H1.
inversion H2.
inversion H6.
inversion H12.
assert (t3 = t5 /\ n1 = n0).
apply sameExpr_sameStuff with M1 e;
assumption.
assert (t4 = t6 /\ n2 = n3).
apply sameExpr_sameStuff with M1 e0;
assumption.
inversion H35.
inversion H36.
rewrite H37.
rewrite H38.
rewrite H39.
rewrite H40.
rewrite H33 in H22.
inversion H22.
reflexivity.
intros t1 t2 H1 H2.
inversion H1.
inversion H2.
assert (t = t0).
inversion H6.
inversion H12.
assert (t3 = t5 /\ n = n0).
apply sameExpr_sameStuff with M1 e;
assumption.
(* gave up for now *)
Admitted.





Lemma lowEquiv_persist : forall M1 M2 x v, (lowEquivalentMem M1 M2) ->
(lowEquivalentMem (memdefine M1 x v) (memdefine M2 x v)).
Proof.
intros M1 M2 x v H.
unfold lowEquivalentMem.
split.
intros x0 v0.
unfold memdefine.
remember (varideq x0 x).
destruct b.
apply iff_refl.
apply H.
intros x0 v0.
unfold memdefine.
remember (varideq x0 x).
destruct b.
apply iff_refl.
apply H.
Qed.

Lemma lowEquiv_sym : forall M1 M2, (lowEquivalentMem M1 M2) -> (lowEquivalentMem M2 M1).
Proof.
intros M1 M2 H.
unfold lowEquivalentMem in *.
split.
intros x v.
apply iff_sym.
apply H.
intros x v.
apply iff_sym.
apply H.
Qed.

Lemma lowEquiv_persist_high_int : forall M1 x v o,
(exists v1, M1 x = Some (vint v1 (o_high o))) ->
(lowEquivalentMem (memdefine M1 x (vint v (o_high o))) M1).
Proof.
intros M1 x v o H.
unfold lowEquivalentMem.
split.
intros x0 v0.
unfold memdefine.
remember (varideq x0 x).
destruct b.
split.
intros HH.
inversion HH.

intros HH.
unfold varideq in Heqb.
destruct x0.
destruct i.
destruct x.
destruct i.
remember (beq_nat n n0).
destruct b.
symmetry in Heqb0.
apply beq_nat_true in Heqb0.
rewrite Heqb0 in HH.
rewrite HH in H.
inversion H.
inversion H0.
inversion Heqb.
apply iff_refl.


intros x0 v0.
unfold memdefine.
unfold varideq.
destruct x0.
destruct x.
destruct i.
destruct i0.
remember (beq_nat n n0).
destruct b.
split.
intros HH.
inversion HH.
intros HH.
symmetry in Heqb.
apply beq_nat_true in Heqb.
rewrite Heqb in HH.
rewrite HH in H.
inversion H.
inversion H0.
apply iff_refl.
Qed.


Lemma lowEquiv_persist_high_arr : forall M1 x v o,
(exists v1, M1 x = Some (varr v1 (o_high o))) ->
(lowEquivalentMem (memdefine M1 x (varr v (o_high o))) M1).
Proof.
intros M1 x v o H.
unfold lowEquivalentMem.
split.
intros x0 v0.
unfold memdefine.
remember (varideq x0 x).
destruct b.
split.
intros HH.
inversion HH.

intros HH.
unfold varideq in Heqb.
destruct x0.
destruct i.
destruct x.
destruct i.
remember (beq_nat n n0).
destruct b.
symmetry in Heqb0.
apply beq_nat_true in Heqb0.
rewrite Heqb0 in HH.
rewrite HH in H.
inversion H.
inversion H0.
inversion Heqb.
apply iff_refl.


intros x0 v0.
unfold memdefine.
unfold varideq.
destruct x0.
destruct x.
destruct i.
destruct i0.
remember (beq_nat n n0).
destruct b.
split.
intros HH.
inversion HH.
intros HH.
symmetry in Heqb.
apply beq_nat_true in Heqb.
rewrite Heqb in HH.
rewrite HH in H.
inversion H.
inversion H0.
apply iff_refl.
Qed.

Lemma lowEquiv_trans : forall M1 M2 M3, (lowEquivalentMem M1 M2) ->
(lowEquivalentMem M2 M3) ->
(lowEquivalentMem M1 M3).
Proof.
intros M1 M2 M3 H1 H2.
unfold lowEquivalentMem in *.
split.
intros x v.
apply iff_trans with (M2 x = Some (vint v low)).
apply H1.
apply H2.
intros x v.
apply iff_trans with (M2 x = Some (varr v low)).
apply H1.
apply H2.
Qed.

Lemma lowEquiv_refl : forall M, (lowEquivalentMem M M).
Proof.
intros M.
unfold lowEquivalentMem.
split.
intros x v.
apply iff_refl.
intros x v.
apply iff_refl.
Qed.

Fixpoint num_statements (S:program) : nat :=
match S with
|(oneLineProg (labline _ (stif _ S1 S2))) => 1 + (num_statements S1) + (num_statements S2)
|(oneLineProg (labline _ (stwhile _ S1 ))) => 1 + (num_statements S1)
|(oneLineProg _ ) => 1
|(progcat S1 S2) => (num_statements S1) + (num_statements S2)
end.


Theorem Theoremone : forall S (gamma:environment) (l:label) (T:TracePat),
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
admit.
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
(*assert (forall gamma l T, progTyping gamma l p0 T -> memTraceObliv gamma p0).*)
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
(*assert (forall gamma l T, progTyping gamma l p0 T -> memTraceObliv gamma p0).*)
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

inversion H6.
inversion H12.
admit.
admit.
inversion H12.
admit.
assert (t3 = t5 /\ n = 0).
apply lemmasix with gamma e T1 M1 M2' t3 t5 n 0 in H18.
inversion H18.
apply H27 in H37.
inversion H37.
assumption.
assumption.
assumption.
assumption.

inversion H37.
inversion H28.

inversion H42.
rewrite H43 in *.



assert (progTyping gamma low (progcat p0 (oneLineProg (labline p (stwhile e p0))))
 (Concat T2 (Concat (Fetch p) T))).

apply TSeq.
assumption.
apply TLab.
assumption.
apply lowlab.


assert (memTraceObliv gamma (progcat p0 (oneLineProg (labline p (stwhile e p0))))).
apply mm with nn.


