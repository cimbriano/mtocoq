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


Theorem Theoremone : forall S (gamma:environment) (l:label) (T:TracePat),
((progTyping gamma l S T) -> 
(memTraceObliv gamma S)).
Proof.
intros S gamma l T.
intros H.
destruct H.
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
(*assign case Note, likely garbage past this point*)
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
(**rewrite H25.
rewrite H18.
rewrite H11.
rewrite H4.**)
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


.
assert (gamma v = Some (lnat l)).

apply HH2.


destruct l4.
rewrite H39.
apply HH2.
apply HH3.
apply H14.
apply H28.
assert (t1 = t2).
destruct l4.


split.
remember lemmasix.
apply a with gamma e  T0 M1 M2 t0 t4 n n0 in H35 .
inversion H35.
rewrite H39.
rewrite H40.
assert (l=l1).
apply labelequal_int with M1 M2 v n1 n2.
apply HH1.
apply H15.
apply H29.
rewrite H41.
apply equal_equiv.
apply HH2.
apply HH3.
apply H14.
apply H28.
apply 
apply concat_decomp_equiv.
apply equal_equiv.
apply concat_decomp_equiv.
apply equal_equiv.

split.
apply concat_decomp_equiv.
apply equal_equiv.
apply concat_decomp_equiv.
assumption.

simpl.
intros M1.
destruct H.
admit.


induction l0.
inversion .
intros H.
Admitted.