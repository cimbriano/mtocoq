Require Export mto_paper_definitions.

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


Lemma lowEquiv_trans :
	forall M1 M2 M3, (lowEquivalentMem M1 M2) ->
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


Lemma lowEquiv_persist :
	forall M1 M2 x v,
	(lowEquivalentMem M1 M2) ->
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

Lemma lowEquiv_sym :
	forall M1 M2,
	(lowEquivalentMem M1 M2) -> (lowEquivalentMem M2 M1).
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

Lemma lowEquiv_persist_high_int :
	forall M1 x v o,
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


Lemma lowEquiv_persist_high_arr :
	forall M1 x v o,
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


