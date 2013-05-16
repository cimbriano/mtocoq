Require Export Sflib.
Require Export strong_induction.
Require Export FSets.
Require Export Peano.
Require Export core.
Require Export semantics.
Require Export typing.
Require Export tactic_notations.


Fixpoint tracepat_len (tp : TracePat) : nat :=
  match tp with
  | Epsilon => 0
  | Concat tp1 tp2 => plus (tracepat_len tp1) (tracepat_len tp2)
  | _ => 1
  end.

Fixpoint ithelement_tp (tp:TracePat) (i:nat) : TracePat:=
  match i with
  | O   => Epsilon
  | S O =>
      match tp with
      | Concat tp1 tp2 =>
         match tp1 with
         | Epsilon => ithelement_tp tp2 i
         | _ => ithelement_tp tp1 i
         end
      | Epsilon        => Epsilon
      |              _ => tp
      end
  | S (S n) =>
      match tp with
      | Concat tp1 tp2 => Epsilon
      | _ => Epsilon
      end
  end.


Lemma lemma_one_tracepat : forall (T1 T2:TracePat),
  TracePatEquiv T1 T2 -> (tracepat_len T1) = (tracepat_len T2).
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


Lemma lemma_two_1_tracepat : forall (T:TracePat) (i:nat),
  ((tracepat_len T) = 0) -> (ithelement_tp T i = Epsilon).
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


Lemma lemma_two_2_tracepat : forall (T:TracePat),
  ithelement_tp T 0 = Epsilon.
Proof.
  intros T.
  trace_pattern_cases (induction T) Case;
  try (simpl; reflexivity).
Qed.

Lemma lemma_two_3_tracepat : forall (T:TracePat) (n:nat),
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
























Lemma lemma_five : forall (tp1 tp2 : TracePat),
  tracePequiv tp1 tp2 <-> 
  forall (i:nat),
    (ithelement_tp tp1 i) = (ithelement_tp tp2 i).
