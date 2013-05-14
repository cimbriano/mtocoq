Require Export Sflib.
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
  tracePequiv T1 T2 -> (tracepat_len T1) = (tracepat_len T2).
Proof.
  intros.

  trace_pattern_equiv_cases (induction H) Case;
  try (reflexivity).

  Case "assoc_equiv".
  simpl. rewrite plus_assoc. reflexivity.

  Case "trans_equiv".
    rewrite <- IHtracePequiv2. apply IHtracePequiv1.

  Case "epsilon_ident_equivr".
    simpl. rewrite plus_0_r. reflexivity.

  Case "concat_decomp_equiv".
    simpl.
    rewrite IHtracePequiv1.
    rewrite IHtracePequiv2.
    reflexivity.
Qed.


Lemma lemma_five : forall (tp1 tp2 : TracePat),
  tracePequiv tp1 tp2 <-> 
  forall (i:nat),
    (ithelement_tp tp1 i) = (ithelement_tp tp2 i).
