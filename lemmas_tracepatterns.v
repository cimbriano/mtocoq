Require Export Sflib.

Require Export FSets.

Require Export Peano.

Require Export core.

Require Export semantics.

Require Export typing.

Fixpoint tracepat_len (tp : TracePat) (i : nat) :=
  match tp with
  | Epsilon => 0
  | Concat tp1 tp2 => plus (tracepat_len tp1 i) (tracepat_len tp2 i) 
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

Lemma lemma_five : forall (tp1 tp2 : TracePat),
  tracePequiv tp1 tp2 <-> 
  forall (i:nat),
    (ithelement_tp tp1 i) = (ithelement_tp tp2 i).
