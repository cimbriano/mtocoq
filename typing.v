Require Export Sflib.
Require Export FSets.
Require Export Peano.
Require Export core.

Inductive labeledType : Type :=
  | larr :  label -> labeledType
  | lnat :  label -> labeledType.

Definition environment: Type := variable -> (option labeledType).

Inductive TracePat : Type :=
  | Read       : variable -> TracePat
  | Write      : variable -> TracePat
  | Readarr    : variable -> TracePat
  | Writearr   : variable -> TracePat
  | Loop       : location -> TracePat -> TracePat -> TracePat
  | Fetch      : location -> TracePat
  | Orambank   : orambank -> TracePat
  | Concat     : TracePat -> TracePat -> TracePat
  | TracePplus : TracePat -> TracePat -> TracePat
  | Epsilon    : TracePat.

Inductive TracePatEquiv: TracePat -> TracePat -> Prop:=
  | Epsilon_equiv: TracePatEquiv Epsilon Epsilon
  | O_equiv : forall n, TracePatEquiv (Orambank n) (Orambank n)
  | Read_equiv : forall x, TracePatEquiv (Read x) (Read x)
  | Fetch_equiv: forall p, TracePatEquiv (Fetch p) (Fetch p)
  | Assoc_equiv: forall t1 t2 t3, TracePatEquiv (Concat (Concat t1 t2) t3) (Concat t1 (Concat t2 t3))
  | Trans_equiv: forall t1 t2 t3, (TracePatEquiv t1 t2) -> (TracePatEquiv t2 t3) -> (TracePatEquiv t1 t3)
  | Epsilon_ident_equivl: forall T, (TracePatEquiv T T) -> TracePatEquiv T (Concat Epsilon T)
  | Epsilon_ident_equivr: forall T, (TracePatEquiv T T) -> TracePatEquiv T (Concat T Epsilon)
  | Concat_decomp_equiv: forall T11 T21 T12 T22,
  (TracePatEquiv T11 T12) -> (TracePatEquiv T21 T22) ->
  (TracePatEquiv (Concat T11 T21) (Concat T12 T22))
  .

Fixpoint TracePRemEpsilon t :=
  match t with
  | Concat a b =>
    match (TracePRemEpsilon a),(TracePRemEpsilon a) with
    | a, Epsilon => a
    | Epsilon, a => a
    | a,b => Concat a b
    end
  | a => a
  end.


Definition evttracePat l t:  TracePat :=
  match l with
  | low => t
  | o_high a => Orambank a
  end.


Inductive exprTyping: environment -> expression -> labeledType -> TracePat -> Prop :=
  | TVar : forall (gamma:environment) (x:variable) l,
      ((gamma x) = (Some (lnat l))) ->
      (exprTyping gamma (exvar x) (lnat l) (evttracePat l (Read x)))

  | TCon : forall (gamma:environment) n, exprTyping gamma (exnum n) (lnat low) Epsilon

  | TOp : forall (gamma:environment) e1 e2 l1 l2 T1 T2 op,
      (exprTyping gamma e1 (lnat l1) T1) ->
      (exprTyping gamma e2 (lnat l2) T2) ->
      (exprTyping gamma (exop e1 op e2) (lnat (mtojoin l1 l2)) (Concat T1 T2))

  | TArr : forall (gamma:environment) x e l l2 T,
      ((gamma x) =(Some (larr l))) ->
      (exprTyping gamma e (lnat l2) T) ->
      (lable l2 l) ->
      (exprTyping gamma (exarr x e) (lnat (mtojoin l l2)) (Concat T (evttracePat l (Readarr x)))).


Inductive select : TracePat -> TracePat -> TracePat -> Prop :=
  | equiv : forall t1 t2, (TracePatEquiv t1 t2) -> (select t1 t2 t1)
  | inequiv : forall t1 t2, (~(TracePatEquiv t1 t2)) -> (select t1 t2 (TracePplus t1 t2))
.
Inductive statementTyping: environment -> label -> labeledstatement -> TracePat -> Prop :=
  | TSkip : forall gamma p l, statementTyping gamma l (labline p skip) Epsilon
  | TAsn : forall gamma e l p T x l0 l1, (exprTyping gamma e (lnat l) T) ->
      (gamma x = Some (lnat l1)) -> (lable (mtojoin l0 l) l1) ->
      (statementTyping gamma l0 (labline p (assign x e)) (Concat T (evttracePat l1 (Write x))))
  | TAAsn : forall gamma e1 e2 l1 l2 T1 T2 l0 l x p,
      (exprTyping gamma e1 (lnat l1) T1) -> (exprTyping gamma e2 (lnat l2) T2) ->
      ((gamma x) = Some (larr l)) -> (lable (mtojoin l1 (mtojoin l2 l0)) l) ->
      (statementTyping gamma l0 (labline p (arrassign x e1 e2)) (Concat T1 (Concat T2 (evttracePat l (Writearr x)))))
  | TCond : forall gamma e l l0 T1 T2 T S1 S2 T3 p,
      (exprTyping gamma e (lnat l) T) ->
      (progTyping gamma (mtojoin l l0) S1 T1) ->
      (progTyping gamma (mtojoin l l0) S2 T2) ->
      (((mtojoin l l0) <> low) -> (TracePatEquiv T1 T2)) -> (select T1 T2 T3) ->
      (statementTyping gamma l0 (labline p (stif e S1 S2)) (Concat T T3))
  | TWhile : forall gamma e l l0 T1 T2 S p,
      (exprTyping gamma e (lnat l) T1) ->
      (progTyping gamma l0 S T2) ->
      (lable (mtojoin l l0) low) ->
      (statementTyping gamma l0 (labline p (stwhile e S )) (Loop p T1 T2))

with progTyping: environment -> label -> program -> TracePat -> Prop :=
(*** for this rule, they require that l0 is less/equal p, this is not defined for
use in locations, only for labels ***)

  | TLab : forall gamma l0 s T p,  (statementTyping gamma l0 (labline p s) T) -> (lablerhslocataion l0 p) ->
      (progTyping gamma l0 (oneLineProg( labline p s)) (Concat (Fetch p) T))
  | TSeq : forall gamma l0 S1 T1 S2 T2, ((progTyping gamma l0 S1 T1) ->
      (progTyping gamma l0 S2 T2) ->
      (progTyping gamma l0 (progcat S1 S2) (Concat T1 T2))).
