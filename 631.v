
Require Export Sflib.

Require Export FSets.

Inductive variable : Type := 
|var : id -> variable.

Inductive orambank : Type :=
|bank : nat -> orambank.


Inductive expression : Type :=
|exvar : variable -> expression
|exop : expression -> expression -> expression
|exarr: variable -> expression -> expression
|exnum: nat -> expression.

Inductive location : Type :=
|addr : nat -> location
|oram : orambank -> location.

Inductive statement : Type :=
|skip : statement
|assign: variable -> expression -> statement
|arrassign: variable -> expression -> expression -> statement
|stif: expression -> program -> program -> statement
|stwhile: expression -> program -> statement

with program : Type := 
|line : location -> statement -> program
|progcat : program -> program -> program.


Inductive label :  Type :=
|low: label
|o_high : orambank -> label.


Inductive labeledType : Type :=
|larr :  label -> labeledType
|lnat :  label -> labeledType.

Definition mtojoin l1 l2 : label := 
match l1 with
|low => l2
|o_high a => l1
end.


(**** NOTICE, excludes requirement that second not be a program location ****)
Inductive lable : label -> label -> Prop :=
|fst_low : forall l, lable low l
|snd_high: forall l n, lable l (o_high n).


Definition environment := variable -> (option labeledType).

Inductive TracePat : Type :=
|Read : variable -> TracePat
|Write: variable -> TracePat
|Readarr:variable ->TracePat
|Writearr:variable ->TracePat
|Loop: location -> TracePat -> TracePat-> TracePat
|Fetch: location -> TracePat
|Orambank : orambank -> TracePat
|concat: TracePat -> TracePat -> TracePat
|plus: TracePat -> TracePat -> TracePat
|epsilon: TracePat.

Inductive tracePequiv: TracePat -> TracePat -> Prop:=
|epsilon_equiv: tracePequiv epsilon epsilon
|O_equiv : forall n, tracePequiv (Orambank n) (Orambank n)
|read_equiv : forall x, tracePequiv (Read x) (Read x)
|fetch_equiv: forall p, tracePequiv (Fetch p) (Fetch p)
|assoc_equiv: forall t1 t2 t3, tracePequiv (concat (concat t1 t2) t3) (concat t1 (concat t2 t3))
|trans_equiv: forall t1 t2 t3, (tracePequiv t1 t2) -> (tracePequiv t2 t3) -> (tracePequiv t1 t3)
|epsilon_ident_equivl: forall T, (tracePequiv T T) -> tracePequiv T (concat epsilon T)
|epsilon_ident_equivr: forall T, (tracePequiv T T) -> tracePequiv T (concat T epsilon)
|concat_decomp_equiv: forall T11 T21 T12 T22, 
(tracePequiv T11 T12) -> (tracePequiv T21 T22) -> 
(tracePequiv (concat T11 T21) (concat T12 T22))
.

(** based on approach to recursion in coq described in
 http://www.di.ens.fr/~zappa/teaching/coq/ecole10/summer/lectures/lec10.pdf **)
Fixpoint TracePNormalFormHelp n T :  TracePat :=
match n,T with 
|(S n), (concat a epsilon) => TracePNormalForm n a
|(S n), concat epsilon a => TracePNormalForm n a
|(S n), concat a b => match TracePNormalForm  a with
|concat c d => concat c (TracePNormalForm (concat d b))
|c => c
end
| a => a
end.


Fixpoint boolTracePequiv : TracePat -> TracePat -> bool :=


Definition evt l t:  TracePat :=
match l with
|low => t
|o_high a => Orambank a
end.

Inductive exprTyping: environment -> expression ->labeledType -> TracePat ->Prop :=
|TVar : forall (gamma:environment) (x:variable) l, 
((gamma x) =(Some (lnat l)))  -> (exprTyping gamma (exvar x) (lnat l) (evt l (Read x)))
|TCon : forall (gamma:environment) n, exprTyping gamma (exnum n) (lnat low) epsilon
|TOp : forall (gamma:environment) e1 e2 l1 l2 T1 T2, 
(exprTyping gamma e1 (lnat l1) T1) -> (exprTyping gamma e2 (lnat l2) T2) ->
(exprTyping gamma (exop e1 e2) (lnat (mtojoin l1 l2)) (concat T1 T2))
|TArr : forall (gamma:environment) x e l l2 T, ((gamma x) =(Some (larr l))) -> 
(exprTyping gamma e (lnat l2) T) -> (lable l2 l) ->
(exprTyping gamma (exarr x e) (lnat (mtojoin l l2)) (concat T (evt l (Readarr x)))).

Definition select t1 t2:TracePat :=


Inductive statementTyping: environment -> label -> statement -> TracePat -> Prop :=
|TSkip : forall gamma l, statementTyping gamma l skip epsilon
|TAsn : forall gamma e l T x l0 l1, (exprTyping gamma e (lnat l) T) -> 
(gamma x = Some (lnat l1)) -> (lable (mtojoin l0 l) l1) ->
(statementTyping gamma l0 (assign x e) (concat T (evt l1 (Write x))))
|TAAsn : forall gamma e1 e2 l1 l2 T1 T2 l0 l x,
(exprTyping gamma e1 (lnat l1) T1) -> (exprTyping gamma e2 (lnat l2) T2) ->
((gamma x) = Some (larr l)) -> (lable (mtojoin l1 (mtojoin l2 l0)) l) ->
(statementTyping gamma l0 (arrassign x e1 e2) (concat T1 (concat T2 (evt l (Writearr x)))))
|TCond : forall gamma e l l0 T1 T2 T S1 S2,
(exprTyping gamma e (lnat l) T) ->
(statementTyping gamma (mtojoin l l0) S1 T1) ->
(statementTyping gamma (mtojoin l l0) S2 T2) ->
(((mtojoin l l0) <> low) -> (TracePequiv T1 T2)) ->
(statementTyping gamma l0 (stif e S1 S2) (concat T (select(T1,T2))))
|TWhile : forall gamma e l l0 T1 T2 S p,
(exprTyping gamma e (lnat l) T1) ->
(statementTyping gamma l0 S T2) ->
(lable (mtojoin l l0) low) ->
(statementTyping gamma l0 (line p (exwhile e S )) (Loop p T1 T2)).


Definition memory := variable -> (option ).

