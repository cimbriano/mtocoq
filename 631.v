
Require Export Sflib.

Require Export FSets.

Inductive variable : Type := 
|var : id -> variable.

Inductive orambank : Type :=
|bank : nat -> orambank.


Inductive expression : Type :=
|expr : variable -> expression
|exop : expression -> expression -> expression
|exarr: variable -> expression -> expression
|exnum: nat -> expression.

Inductive location : Type :=
|addr : nat -> location
|oram : orambank -> location.

Inductive statement : Type :=
|skip : statement
|assign: variable -> expression -> statement
|arrasign: variable -> expression -> expression -> statement
|stif: expression -> program -> program -> statement
|stwhile: expression -> program -> statement

with program : Type := 
|line : location -> statement -> program
|progcat : program -> program -> program.

Inductive mtonat : Type :=
| natl.

Inductive label :  Type :=
|low: label
|o_high : orambank -> label.

Inductive mtoarray : Type :=
|arrl.

Inductive labeledType : Type :=
|larr : mtoarray -> label -> labeledType
|lnat : mtonat -> label -> labeledType.

Definition mtojoin l1 l2 : label := 
match l1 with
|low => l2
|o_high a => l1
end.

Definition lable l1 l2 : bool :=
match l1 with 
|low => true
|o_high _ =>
    (match l2 with
    |low => false
    |o_high _ => true 
    end)
end.


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

Variable A : Type.

(* We will want to change this definition later *)
(* A list of nat doesn't have a length *)
(*Definition array := list nat.*)

Inductive array : nat -> Type :=
  | arrnil : array 0
  | arrcons : forall (n:nat), array n -> array (S n).

Inductive value : Type :=
 | ar : forall (n:nat), array n -> value
 | nu : nat -> value.

Definition memory := variable -> (option (value * label)).

Inductive memoryLowEquiv : memory -> memory -> Prop :=
  | def1: forall (x:variable) (v:value) (m1 m2:memory),
    (((m1 x) = (Some (v , low))) <-> ((m2 x) = (Some (v , low)))) ->
    memoryLowEquiv m1 m2.

(*  *)
Fixpoint get (len:nat) (m:array len) (n:nat) : nat :=
  match m with
  | arrnil => 0
  | arrcons ele tail => if (ble_nat n (len - 1)) then (1) else 0
  end.
