
Require Export Sflib.

Require Export FSets.

Require Export Peano.

Module core.

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
|labeledStmt : location -> statement -> program
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







Definition array:Type :=  nat -> option nat.



Definition mtoint : Type := nat.


Definition mtoarrget (m:array) (n:mtoint) : mtoint :=
match m n with
|None => O
|Some a => a
end.

Definition mtoarrupd m n1 n2 : array :=
match m n1 with
|None => m
|Some a => (fun ind =>
if (beq_nat ind n1) then n2 else (m ind) )
end.


Inductive labeledValue : Type :=
|vint : mtoint -> label -> labeledValue
|varr : array -> label -> labeledValue.



Definition memory := variable -> (option labeledValue).

