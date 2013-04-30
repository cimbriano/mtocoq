
Require Export Sflib.

Require Export FSets.

Require Export Peano.

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






