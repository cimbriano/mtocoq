
Require Export Sflib.

Require Export FSets.

Require Export Peano.

Inductive variable : Type := 
|var : id -> variable.

Definition varideq x1 x2 : bool :=
match x1, x2 with
|var(Id(a)),var(Id(b)) => if (beq_nat a b) then true else false
end.

Inductive orambank : Type :=
|bank : nat -> orambank.

Definition mtoint : Type := nat.

Definition binop := mtoint -> mtoint -> mtoint.


Inductive expression : Type :=
|exvar : variable -> expression
|exop : expression ->binop -> expression -> expression
|exarr: variable -> expression -> expression
|exnum: mtoint -> expression.

Inductive location : Type :=
|addr : nat -> location
|oram : orambank -> location.

Inductive statement : Type :=
|skip : statement
|assign: variable -> expression -> statement
|arrassign: variable -> expression -> expression -> statement
|stif: expression -> program -> program -> statement
|stwhile: expression -> program -> statement

with labeledstatement : Type :=
|labline : location -> statement -> labeledstatement

with program : Type := 
|oneLineProg : labeledstatement -> program
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

(**** we cover that case here****)
Inductive lablerhslocataion : label -> location -> Prop :=
|nothighloc : forall l n, lablerhslocataion l (oram n). 






