
Require Export Sflib.

(* Language Syntax *)
Inductive variable : Type := 
  | var : id -> variable.

Inductive orambank : Type :=
  | bank : nat -> orambank.

Inductive expression : Type :=
  | expr : variable -> expression
  | exop : expression -> expression -> expression
  | exarr: variable -> expression -> expression
  | exnum: nat -> expression.

Inductive location : Type :=
  | addr : nat -> location
  | oram : orambank -> location.

Inductive statement : Type :=
  | skip : statement
  | assign: variable -> expression -> statement
  | arrasign: variable -> expression -> expression -> statement
  | stif: expression -> program -> program -> statement
  | stwhile: expression -> program -> statement  
 with program : Type := 
  | line : location -> statement -> program
  | progcat : program -> program -> program.

Inductive mtonat : Type := natl.

Inductive label :  Type := 
  | low: label
  | o_high : orambank -> label.

Inductive mtoarray : Type := arrl.

Inductive labeledType : Type :=
  | larr : mtoarray -> label -> labeledType
  | lnat : mtonat -> label -> labeledType.

Inductive  