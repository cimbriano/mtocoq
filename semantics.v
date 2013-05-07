Require Export Sflib.

Require Export FSets.

Require Export Peano.

Require Export core.



Definition array:Type :=  nat -> option nat.





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

Inductive trace : Type :=
|read : variable -> mtoint -> trace
|readarr : variable ->mtoint -> mtoint -> trace
|write : variable -> mtoint -> trace
|writearr : variable -> mtoint -> mtoint -> trace
|fetch : location -> trace
|orambank : orambank -> trace
|concat : trace -> trace ->trace
|epsilon : trace.


Definition evttrace l t : trace:=
match l with
|low => t
|o_high a => orambank a
end.


Inductive exprSem: memory -> expression ->trace -> mtoint -> Prop:=
|EVar : forall M x t n l, (M x = Some (vint n l)) -> (t = evttrace l (read x n)) -> 
(exprSem M (exvar x) t n)
|EConst : forall M n, (exprSem M (exnum n) epsilon n)
|EOp : forall M e1 e2 t1 t2 n1 n2 n op, (exprSem M e1 t1 n1) -> (exprSem M e2 t2 n2) ->
(n = op n1 n2) -> (exprSem M (exop e1 op e2) (concat t1 t2) n)
|EArr : forall M e t n m l n1 t1 x, (exprSem M e t n) -> (M x = Some (varr m l)) ->
 (n1 = mtoarrget m n) -> (t1 = evttrace l (readarr x n n1)) ->
(exprSem M (exarr x e) (concat t t1) n1)
.

Inductive stmtSem: memory -> statement -> trace -> memory -> Prop :=
|SSkip : forall M, stmtSem M skip epsilon M
|SAsn : forall M e t n n1 l, (exprSem M e t n) -> (M x = Some (vint n1 l)) -> 


