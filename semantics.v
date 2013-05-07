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

Definition mtoarrupd (m:array) (n1 n2:mtoint) : array :=
match m n1 with
|None => m
|Some a => (fun ind =>
if (beq_nat ind n1) then (Some n2) else (m ind) )
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

Definition memdefine m x v : memory :=
(
fun x1 => if (varideq x1 x) then Some v else m x1
).


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

Inductive stmtSem: memory -> labeledstatement -> trace -> memory -> Prop :=
|SSkip : forall M p, stmtSem M (labline p skip) epsilon M
|SAsn : forall p M e t n n1 l x, (exprSem M e t n) -> (M x = Some (vint n1 l)) -> 
(stmtSem M (labline p (assign x e)) (concat t (evttrace l (write x n))) (memdefine M x (vint n l)))
|SAAsn : forall M e1 t1 n1 e2 t2 n2 x m l m1 p,
(exprSem M e1 t1 n1) -> (exprSem M e2 t2 n2) -> (M x = Some (varr m l)) ->
(m1 = mtoarrupd m n1 n2) -> 
(stmtSem M (labline p (arrassign x e1 e2)) (concat t1 (concat t2 (evttrace l (writearr x n1 n2))))
(memdefine M x (varr m1 l)))
|SCondT : forall M e p t1 n S1 S2 t2 M1, (exprSem M e t1 n) -> (n <> O) -> 
(progSem M S1 t2 M1) ->
(stmtSem M (labline p (stif e S1 S2)) (concat t1 t2) M1)
|SCondF : forall M e p t1 n S1 S2 t2 M1, (exprSem M e t1 n) -> (n = O) -> 
(progSem M S2 t2 M1) ->
(stmtSem M (labline p (stif e S1 S2)) (concat t1 t2) M1)
|SWhileT : forall M e t n S p t1 M1,
(exprSem M e t n) -> (n<> O) ->
(progSem M (progcat S (oneLineProg (labline p (stwhile e S)))) t1 M1) -> 
(stmtSem M (labline p (stwhile e S)) (concat (fetch p) (concat t t1)) M1)
|SWhileF : forall M e t S p,
(exprSem M e t O) ->
(stmtSem M (labline p (stwhile e S)) (concat (fetch p) t) M)

with

progSem : memory -> program -> trace -> memory -> Prop :=
|PStmt : forall M p s t M1, (stmtSem M (labline p s) t M1) -> 
(progSem M (oneLineProg (labline p s)) (concat (fetch p) t) M1)
|PStmts: forall M S1 t1 M1 S2 t2 M2,
(progSem M S1 t1 M1) -> (progSem M1 S2 t2 M2) ->
(progSem M (progcat S1 S2) (concat t1 t2) M2).

Check (stmtSem (memdefine (fun x => None) (var (Id (S O))) (vint O low))

 (labline (addr O) (assign (var(Id(S O))) (S O)))

(concat epsilon (write (var (Id(S O))) (S O)))

(memdefine (memdefine (fun x => None) (var (Id (S O))) (O)) (var (Id(S O))) (vint (S O) low))).




