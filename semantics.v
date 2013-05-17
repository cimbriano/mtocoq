Require Export Sflib.
Require Export FSets.
Require Export Peano.
Require Export core.


Definition mtoarray : Type :=  mtonat -> option mtonat.

Definition mtoarrget (m:mtoarray) (n:mtonat) : mtonat :=
  match m n with
  | None => O
  | Some a => a
  end.


Definition mtoarrupd (m:mtoarray) (n1 n2:mtonat) : mtoarray :=
  match m n1 with
  | None => m
  | Some a => (
      fun ind =>
        if (beq_nat ind n1)
        then (Some n2)
        else (m ind) )
  end.


(*
  TODO: Replace two constructors with one that
  that takes a value * label, where value is
  one of mtoint or array.
*)

Inductive labeledValue : Type :=
  | vint : mtonat -> label -> labeledValue
  | varr : mtoarray -> label -> labeledValue.

Inductive trace : Type :=
  | read : variable -> mtonat -> trace
  | readarr : variable ->mtonat -> mtonat -> trace
  | write : variable -> mtonat -> trace
  | writearr : variable -> mtonat -> mtonat -> trace
  | fetch : location -> trace
  | orambank : orambank -> trace
  | concat : trace -> trace ->trace
  | epsilon : trace.


Definition evttrace l t : trace:=
  match l with
  | low      => t
  | o_high a => orambank a
  end.

Fixpoint tracelen (t:trace) : nat :=
  match t with
  | epsilon => 0
  | concat t1 t2 => plus (tracelen t1) (tracelen t2)
  | _ => 1
  end.

(*
  Used in proving Theorem 1
  for the induction on while
*)

Fixpoint tracelen_withepsilon (t:trace) : nat :=
  match t with
  | concat t1 t2 => plus (tracelen_withepsilon t1) (tracelen_withepsilon t2)
  | _ => 1
  end.

Fixpoint ithelement (t:trace) (i:nat) : trace :=
  match i with
  | O => epsilon
  | S O =>

    match t with
    | read _ _ => t
    | write _ _ => t
    | readarr _ _ _ => t
    | writearr _ _ _ => t
    | fetch _ => t
    | orambank _ => t
    | concat t1 t2 => (if( ble_nat 1 (tracelen t1) ) then
                      ithelement t1 i else
                      ithelement t2 i)
    |_ => epsilon
    end

  | S (S n) =>
    match t with
    | concat t1 t2 =>
      if (ble_nat i (tracelen t1))
      then (ithelement t1 i)
      else (ithelement t2 (minus i (tracelen t1)))
    | _ => epsilon
    end
  end.

Fixpoint numconcat t : nat :=
  match t with
  | concat a b => S (plus (numconcat a) (numconcat b))
  | _ => O
  end.

Fixpoint numblocks t : nat :=
match t with
| concat a b => numblocks a + numblocks b
| _ => 1
end.


Definition memory : Type := variable -> (option labeledValue).

Definition memdefine m x v : memory :=
  (
  fun x1 => if (varideq x1 x) then Some v else m x1
  ).


Inductive exprSem: memory -> expression -> trace -> mtonat -> Prop:=
  | EVar : forall M x t n l,
      (M x = Some (vint n l)) ->
      (t = evttrace l (read x n)) ->
      (exprSem M (exvar x) t n)

  | EConst : forall M n, (exprSem M (exnum n) epsilon n)

  | EOp : forall M e1 e2 t1 t2 n1 n2 n op,
      (exprSem M e1 t1 n1) ->
      (exprSem M e2 t2 n2) ->
      (n = op n1 n2) ->
      (exprSem M (exop e1 op e2) (concat t1 t2) n)

  | EArr : forall M e t n m l n1 t1 x,
      (exprSem M e t n) ->
      (M x = Some (varr m l)) ->
      (n1 = mtoarrget m n) ->
      (t1 = evttrace l (readarr x n n1)) ->
      (exprSem M (exarr x e) (concat t t1) n1).

Inductive stmtSem: memory -> labeledstatement -> trace -> memory -> Prop :=
  | SSkip : forall M p, stmtSem M (labline p skip) epsilon M

  | SAsn : forall p M e t n n1 l x,
      (exprSem M e t n) ->
      (M x = Some (vint n1 l)) ->
      (stmtSem M (labline p (assign x e))
                 (concat t (evttrace l (write x n)))
                 (memdefine M x (vint n l)))

  | SAAsn : forall M e1 t1 n1 e2 t2 n2 x m l m1 p,
      (exprSem M e1 t1 n1) ->
      (exprSem M e2 t2 n2) ->
      (M x = Some (varr m l)) ->
      (m1 = mtoarrupd m n1 n2) ->
      (stmtSem M (labline p (arrassign x e1 e2))
                 (concat t1 (concat t2 (evttrace l (writearr x n1 n2))))
                 (memdefine M x (varr m1 l)))

  | SCondT : forall M e p t1 n S1 S2 t2 M1,
      (exprSem M e t1 n) ->
      (n <> O) ->
      (progSem M S1 t2 M1) ->
      (stmtSem M (labline p (stif e S1 S2)) (concat t1 t2) M1)

  | SCondF : forall M e p t1 n S1 S2 t2 M1,
      (exprSem M e t1 n) ->
      (n = O) ->
      (progSem M S2 t2 M1) ->
      (stmtSem M (labline p (stif e S1 S2)) (concat t1 t2) M1)

  | SWhileT : forall M e t n S p t1 M1,
      (exprSem M e t n) ->
      (n <> O) ->
      (progSem M (progcat S (oneLineProg (labline p (stwhile e S)))) t1 M1) ->
      (stmtSem M (labline p (stwhile e S)) (concat (fetch p) (concat t t1)) M1)

  | SWhileF : forall M e t S p,
      (exprSem M e t O) ->
      (stmtSem M (labline p (stwhile e S)) (concat (fetch p) t) M)

with progSem : memory -> program -> trace -> memory -> Prop :=
  | PStmt : forall M p s t M1, (stmtSem M (labline p s) t M1) ->
      (progSem M (oneLineProg (labline p s)) (concat (fetch p) t) M1)

  | PStmts: forall M S1 t1 M1 S2 t2 M2,
      (progSem M S1 t1 M1) ->
      (progSem M1 S2 t2 M2) ->
      (progSem M (progcat S1 S2) (concat t1 t2) M2).



Inductive traceequiv: trace -> trace -> Prop:=
  | equal_equiv: forall t, traceequiv t t

  | refl_equiv: forall t1 t2,
      (traceequiv t1 t2) -> (traceequiv t2 t1)

  | assoc_equiv: forall t1 t2 t3,
      traceequiv (concat (concat t1 t2) t3) (concat t1 (concat t2 t3))

  | trans_equiv: forall t1 t2 t3,
      (traceequiv t1 t2) ->
      (traceequiv t2 t3) ->
      (traceequiv t1 t3)

  | epsilon_ident_equivl: forall T,
      (traceequiv T T) -> traceequiv T (concat epsilon T)

  | epsilon_ident_equivr: forall T,
      (traceequiv T T) -> traceequiv T (concat T epsilon)

  | concat_decomp_equiv: forall T11 T21 T12 T22,
      (traceequiv T11 T12) ->
      (traceequiv T21 T22) ->
      (traceequiv (concat T11 T21) (concat T12 T22)).

Fixpoint num_statements (S:program) : nat :=
  match S with
  | (oneLineProg (labline _ (stif _ S1 S2))) =>
      1 + (num_statements S1) + (num_statements S2)
  | (oneLineProg (labline _ (stwhile _ S1 ))) =>
      1 + (num_statements S1)
  | (oneLineProg _ ) => 1
  | (progcat S1 S2) => (num_statements S1) + (num_statements S2)
  end.


(***
Check (stmtSem (memdefine (fun x => None) (var (Id (S O))) (vint O low))

 (labline (addr O) (assign (var(Id(S O))) (S O)))

(concat epsilon (write (var (Id(S O))) (S O)))

(memdefine (memdefine (fun x => None) (var (Id (S O))) (O)) (var (Id(S O))) (vint (S O) low))).
***)



