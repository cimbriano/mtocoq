

(* The curly less then equal operator defined in tech report *)

Inductive curlyless : trace -> trace -> Prop :=
	| fewerblocks :
		forall t1 t2,
		(numblocks t1 <= numblocks t2) ->
		(curlyless t1 t2)

	| othercurlyless1 :
		forall t1' t1'' t2' t2'',
		(numblocks t1' + numblocks t1'' =
				numblocks t2' + numblocks t2'') ->
		(numblocks t1' >numblocks t2') ->
		(curlyless (concat t1' t1'') (concat t2' t2''))

	| othercurlyless2 :
		forall t1' t1'' t2' t2'',
		(numblocks t1' + numblocks t1'' =
				numblocks t2' + numblocks t2'') ->
		(numblocks t1'  = numblocks t2') ->
		(curlyless t1' t2') ->
		(curlyless (concat t1' t1'') (concat t2' t2''))

	| othercurlyless3 :
		forall t1' t1'' t2' t2'',
		(numblocks t1' + numblocks t1'' =
				numblocks t2' + numblocks t2'') ->
		(t1' = t2') ->
		(curlyless t1'' t2'') ->
		(curlyless (concat t1' t1'') (concat t2' t2'')).
