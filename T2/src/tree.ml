type tree =
	| Conj of tree * tree
	| Disj of tree * tree
	| Impl of tree * tree
	| Neg of tree
	| Var of string;;
