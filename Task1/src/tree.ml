open Buffer;;

type operation = Conj | Disj | Impl;;

type tree_t = 
	| Binop of operation * tree_t * tree_t
    | Neg of tree_t
    | Var of string
;;
