open Buffer;;

type operation = Conj | Disj | Impl;;

type tree_t = 
	| Binop of operation * tree_t * tree_t
    | Neg of tree_t
    | Var of string
;;

let string_of_operation operation = match operation with
	| Conj -> "&"
	| Disj -> "|"
	| Impl -> "->"
;;

let string_of_tree tree =
	let string_buffer = Buffer.create 1000 in
		let rec add_verb_to_buffer v = 
		match v with
			| Var v ->
				add_string string_buffer v
			| Neg t ->
				add_string string_buffer "!"; 
				add_verb_to_buffer t;
			| Binop (operation, left, right) ->
				add_string string_buffer "(";
				add_verb_to_buffer left;
				add_string string_buffer (string_of_operation operation);
				add_verb_to_buffer right;
				add_string string_buffer ")"
		in add_verb_to_buffer tree;
		contents string_buffer;;

let rec string_of_tree_list = 
	function
	| [] -> ""
	| tree :: tree_list -> string_of_tree (tree) ^ " " ^ string_of_tree_list (tree_list) 
;;

module Tree_table = Hashtbl.Make(struct
	type t = tree_t
	let equal = (=)
	let hash = Hashtbl.hash
end)

let string_of_tree_table table = 
	Tree_table.iter (fun tree ind -> print_endline ((string_of_tree tree) ^ " " ^ (string_of_int ind))) table;;









	