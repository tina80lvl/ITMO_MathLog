open Tree;;
open Printf;;
open Checker;;

let (inp, out) = (open_in "input.txt", open_out "output.txt");;

let (>>) x f = f x;;

(* parse_ass = parse assumptions from header to tree list *)
let parse_ass header = header >> Lexing.from_string >> Parser.header Lexer.read;;

(* get_ass_from_h = get assumption from header *)
let get_ass_from_h header = 
	let ass_hash_table = Tree_table.create 1001 in
	let ass_tree_list  = parse_ass (header) in
	List.iteri (fun i tree -> Tree_table.add ass_hash_table tree (i + 1)) ass_tree_list;
	ass_hash_table;;

let is_ass tree tree_table = 
	if (Tree_table.mem tree_table tree) then 
		(Some (Tree_table.find tree_table tree))
	else (None)

let parse_exp_to_tree exp = 
	exp >> Lexing.from_string >> Parser.body Lexer.read;;

let ass_table = get_ass_from_h (input_line inp);;

let ind = ref 0;;
try
	while true do begin
		let line = input_line inp in
			if (line <> "") then begin
				ind := !ind + 1;
				let exp_tree = parse_exp_to_tree (line) in
				let checked_exp = check_exp_tree exp_tree !ind ass_table in
					fprintf out "(%d) %s (%s)\n" !ind (string_of_tree (exp_tree)) (string_of_checked_exp (checked_exp))
			end
		end
	done
with
	| End_of_file -> 
		close_out out;
		close_in inp
;;