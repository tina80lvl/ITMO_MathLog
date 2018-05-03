open Tree;;
open Printf;;
open Checker;;

let (>>) x f = f x;;

let (inp, out) = (open_in "input.txt", open_out "output.txt");;

let (ass_table, alpha, exp, ass_list) = get_ass_from_h (input_line inp);;
let ind_to_exp = Hashtbl.create 1001;;

let ind = ref 0;;
let alpha_string = string_of_tree alpha;;

fprintf out "%s|-(%s->%s)\n"
	(string_of_tree_list ass_list)
	alpha_string
	(string_of_tree exp)
;;

try
	while true do begin
		let line = input_line inp in
			if (line <> "") then begin
				ind := !ind + 1;
				let exp_tree = parse_exp_to_tree (line) in
				Hashtbl.add ind_to_exp !ind (string_of_tree exp_tree);

				

				let delta_k = string_of_tree exp_tree in
				let checked_exp = check_exp_tree exp_tree !ind ass_table in
				if (exp_tree = alpha) then begin
					fprintf out "%s->(%s->%s)\n"
						alpha_string
						alpha_string
						alpha_string;
					fprintf out "(%s->(%s->%s))->((%s->((%s->%s)->%s))->(%s->%s))\n"
						alpha_string
						alpha_string
						alpha_string
						alpha_string
						alpha_string
						alpha_string
						alpha_string
						alpha_string
						alpha_string;
					fprintf out "%s->((%s->%s)->%s)\n"
						alpha_string
						alpha_string
						alpha_string
						alpha_string;
					fprintf out "(%s->((%s->%s)->%s))->(%s->%s)\n"
						alpha_string
						alpha_string
						alpha_string
						alpha_string
						alpha_string
						alpha_string;
					fprintf out "%s->%s\n"
						alpha_string
						alpha_string;
				end
				else
					match checked_exp with
					| ModusPonens (i, j) ->
						let delta_j = Hashtbl.find ind_to_exp j in 
						fprintf out "(%s->%s)->((%s->(%s->%s))->(%s->%s))\n"
							alpha_string
							delta_j
							alpha_string
							delta_j
							delta_k
							alpha_string
							delta_k;
						fprintf out "(%s->(%s->%s))->(%s->%s)\n"
							alpha_string
							delta_j
							delta_k
							alpha_string
							delta_k;
						fprintf out "%s->%s\n"
							alpha_string
							delta_k;
					| Axiom _
					| Assumption _ -> 
						fprintf out "%s->%s->%s\n"
							delta_k
							alpha_string
							delta_k;
						fprintf out "%s\n"
							delta_k;
						fprintf out "%s->%s\n"
							alpha_string
							delta_k
					| _ -> ()
			end
		end
	done
with
	| End_of_file -> 
		close_out out;
		close_in inp
;;




