open Tree;;
open Buffer;;
open Printf;;
open Hashtbl;;

let (>>) x f = f x;;
let hmap = Hashtbl.create 1000;;
let found_vars = Hashtbl.create 1000;;

let match_exp' p expr1 expr2 = match (expr1,expr2) with
  | (Impl(l1,r1), Impl(l2,r2)) -> match p with
    | (_, false) -> p
    | (_, true)  -> match_exp'r (match_exp'r p l1 l2) r1 r2
  | (Conj(l1,r1), Conj(l2,r2)) -> match p with
    | (_, false) -> p
    | (_, true)  -> match_exp'r (match_exp'r p l1 l2) r1 r2
  | (Disj(l1,r1), Disj(l2,r2)) -> match p with
    | (_, false) -> p
    | (_, true)  -> match_exp'r (match_exp'r p l1 l2) r1 r2
  | (Neg(v1), Neg(v2)) -> match p with
    | (_, false) -> p
    | (_, true)  -> match_exp'r p v1 v2
  | (Var(v1), v2) -> match Map.find_opt v1 (fst p) with
    | None -> (Map.add v1 v2 (fst p), (snd p))
    | Some t -> ((fst p), (snd p && t == v2))
  | _ -> match p with | (a,b) -> (a, false)
  ;;

let match_expr expr1 expr2 = snd (match_expr' (Map.empty, true) expr1 expr2);;

let substitute lst tmpl =
  let f m Var(v) =
  let e = Map.find_opt v m in
    match e with
    | None -> Var(v)
    | Some t -> t
    (*TODO*)
  in f mp tmpl;; (* was map from list [(a,b)] changed on map*)

let axiom_list = List.map parse [ "A -> B -> A"
                                , "(A -> B) -> (A -> B -> C) -> (A -> C)"
                                , "A -> B -> A & B"
                                , "A & B -> A"
                                , "A & B -> B"
                                , "A -> A | B"
                                , "B -> A | B"
                                , "(A -> C) -> (B -> C) -> (A | B -> C)"
                                , "(A -> B) -> (A -> !B) -> !A"
                                , "!!A -> A"
                                ];;

type annotation =
  | NotProoved
  | ByAxiom of int
  | ByAssumption of int
	| ByModusPones of int * int
  ;;

let gen_annotation_from_axioms ax st =
  let gen c lst st = match lst with
    | [] -> NotProoved
    | a::ax -> if match a st then ByAxiom c else gen (c+1) ax st
  in gen 0 ax st
  ;;

let gen_annotation_from_assuptions ax st =
  let gen c lst st = match lst with
    | [] -> NotProoved
    | a::ax -> if a == st then ByAssumption c else gen (c+1) ax st
  in gen 0 ax st
  ;;

let gen_annotation_by_MP m s st =
  let ls = Hashtbl.find m st in
    let f x y = match Map.find_opt (fst y) s with
      | None -> x
      | Some t -> ByModusPonens t (snd y)
    in fold_left f NotProoved ls (* TODO not sure *)
    ;;

let ge_annotation mm m ax as st =
  let f a b c = match a with
    | NotProoved -> match b with
      | NotProoved -> c
      | b' -> b'
    | a' -> a'
  in  f (gen_annotation_from_axioms ax st) (gen_annotation_from_assuptions as st) (gen_annotation_by_MP mm m st)
  ;;

let verify ax ass term =
  let ver c mm m ax ass lst = match lst with
    | [] -> []
    | t::term ->
      let an = gen_annotation mm m ax ass t
      in match an with
        | NotProoved -> NotProoved :: (ver (c+1) mm m ax ass term)
        | _ -> match t with
          | Impl(a,b) -> an :: (ver (c+1) (Hashtbl.add mm b (Pair a c)) (Map.add t c m) ax ass term)
          | _ -> an :: (ver (c+1) mm (Map.add t c m) ax ass term)
  in ver 0 (Hashtbl.create 1000) Map.empty ax ass term
  ;;

let string_of_annotation ann =;;(* TODO *)

let to_string =
  let t_s x lst = match lst with
    | [] -> ""
    | (a,b)::xs -> "(" + string_of_int x + ") " + a + " " + string_of_annotation b + "\n" + (t_s (x+1) xs)
  in t_s 0
  ;;

(* let next_number = Stream.from (fun i -> Some (string_of_int i));;
let expr_number expr = string_of_int Map.at expr;; *)

let string_of_tree tree =
  let s_op op = match op with Conj -> "&" | Disj -> "|" | Impl -> "->" in
  let buf = create 1000 in
  let rec s_t t = match t with
    | Var v -> add_string buf v
    | Neg t -> add_string buf "(!"; s_t t; add_char buf ')'
    | Binop (op,l,r) -> bprintf buf "(%s," (s_op op); s_t l; add_char buf ','; s_t r; add_char buf ')'
  in s_t tree;
  contents buf;;

let (ic,oc) = (open_in "input.txt", open_out "output.txt");;

(* TODO: translate:
main = readFile "task1.in" >>= (return . toString . f) >>= writeFile "task1.out"
	where
		f s =
			let lst = lines s
				in zip lst (verify A.axiomList [] (map parse lst)) *)
ic >> input_line >> Lexing.from_string >> Parser.main Lexer.main >> string_of_tree >> fprintf oc "%s\n";;

close_out oc;;
close_in ic;;
