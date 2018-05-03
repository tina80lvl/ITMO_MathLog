float_of_int == float
int_of_float 
char_of_int
int_of_char
string_of_int

(* cortege *) ( , )
(1,4.5,"OK");;
(* list *) [ ; ]
[1;2;3];;

add ::
# 0::[1;2;3;4];;
- : int list = [0; 1; 2; 3; 4]
# 1::2::3::4::5::[];;
- : int list = [1; 2; 3; 4; 5]

combine @
[1;2;3] @ [4;5;6];;
- : int list = [1; 2; 3; 4; 5; 6]

(* array *) [| ; |]
# [|1;2;3|];;
- : int array = [|1; 2; 3|]
# [|1;2;3|].(0);;
- : int = 1

(* functions & global variables *) in (* connection between name ind value *)
# let a=2 in a*a;;
- : int = 4
let a = 5;;
Printf.printf "%i\n" a;;
let a = 7 in 
  let b = a * a in
    Printf.printf "%i %i\n" a b;;
Printf.printf "%i\n" a;;
//output
5
7 49
5


(* recursion *)
let rec range a b =
  if a > b then []
  else a :: range (a + 1) b
  ;; 

 let positive_sum a b = 
    let a = max a 0
    and b = max b 0 in
    a + b
