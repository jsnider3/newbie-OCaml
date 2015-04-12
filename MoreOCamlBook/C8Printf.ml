open Core.Std;;
open Printf;;

type point = {x:float; y:float; label:string};;

let string_of_point p = sprintf "%s = (%f, %f)" p.label p.x p.y

let test_sop () = let p = {x = 0.0; y=0.0; label = "Origin"} in
  assert(string_of_point p = "Origin = (0.000000, 0.000000)");;

let data = [(1, 6, 5);
            (2, 18, 4);
            (3, 31, 12);
            (4, 16, 2)];;

let print_header () =
  printf "A     | B     | C    \n";
  printf "------|-------|-------\n";;

let print_line a b c =
  printf "%6i| %6i| %6i \n" a b c;;

let print_nums nums =
  print_header ();
  List.iter nums (fun (a,b,c) -> print_line a b c);;

(*
  Page 62 Question 1
*)
let string_of_pair (a, b) = sprintf "(%d, %d)" a b;;
let string_of_pair_list ls = 
  String.concat ~sep:" --> " (List.map ls string_of_pair);;

let test_pairlist () = let pairs = [(1,2);(3,4)] in
  assert(string_of_pair_list pairs = "(1, 2) --> (3, 4)");;

(*
  Page 62 Question 2
*)
let hex_of_string s = List.map (String.to_list s) Char.to_int;;

let hex_string_of_string s = 
  String.concat (List.map (hex_of_string s) (sprintf "%x"));;

let test_hex () = printf "%s\n" (hex_string_of_string "Hello");
  assert(hex_string_of_string "Hello" = "48656c6c6f");;

(*
  Page 63 Question 3: It causes a type error
    because it can't safely convert that string to a format string.
    printf "%s" (mkstring()) would work.
*)

(*
  Page 63 Question 4: 
*)

let string_of_table ls width =
  let fmt = Scanf.format_from_string (sprintf "(%%%dd)\n" width) "%d" in
    List.iter ls (printf fmt);;

let test_table () = string_of_table [1;2;3;4;5] 5;;

(*

*)
let main () = test_sop();
  test_pairlist ();
  test_hex ();
  test_table ();
  print_nums data;;

main ();;
