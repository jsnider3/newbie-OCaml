(* A classic *)

(* Like Haskell, we apply functions to arguments by putting a space between
   them. We use the print_string function instead of a generic print function
   because ocaml uses a strict form of typing.*)
print_string "Hello World!\n";;

(*Global variables can be done with let *)
let helloStr = "Hello ";;
let worldStr = "World!\n";;

print_string(helloStr);;
print_string(worldStr);;
