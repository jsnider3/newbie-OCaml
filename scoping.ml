(*This shows that ocaml uses lexical aka static scoping.*)
let x = 5;;

let foo () =
  print_string "x in foo = ";
  print_int x;
  print_string "\n";;

let bar () =
  (* Here we have bar redefining x and shadowing the global definition. *)
  let x = 2 in 
    print_string "x in bar = ";
    print_int x;
    print_string "\n";;

bar();
(* This x produces an unused variable warning. Because it only exists
   within foo (). The fact that this prints x in foo = 5, is also proof
   that we use lexical scoping and not runtime scoping. *)
let x = 3 in foo ();;
(* Deleting this semicolon causes the program to behave differently as
   shown next. *)
let x = 3;(* ;*)
print_string "x in top = ";
print_int x;
print_string "\n";;
(* Here it is again. The reason the second semi-colon makes a difference
   is that ; and ;; are copletely seperate things in OCaml in contrast to
   what you'd expect from the C-family. The single semicolon is an operator
   that of type a -> b -> b. It takes two exprs, evaluates the first one, 
   evaluates the second one, and returns the return value of the second one.
   In contrast the double semicolon, seperates toplevel-input from each other.
   So what's happening is that the let-binding used as a toplevel-phrase is 
   different from the let-binding used as an expr and they of course behave
   differently. Credit to
            http://caml.inria.fr/pub/docs/manual-ocaml-400/manual023.html *)
let x = 3;;
print_string "x in top = ";
print_int x;
print_string "\n";;
foo ();
