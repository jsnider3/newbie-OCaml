(* When I was messing with the print functions. I thought it might be useful
   to have a short function that would print a new line instead of filling my
   code with a bunch of 'print_string "\n"'s *)

(* My first attempt. Since a function that takes two arguments can be 
   defined as let foo a b = ... and a function that takes one argument
   can be defined as let foo a = ..., I thought you may be able to define
   a function with zero args by let foo = ...*)

let newline = 
  print_string "\n";;

print_int 1;;
newline;;
print_int 2;;
newline;;

(* The above fails. Instead of printing 1 and 2 on seperate lines it prints
   an empty line followed by a 12. Why is this? It's because that newline 
   "function" we defined is actually a variable. When we create it, it evaluates
   print_string "\n" which has the side-effect of printing a newline, then 
   returns unit. So basically newline instead of being a function as I wanted
   is just a variable. A working solution follows *)

let endline () =
  print_string "\n";;

print_endline "\nAttempt 2:";;
print_int 1;;
endline ();;
print_int 2;;
endline ();;
