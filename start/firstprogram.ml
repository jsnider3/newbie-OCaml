(* Stereotypically, the first program written in a language is "Hello World".
   Joke's on you. Let's try averaging two numbers together. *)

(* In Haskell, I would have written something like average : Float -> Float ->
   Float to tell the compiler that average takes two floats and returns one.
   That's not really necessary since type inference is powerful enough to 
   figure that out on our own. *)

let average a b = 
  (a +. b) /. 2.0;;

(* ...and the same thing for ints with the added feature of a let-binding *)
let averageInt a b = 
  let sum = a + b in
  sum / 2;;

(* When I ran this next line, my love of Python made me
   expect it to print out 2.5. But it didn't, lazy evaluation 
   means it's not going to turn "average 5.0 0.0"
   into 2.5 unless it's forced to. *)
average 5.0 0.0;; 

(* Nothing exciting here just casting numbers to strings and printing them. *)
print_endline(string_of_int 3);;
print_endline(string_of_float (average 12.0 0.));;
print_endline(string_of_int (averageInt 5 2));;
(* This next line isn't even syntactically valid, try to guess why. *)
(* print_float (average 5.0 -2.1);;*)

(* The reason it's invalid is that -2.1. That minus sign is being interpreted
   as the integer subtraction operator, it checks if average 5.0 is an int,
   sees that it's not and stops immediately. It can be fixed by putting parens
   around -2.1.*)
(* Credit to SreekanthGS on StackOverflow for helping me figure
   that out.
   http://stackoverflow.com/q/27977496/syntax-error-trying-to-average-variables *)
print_float (average 5.0 (-2.1));;
