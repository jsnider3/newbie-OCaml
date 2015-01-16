(* FYI, I assume that the 0th fibonacci is 0, followed by 1, 1, 2. *)

(* Here's the straightforward definition, which is big-O 2^n *)
let rec naiveFib n =
  match n with
    0 -> 0
   |1 -> 1
   |x -> naiveFib (x - 1) + naiveFib (x - 2);;

print_endline(string_of_int (naiveFib 1));;
print_endline(string_of_int (naiveFib 2));;
print_endline(string_of_int (naiveFib 5));;
print_endline(string_of_int (naiveFib 10));;
(* As expected from an O(2^n) algorithm this next line takes longer
   than I would care to wait. *)
(* print_endline(string_of_int (naiveFib 100));;*)

(* Fortunately, there are many ways to do a faster fibonacci *)

(* This is basically a for loop, reimagined in functional style. It starts
   at the 0th and 1st fibonacci numbers and counts up to whatever n is. It is
   linear in complexity with respect to n. *)
let rec forFibHelper a b n =
  match n with
    0 -> a
   |_ -> forFibHelper b (b + a) (n - 1);;

let forFib n = 
  forFibHelper 0 1 n;;   

print_endline(string_of_int (forFib 1));;
print_endline(string_of_int (forFib 2));;
print_endline(string_of_int (forFib 5));;
print_endline(string_of_int (forFib 10));;
print_endline(string_of_int (forFib 100));;
(* forFib 100 finishes rapidly, but if you check it's wrong. This is because
   the 100th fibonacci number is simply to big for 64 bits. On my machine, the
   last correct fibonacci number if the 90th at 2,880,067,194,370,816,120. *)

(* Fun fact, OCaml actually overflows at 2^62 - 1, since it uses one of the 64
   bits for fancy shmancy tagged pointer tricks. Credit to
     http://stackoverflow.com/q/3773985/why-is-an-int-in-ocaml-only-31-bits *)

(* Let's make a Fibonacci that is smart enough to alert the user when it won't
   be able to give correct results. This is just using the direct formula for
   the Fibonacci numbers, this is either linear or logarithmic complexity.
   It depends on how fancy your exponent function is.*)
(* Invalid arg is a string -> 'a function. Just like error in Haskell, but OCaml
   has a couple different functions to raise different kinds of errors.*)

let smartFib a =
  let a = float_of_int a in
    if a < 0. || a > 90. then
      invalid_arg "INVALID INPUT"
    else
      let phi = (1. +. (sqrt 5.)) /. 2. in
        let tmp = ((phi ** a) +. ((1. /. phi) ** a)) /. sqrt (5.) in
          int_of_float tmp
  ;;

print_endline(string_of_int (smartFib 1));;
print_endline(string_of_int (smartFib 2));;
print_endline(string_of_int (smartFib 5));;
print_endline(string_of_int (smartFib 10));;

(* Here's my solution to the Even Fibonacci numbers problem on Project Euler.
   If you copy my answer, you suck. But honestly it's not that hard, we just
   list the fibonacci numbers less than 4 million, check if they're even, and
   keep a running total of those that are.*)

let rec eulerAccumulator sum cnt = 
  let fib = smartFib cnt in
    if fib < 4000000 then
      if (fib mod 2) = 0 then
        eulerAccumulator (sum + fib) (cnt + 1)
      else
        eulerAccumulator sum (cnt + 1)
    else
      sum
  ;;

let projectEuler = eulerAccumulator 0 1;;

print_endline(string_of_int(projectEuler));;
   
