open Core.Std;;
open Printf;;

type 'a lazylist = Cons of 'a * (unit -> 'a lazylist);; 

let rec lseq n = Cons(n, fun () -> lseq (n+1))

let rec ltake (Cons (h, tf)) n =
  match n with
    0 -> []
    |_ -> h::(ltake (tf()) (n - 1));;

let rec ldrop (Cons (h, tf)) n =
  match n with
    0 -> Cons (h, tf)
    |_ -> ldrop (tf()) (n-1);;

let rec lmap (Cons (h, tf)) f = Cons (f h, fun () -> lmap (tf ()) f)

let rec lfilter (Cons (h, tf)) f =
  match f h with
    true -> Cons(h, fun () -> lfilter (tf ()) f)
    |false -> lfilter (tf ()) f;;

(*
  Page 14 Question 1: Type of powers_of_two is int lazylist.
*)

let is_power_of_two n = n land (n - 1) = 0;;

let powers_of_two = lfilter (lseq 1) is_power_of_two;;

(*
  Page 14 Question 2
*)

let rec lindex (Cons (h, tf)) n =
  match n with
  0 -> h
  |_ -> lindex (tf()) (n - 1);;

(*
  Page 14 Question 3
*)

let rec lrepeat_helper iter ls = 
  match (iter, ls) with
    ((x::xs),_) -> Cons (x, fun () -> lrepeat_helper xs ls)
    |([], []) -> invalid_arg "Empty list"
    |([],_) -> lrepeat_helper ls ls;;

let rec lrepeat ls = lrepeat_helper ls ls;;

(*
  Page 14 Question 4
*)

let rec lfib (x,y) = Cons (x, fun () -> lfib (y, x+y));;

(*
  Page 14 Question 5
*)

let rec every_other lst = (Cons ((lindex lst 0), fun () -> every_other (ldrop lst 2)));;

let rec unleave lst = (every_other lst, every_other (ldrop lst 1));; 

(*
  Page 14 Question 6
*)

let remove_last strn = String.sub strn ~pos:0 ~len:((String.length strn)-1);;

let next_char chr = match (Char.of_int(1 + Char.to_int chr)) with
  Some a -> a
  |_ -> 'a';;

let rec next_word strn = match strn with
  "" -> "A"
  |_ -> (match strn.[(String.length strn)-1] with
    'Z' -> (next_word (remove_last strn)) ^ "A"
    |a -> remove_last strn ^ Char.to_string (next_char a)
    )
;;

let rec lwords strn = Cons(strn, fun () -> (lwords (next_word strn)));;

let test_unleave () = let (a,b) = unleave (powers_of_two) in
  assert (ltake a 3 = [1; 4; 16]);
  assert (ltake b 2 = [2; 8;]);;

let test_lwords () = let strs = lwords "A" in
  assert (lindex strs 1 = "B"); 
  assert (lindex strs 26 = "AA");; 

let main () = 
  assert (ltake powers_of_two 5 = [1;2;4;8;16]);
  assert (lindex powers_of_two 2 = 4);
  assert (lindex powers_of_two 0 = 1);
  assert (lindex (lrepeat [1;2;3]) 0 = 1);
  assert (lindex (lrepeat [1;2;3]) 3 = 1);
  assert (ltake (lfib (0,1)) 5 = [0;1;1;2;3]);
  test_unleave();
  test_lwords();;

main ();;
