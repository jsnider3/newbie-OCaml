open Core.Std;;
open Printf;;

(*
  NOTE: Labels can be omitted if we do them in order.
*)
let rec fill a ~start:s ~length v = match length with
  0 -> ()
  |_ -> a.(s) <- v; fill a (s+1) (length-1) v;;

let filled () =
  let a = Array.create 100 "x" in
    fill a 20 40 "y";
    a;;

let rec drop ls n = match n with
  0 -> ls
  |_ -> drop (List.tl_exn ls) (n - 1);;

let rec take ls n = match n with
  0 -> []
  |_ -> List.hd_exn ls :: take (List.tl_exn ls) (n - 1);;

(*
  Under the hood, optional arguments are 
    implemented through Option values.
*)
let rec split ?(chunksize = 1) l =
  try
    take l chunksize ::
      split ~chunksize (drop l chunksize)
  with
    _ -> match l with
      [] -> []
      |_ -> [l];;

let incr ?(delta = 1) x = x + delta;;
 
(*
  Page 56 Question 2: The order start stop is more intuitive
    and will crash nastily if they're confused.
*)
let fill_range a start stop v = fill a start (stop-start) v;;

(*
  Page 56 Question 4:
*)
let rec map ?(a = []) f l =
  match l with
    [] -> List.rev a
    |h::t -> map ~a:(f h :: a) f t;;

let test_incr () = assert(incr ~delta:5 4 = 9);
  assert(incr 2 = 3);;

let test_map () = assert(map (incr ~delta:5) [1;2;3;4] = [6;7;8;9]);;

let main () = test_incr ();
  test_map ();;

main ();;
