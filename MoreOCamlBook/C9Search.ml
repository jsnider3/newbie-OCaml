open Core.Std;;
open Printf;;

let rec take ls n = match n with
  0 -> []
  |_ -> List.hd_exn ls :: take (List.tl_exn ls) (n - 1);;

let rec list_eq l len p =
  len = 0
  ||
  (List.hd_exn l = List.hd_exn p
    &&
   list_eq (List.tl_exn l) (len - 1) (List.tl_exn p));;

let rec search_inner p len_p l len_l =
  len_p <= len_l
  &&
  (list_eq l len_p p ||
   search_inner p len_p (List.tl_exn l) (len_l - 1));;

let rec search_list p l =
  search_inner p (List.length p) l (List.length l);;

(*
  This is basically an extra-fancy-pants for loop.
*)
(*let rec at p pp s sp l =
  l = 0 || (p.[pp] = s.[sp] && at p (pp + 1) s (sp + 1) (l - 1));;*)

let rec swallow_all ?(acc = 0) ch p sp =
  if sp < String.length p && p.[sp] = ch
    then swallow_all ~acc:(acc + 1) ch p (sp + 1)
    else acc;; 

(*
  Do fancy-shmancy regex tricks.
  Returns (int, int) Option:
    None means failure.
    Some (x, y) means consume x of the regex, y of other.
  
*)
let at_help p pp s sp c = match c with
  '?' ->
    if pp + 1 > String.length p - 1 then None
    else if sp > String.length s - 1 then Some (2, 0)
    else if p.[pp + 1] = s.[sp] then Some (2, 1)
    else Some (2, 0)
  |'*' ->
    if pp > String.length p - 2 then None else
      Some (2, swallow_all p.[pp + 1] p sp)
  |'+' ->
    if pp > String.length p - 2 then None
    else if sp > String.length s - 1 then None
    else if p.[pp + 1] <> s.[sp] then None
    else  
      Some (2, swallow_all p.[pp+1] p sp)
  |c -> 
    if sp < String.length s && c = s.[sp] then
      Some (1, 1)
    else
      None;;

(*
  Go through the chars of the regex and consume the string.
*)
let rec at p pp s sp =
  pp > String.length p -1 ||
  match at_help p pp s sp p.[pp] with
    None -> false
    |Some (jump_p, jump_s) ->
      at p (pp + jump_p) s (sp + jump_s);;

(*
  This is basically another fancy for loop.
*)
let rec search_str' n p s =
  (n < String.length s || n = 0 && String.length s = 0)
  &&
  (at p 0 s n || search_str' (n + 1) p s);;

let search_str = search_str' 0;;

let test_search () =
  assert(search_list [5; 6] [4; 5; 6; 7]);
  assert(not(search_list [7; 8] [4; 5; 6; 7]));
  assert(search_list [4] [4; 5; 6; 7]);
  assert(search_str "bc" "abcd");
  assert(not(search_str "de" "abcd"));
  assert(search_str "d?e" "abcd");
  assert(not(search_str "?de" "abcd"));
  assert(not(search_str "*de" "abcd"));
  assert(search_str "*d" "abcd");
  assert(search_str "*d" "abcdd");
  assert(search_str "*d*e" "abcdd");
  assert(search_str "+d*e" "abcdd");
  assert(not(search_str "+d+e" "abcdd"));
  assert(search_str "a" "abcd");;

let main () = test_search ();;

main ();;
