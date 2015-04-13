open Core.Std;;
open Printf;;

let print_int_list ls = printf "[" ;
  printf "%s]" (String.concat ~sep:"; " (List.map ls (sprintf "%d")));;

(*
  Not fully correct, but no need to fix something that's for debug only.
*)
let print_int_list_list ls = 
  printf "[" ;
  List.map ls print_int_list;
  printf "]\n" ;;

(*
  Seen/interleave could be made optional value and default to [].
  But since it's a helper function, we can just hope our
  future selves remember how to use it.
*)
let rec interleave acc e seen l =
  match l with
    [] -> List.rev((seen @ [e]) :: acc)
    |x::xs -> interleave ((seen @ e :: x :: xs)::acc) e (seen @ [x]) xs;;

let combine x ps =
  List.concat(List.map ps (interleave [] x []));;

(*let rec perms p =
  match p with
    [] -> [[]]
    |(h::t) -> combine h (perms t);;*)

let rec without x l =
  match l with
    [] -> []
    |h::t -> if h = x then t else h :: without x t;;

let rec perms l =
  match l with
    [] -> [[]]
    | _ -> List.concat (List.map l 
              (fun x -> List.map (perms (without x l)) (fun l -> x :: l)));;

(*
  Finds the last element that is less
  than its successor. Returns 
  len(arr) - 1 for failure.
*)


let first arr =
  let rec first_help best x = 
    if x = Array.length arr - 1 then best
      else if arr.(x) < arr.(x + 1) 
        then first_help x (x+1)
        else first_help best (x+1) 
  in
    first_help (Array.length arr - 1) 0;;

(*
  f is the result of calling first above.
  This function tries to find the 
  smallest index i where i > f and
  arr.(i) > arr.(f).
  -1 means the list is reverse-sorted.
*)

let last arr f =
  let rec last_help best ind =
    if ind = f then best
      else if arr.(ind) > arr.(f) && (best = -1 || arr.(ind) < arr.(best))
        then last_help ind (ind - 1)
        else last_help best (ind - 1)
  in
    last_help (-1) (Array.length arr - 1);;

(*
  Standard issue swap. Identical to how this would be done in C.
*)
let swap arr a b =
  let t = arr.(a) in
    arr.(a) <- arr.(b);
    arr.(b) <- t;;

(*
  Make a copy of a subarray, sort it,
  and write it into the original
*)
let sort_subarray arr o l =
  let sub = Array.sub arr o l in
    Array.sort sub compare;
    Array.blit sub 0 arr o l;;

let next_permutation arr_in =
  let arr = Array.copy arr_in in
  let f = first arr in
  let c = last arr f in
    swap arr f c;
    sort_subarray arr (f + 1) (Array.length arr - 1 - f);
    arr;;

let non_increasing arr =
  let rec non_increasing_loop arr ind =
    ind = 0 ||
    (arr.(ind) <= arr.(ind - 1) &&
     non_increasing_loop arr (ind - 1))
  in
    Array.length arr <= 1 ||
    non_increasing_loop arr (Array.length arr - 1);;

(*
  Disgustingly imperative.
*)
let all_permutations arr =
  let copy = Array.copy arr in
    Array.sort copy compare;
    let perm = ref copy in
    let perms = ref [copy] in
      while not (non_increasing !perm) do
        perm := next_permutation !perm;
        perms := !perm :: !perms;
      done;
      Array.of_list (List.rev !perms);;

type 'a lazylist = Cons of 'a * (unit -> 'a lazylist);; 

let rec perms_lazy x =
  Cons (x, fun () ->
    if non_increasing x then
      let c = Array.copy x in
        Array.rev_inplace c;
        perms_lazy c
    else
      perms_lazy (next_permutation x));;

let test_lazy () = match perms_lazy [|1;2|] with
  Cons (_, f) -> match f() with
    Cons (x,_)-> assert( x = [|2;1|]);;
let main () = 
  print_int_list_list (perms[1; 2]);
  print_int_list_list (perms[1; 2; 3; 4]);
  assert(perms[1; 2] = [[1; 2];[2; 1]]);;
  assert(List.length (perms[1; 2; 3; 4]) = 4*3*2*1);
  assert(next_permutation[|1; 2|] = [|2; 1|]);
  assert(next_permutation[|1; 2|] = [|2; 1|]);
  assert(non_increasing[|3; 2; 1|]);
  assert(not (non_increasing[|3; 1; 2|]));
  assert(next_permutation[|1; 4; 2; 3|] = [|1; 4; 3; 2|]);
  test_lazy ();;

main ();;
