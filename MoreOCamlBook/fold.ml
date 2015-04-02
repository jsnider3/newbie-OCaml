open Core.Std;;
open Printf;;

(* What kind of pythonista would I be if I didn't have
   these functions? *)

let all l = List.fold ~f:(&&) ~init:true l;;

let any l = List.fold ~f:(||) ~init:false l;;

(* Like the concat from page 4, but should be faster
   since it's using fold_right instead of fold_left. *)
let fast_concat l = List.fold_right ~f:(@) ~init:[] l;;

(*
  Page 7 Question 1: Subtract a list of expenses from a budget
*)
let sub_expenses b e = List.fold ~f:(-) ~init:b e;;

(*
  Page 7 Question 2
*)
let list_len l = List.fold ~f:(fun x y -> x + 1) ~init:0 l;;

(*
  Page 7 Question 3: Return last element or None for []
*)
let last l = List.fold ~f:(fun x y -> Some y) ~init:None l;;

(*
  Page 7 Question 4
*)
let rev_list l = List.fold ~f:(fun x y-> y::x) ~init:[] l;;

(*
  Page 7 Question 5: See hoogle.
*)
let elem e l = List.fold ~f:(fun x y-> x || (e = y)) ~init:false l;;

(*
  Page 7 Question 6: See hoogle.
          This thing has pretty terrible efficiency, since strings are
          immutable and it needs to allocate a new one each time it 
          concats two strings together (which is O(n)).
*)

let interspace x y = match x with
  "" -> y;
  |_ -> x ^ " " ^ y;; 

let unwords l = List.fold ~f:interspace ~init:"" l;;

(*
  Page 7 Question 7: Find max depth of a tree.
    max_depth is of type fun 'a tree -> int
*)

type 'a tree =
  Lf | Br of 'a * 'a tree * 'a tree;;

let rec fold_tree f e t =
  match t with
    Lf -> e
    |Br(x, l, r) -> f x (fold_tree f e l) (fold_tree f e r);;

let max_depth tr = fold_tree (fun x l r -> 1 + max l r) 0 tr;;

(* 
  Test code: The most valuable and least interesting code!
*)

let test_depth () =
  let tr = Br (1, Br(0, Lf, Lf), Br(6, Br(4,Lf,Lf),Lf)) in
    assert(max_depth tr = 3);
    assert(max_depth (Br(1,Lf,Lf)) = 1);
    assert(max_depth Lf = 0);;

let test_expenses () =
  assert ((sub_expenses 10 [5]) = 5);
  assert ((sub_expenses 10 [5;3]) = 2);
  assert ((sub_expenses 20 [7;5;3;2]) = 3);;

let test_unwords () = let words = ["My"; "name"; "is"; "Josh"] in
  assert(unwords words = "My name is Josh");;

let main () = let lists = [[1]; [2]; [3]; [4]; [5]; [6];[7]] in
  let ans = [1;2;3;4;5;6;7] in
  let revd = [7;6;5;4;3;2;1] in
  assert ((fast_concat lists) = ans);
  assert (list_len(fast_concat lists) = 7);
  assert (last revd = Some 1);
  assert (last [] = None);
  assert (last ans = Some 7);
  assert (rev_list ans = revd);
  test_expenses();
  assert (elem 4 ans = true);
  assert (elem 9 revd = false);
  test_unwords();
  test_depth();;
main();;
