open Core.Std;;
open Printf;;

let rec drop ls n = match n with
  0 -> ls
  |_ -> drop (List.tl_exn ls) (n - 1);;

let rec take ls n = match n with
  0 -> []
  |_ -> List.hd_exn ls :: take (List.tl_exn ls) (n - 1);;

type turn = O | X | E;;

let won [a; b; c; d; e; f; g; h; i] =
  a && b && c || d && e && f || g && h && i || a && d && g ||
  b && e && h || c && f && i || a && e && i || c && e && g;;

let empties b =
  List.filter (List.mapi b 
    (fun i t -> if t = E then i+1 else 0)) ((<>) 0);;

let replace turn board p =
  take board (p - 1) @ [turn] @ drop board p;;

let flip_turn t =
  match t with O -> X | X -> O;;

type tree = Move of turn list * tree list;;

let rec next_moves turn board =
  let next =
    if won (List.map board ((=) O)) ||
      won (List.map board ((=) X)) 
    then
      []
    else
      List.map (List.map (empties board) (replace turn board))
        (next_moves (flip_turn turn))
  in
    Move (board, next);;

let main () = ();;

main ();;
