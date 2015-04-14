open Core.Std;;
open Printf;;

module type SetType =
  sig
    type 'a t;;
    val set_of_list : 'a list -> 'a t;;
    val list_of_set : 'a t -> 'a list;;
    val insert : 'a t -> 'a -> 'a t;;
    val size : 'a t -> int;;
    val member : 'a t -> 'a -> bool;;
  end

module SetList : sig include SetType end =
  struct
    type 'a t = 'a list;;
    
    (*
      This will actually err if you omit the x's,
      http://stackoverflow.com/q/29597863/.
    *)
    let member x = List.mem ~equal:(=) x;;

    (*
      Prepend x to the backing list.
    *)
    let insert l x = if member l x then l else x::l;;

    let rec set_of_list l = match l with
      [] -> []
      |h::t -> insert (set_of_list t) h;;

    let list_of_set x = x;;

    let size = List.length;;
  end;;

module SetTree : sig include SetType end =
  struct
    type 'a t = Lf | Br of 'a t * 'a * 'a t;;
    
    (*
      Not tail recursive
    *)
    (*let rec listify ?(acc=[]) s =
      match s with
        Lf -> acc
        |Br (l, x, r) -> listify l ~acc:(listify r ~acc:(x::acc));; *)

    let rec list_of_set s =
      match s with
        Lf -> []
        |Br (l, x, r) -> list_of_set l @ [x] @ list_of_set r;;

    let rec insert s x =
      match s with
        Lf -> Br (Lf, x, Lf)
        |Br (l, y, r) -> if x = y then Br (l, y, r)
          else if x < y then Br(insert l x, y, r)
          else Br(l, y, insert r x);;

    (*
      I'm pretty sure that this is inefficient
      and that we do this smarter than just
      adding the elements one-by-one.
    *)
    let rec set_of_list l =
      match l with
        [] -> Lf
        |h::t -> insert (set_of_list t) h;;

    let rec size s =
      match s with
        Lf -> 0
        | Br(l, _, r) -> 1 + size l + size r;;

    let rec member s x =
      match s with
        Lf -> false
        |Br (_, y, _) when x = y -> true
        |Br (l, y, r) -> if x < y then member l x else member r x;;
  end;;

module SetRB : sig include SetType end =
  struct
    (*
      A red-black tre is a binary tree where each node is either red or black.
      All leaves are black. Any child of a red is black. Any path from the
      root to leaf contains an equal number of blacks.
    *)
    type color = R | B;;

    type 'a t = Lf | Br of color * 'a t * 'a * 'a t;;
  
    (*
      TODO explain.
    *)
    let balance t = match t with
      (B, Br (R, Br (R, a, x, b), y, c), z, d)
      |(B, Br (R, a, x, Br (R, b, y, c)), z, d)
      |(B, a, x, Br (R, Br (R, b, y, c), z, d))
      |(B, a, x, Br (R, b, y, Br (R, c, z, d))) ->
        Br (R, Br (R, a, x, b), y, Br (B, c, z,d))
      |(a, b, c, d) -> Br (a, b, c, d);;

    let rec list_of_set s =
      match s with
        Lf -> []
        |Br (c, l, x, r) -> list_of_set l @ [x] @ list_of_set r;;

    let rec insert_inner s x = 
      match s with
        Lf -> Br (R, Lf, x, Lf)
        |Br (c, l, y, r) ->
          if x < y
            then balance (c, insert_inner l x, y, r)
            else if x > y then balance (c, l, y, insert_inner r x)  
            else Br (c, l, y, r);;

    let insert s x =
      match insert_inner s x with
        Br (_, l, y, r) -> Br (B, l, y, r)
        |Lf -> assert false;; (* Not possible, but supresses warning *)

    (*
      These three are just copypasted from the other one.
    *)
    let rec set_of_list l =
      match l with
        [] -> Lf
        |h::t -> insert (set_of_list t) h;;

    let rec size s =
      match s with
        Lf -> 0
        | Br(_, l, _, r) -> 1 + size l + size r;;

    let rec member s x =
      match s with
        Lf -> false
        |Br (_, _, y, _) when x = y -> true
        |Br (_, l, y, r) -> if x < y then member l x else member r x;;
  end;;

module SetHash : sig include SetType end =
  struct
    type 'a t = ('a, unit) Hashtbl.t;;

    let list_of_set s = Hashtbl.fold s ~init:[] ~f:(fun ~key:x ~data:() l -> x::l);;

    (*
      Translating this from stdlib to core was a huge pain.
    *)
    let set_of_list l = let s = Hashtbl.create ~hashable:Hashtbl.Poly.hashable () in
      List.map l (fun x -> Hashtbl.add s ~key:x ~data:());
      s;;

    let member s x = Hashtbl.mem s x;;

    let insert s x = 
      Hashtbl.add ~key:x ~data:() s;
      s;;

    let size = Hashtbl.length;;
  end;;

let test_set () =
  assert(SetList.list_of_set (SetList.set_of_list [2;2;2]) = [2]);
  assert(SetList.size (SetList.set_of_list [2;2;2]) = 1);
  List.map [2;3;4;5] (fun x -> (SetList.member (SetList.set_of_list [2;3;4;5]) x));
  assert(not(SetList.member (SetList.set_of_list [2;3;4;5]) 6));;

let test_tree () =
  assert(SetTree.list_of_set (SetTree.set_of_list [2;2;2]) = [2]);
  assert(SetTree.size (SetTree.set_of_list [2;2;2]) = 1);
  List.map [2;3;4;5] (fun x -> (SetTree.member (SetTree.set_of_list [2;3;4;5]) x));
  assert(not(SetTree.member (SetTree.set_of_list [2;3;4;5]) 6));;

let test_rb () =
  assert(SetRB.list_of_set (SetRB.set_of_list [2;2;2]) = [2]);
  assert(SetRB.size (SetRB.set_of_list [2;2;2]) = 1);
  List.map [2;3;4;5] (fun x -> (SetRB.member (SetRB.set_of_list [2;3;4;5]) x));
  assert(not(SetRB.member (SetRB.set_of_list [2;3;4;5]) 6));;

let main () = 
  test_set ();
  test_tree ();
  test_rb ();;

main ();;
