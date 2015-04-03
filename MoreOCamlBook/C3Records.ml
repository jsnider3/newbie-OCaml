open Core.Std;;
open Gc;;
open Gc.Stat;;
open Printf;;
open Unix;;

(*
  Page 19 Question 1
*)
let change_ref x n = x.contents <- n;;
  
(*
  Page 19 Question 2
*)

let string_of_hour tm = sprintf "%02d%02dZ" tm.tm_hour tm.tm_min;;

let string_of_date tm = 
  sprintf "%d/%d/%d" (tm.tm_year + 1900) (tm.tm_mon + 1)(tm.tm_mday);;

let print_time tm = 
  let fmt = format_of_string "It is %s on %s.\n" in
  printf fmt (string_of_hour tm) (string_of_date tm);;

(*
  Page 19 Question 3: The difference between type t = {x: int ref}
    and type t = {mutable x: int} is ...
*)

(*
  Page 19 Question 4
*)
type ('a,'b,'c) thing = {a:'a; b:'a; c:'b; d:'b; e:'c; f:'c};;

(*
  Page 19 Question 5: With bare-bones OCaml you could make it
    verbose with something like gc.set { (gc.get()) with Gc.verbose = 63 };
*)

let print_gc_stats () = 
  let out = open_out "/tmp/gcstats.txt" in
  let stats = Gc.stat() in
  fprintf out "GC STATS\n";
  fprintf out "minor words: %f\n" stats.minor_words;
  fprintf out "promoted words: %f\n" stats.promoted_words;
  fprintf out "major words: %f\n" stats.major_words;
  fprintf out "minor collections: %d\n" stats.minor_collections;
  fprintf out "major collections: %d\n" stats.major_collections;
  fprintf out "heap words: %d\n" stats.heap_words;
  fprintf out "heap chunks: %d\n" stats.heap_chunks;
  fprintf out "live words: %d\n" stats.live_words;
  fprintf out "live blocks: %d\n" stats.live_blocks;
  fprintf out "free words: %d\n" stats.free_words;
  fprintf out "free blocks: %d\n" stats.free_blocks;
  fprintf out "largest free: %d\n" stats.largest_free;
  fprintf out "fragments: %d\n" stats.fragments;
  fprintf out "compactions: %d\n" stats.compactions;
  fprintf out "top heap words: %d\n" stats.top_heap_words;
  fprintf out "stack size: %d\n" stats.stack_size;
  Out_channel.close out;;

let test_ref () = let x = ref 0 in
  change_ref x 5;;
(*  assert (x.contents = 5);;*) (* Weird error if this is uncommented. *)

let main () = test_ref();
  print_time (gmtime (time ()));
  print_gc_stats ();
  print_time (gmtime (time ()));;

main ();;
