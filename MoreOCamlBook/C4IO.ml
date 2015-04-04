open Core.Std;;
open Printf;;

type input =
  {
   pos_in : unit -> int;
   seek_in : int -> unit;
   input_char : unit -> char;
   input_byte : unit -> int;
   input_char_opt : unit -> char option;
   length : int
  };;

(*
  Page 26: Question 1 
*)
let input_of_chars chs = let pos = ref 0 in
  {
    pos_in = (fun() -> !pos);
    seek_in = (fun p ->
                if p < 0
                  then raise(Invalid_argument "Can't do that");
                pos := p);
    input_char = (fun () ->
                  (if !pos = (List.length chs)
                      then raise End_of_file;
                   pos := (!pos + 1);
                   List.nth_exn chs (!pos - 1);
                  )
                 );
    input_char_opt = (fun () ->
                   pos := (!pos + 1);
                   List.nth chs (!pos - 1);
                 );
    input_byte = (fun () ->
                   pos := (!pos + 1);
                   match List.nth chs (!pos - 1) with
                    Some x -> Char.to_int x
                    |None -> -1;
                 );
    length = List.length chs;
  };;

(*
  Page 26: Question 2
*)
let rec input_string inp len = match len with
  0 -> ""
  |_ ->   try (let c = String.of_char (inp.input_char()) in
            c ^ input_string inp (len - 1)) with
            _ -> "";;

(*
  Page 26: Question 3
*)
let int64_to_int n = match Int64.to_int n with
  Some x -> x
  |None -> raise(Invalid_argument "not a number?");;

let input_of_channel ch =
  { 
   pos_in = (fun () -> int64_to_int (In_channel.pos ch));
   seek_in = (fun n -> In_channel.seek ch (Int64.of_int n));
   input_char = (fun () -> input_char ch);
   input_char_opt = (fun () -> In_channel.input_char ch);
   input_byte = (fun () -> match In_channel.input_char ch with
                                Some x -> Char.to_int x
                                |None -> -1);
   length = int64_to_int (In_channel.length ch)
  };;

let input_of_string ch = let pos = ref 0 in
  {
   pos_in = (fun () -> !pos);
   seek_in = (fun p -> if p < 0 then
                          raise (Invalid_argument "seek before start");
                        pos := p);
   input_char = (fun () -> if !pos > (String.length ch - 1)
                             then raise End_of_file
                             else (let c = ch.[!pos] in 
                                  pos := 1 + !pos; c));
   input_char_opt = (fun () -> if !pos > (String.length ch - 1)
                             then None
                             else (let c = ch.[!pos] in 
                                  pos := 1 + !pos; Some c));

   input_byte = (fun () -> if !pos > (String.length ch - 1)
                             then -1
                             else (let c = ch.[!pos] in 
                                  pos := 1 + !pos; Char.to_int c));
   length = String.length ch
  };;

(*
  Page 26: Question 5
*)
let line_reader ch = {ch with
   input_char = (fun () -> match ch.input_char () with
                            '\n' -> raise End_of_file
                            |x -> x;);
   input_char_opt = (fun () -> match ch.input_char_opt () with
                             Some '\n' -> None
                             |x -> x);

   input_byte = (fun () -> match ch.input_byte () with
                            10 -> raise End_of_file
                            |x -> x);
  (*
    The length field for this record is now invalid. 
  *)
  };;

(*
  Page 26: Question 5
*)

type output =
  {
    output_char : char -> unit;
    out_channel_length : unit -> int;
  };;

let output_of_buffer bf = 
  {
    output_char = (fun c -> Buffer.add_char bf c);
    out_channel_length = (fun c -> Buffer.length bf);
  };;

(*

*)
let test_input_of_chars () =
  let inp = input_of_chars ['a'; 'b'; 'c'] in
  assert (inp.input_char () = 'a');
  assert (inp.input_char () = 'b');
  assert (inp.input_char () = 'c');
  assert (inp.input_char_opt () = None);
  inp.seek_in 0;
  assert ("abc" = (input_string inp 4));;

let test_input_of_channel () =
  let inp = input_of_channel (open_in "C4IO.ml") in
  assert ("open Core.Std;;" = (input_string inp 15));;

let test_line_reader () =
  let inp = line_reader(input_of_channel (open_in "C4IO.ml")) in
  assert ("open Core.Std;;" = (input_string inp 95));;

let main () = 
  test_input_of_chars ();
  test_input_of_channel ();
  test_line_reader ();;

main ();;

