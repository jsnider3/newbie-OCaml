open Core.Std
open Printf

type pdfobject =
  Boolean of bool
  |Integer of int
  |Float of float
  |String of string
  |Name of string
  |Array of pdfobject list
  |Dictionary of (string * pdfobject) list
  |Stream of pdfobject * string
  |Indirect of int

type t =
  {version : int * int;
   objects : (int * pdfobject) list;
   trailer : pdfobject}

(*
  F0 is f-zero not f-oh, messing that up will fail quietly.
  True story.
*)
let pdf_echo_obj strn =
  [(1, Dictionary
        [("/Type", Name "/Page");
         ("/Parent", Indirect 3);
         ("/Resources",
            Dictionary [("/Font",
              Dictionary [("/F0",
                Dictionary
                  [("/Type", Name "/Font");
                   ("/Subtype", Name "/Type1");
                   ("/BaseFont", Name "/Times-Italic")])])]);
         ("/MediaBox", Array [Float 0.; Float 0.;
                          Float 595.275590551; Float 841.88976378]);
         ("/Rotate", Integer 0); 
         ("/Contents", Array [Indirect 4])]);
  (2, Dictionary 
       [("/Type", Name "/Catalog");
        ("/Pages", Indirect 3)]);
  (3, Dictionary
       [("/Type", Name "/Pages");
        ("/Kids", Array [Indirect 1]);
        ("/Count", Integer 1)]);
  (4, Stream
      (Dictionary [("/Length", Integer 53)],
        "1 0 0 1 50 770 cm BT /F0 36 Tf (" ^ strn ^ ") Tj ET"))];; 

let pdf_echo strn =
  {version = (1, 1);
   objects = pdf_echo_obj strn;
   trailer = Dictionary 
      [("/Size", Integer 5);
       ("/Root", Indirect 2)]}

let rec string_of_pdfobject o =
  match o with
    Boolean b -> Bool.to_string b
    |Integer i -> Int.to_string i
    |Float f -> Float.to_string f
    |String s -> "(" ^ s ^ ")"
    |Name n -> n
    |Array a -> string_of_array a
    |Dictionary d -> string_of_dictionary d
    |Stream (dict, data) -> string_of_stream dict data
    |Indirect i -> sprintf "%i 0 R" i

and string_of_array a =
  let b = Buffer.create 100 in
    Buffer.add_string b "[";
    List.iter a 
      (fun s -> Buffer.add_char b ' ';
                Buffer.add_string b (string_of_pdfobject s));
    Buffer.add_string b " ]";
    Buffer.contents b

and string_of_dictionary d =
  let b = Buffer.create 100 in
    Buffer.add_string b "<<";
    List.iter d
      (fun (k, v) ->
        Buffer.add_char b ' ';
        Buffer.add_string b k;
        Buffer.add_char b ' ';
        Buffer.add_string b (string_of_pdfobject v));
    Buffer.add_string b " >>";
    Buffer.contents b

and string_of_stream dict data =
  let b = Buffer.create 100 in
    List.iter [string_of_pdfobject dict; "\nstream\n";
               data; "\nendstream"]
      (Buffer.add_string b);
    Buffer.contents b

let write_header o {version = (major, minor)} =
  output_string o
    (sprintf "%%PDF-%i.%i\n" major minor)

(*
  ULTRA-HERESY!
*)
let write_objects out objs =
  let offsets = ref [] in
    List.iter (List.sort ~cmp:compare objs)
      (fun (objnum, obj) ->
        offsets := Int64.to_int_exn (Out_channel.pos out) :: !offsets;
        Out_channel.output_string out (sprintf "%i 0 obj\n" objnum);
        Out_channel.output_string out (string_of_pdfobject obj);
        Out_channel.output_string out "\nendobj\n");
    List.rev !offsets

let write_trailer out pdf offsets =
  let startxref = Out_channel.pos out in
    Out_channel.output_string out "xref\n";
    Out_channel.output_string out 
      (sprintf "0 %i\n" (List.length pdf.objects + 1));
    Out_channel.output_string out "0000000000 65535 f \n";
    List.iter offsets
      (fun offset -> Out_channel.output_string out 
                      (sprintf "%010i 00000 n \n" offset));
    Out_channel.output_string out "trailer\n";
    Out_channel.output_string out (string_of_pdfobject pdf.trailer);
    Out_channel.output_string out "\nstartxref\n";
    Out_channel.output_string out (Int64.to_string startxref);
    Out_channel.output_string out "\n%%EOF";;

let pdf_to_file pdf filename =
  let output = open_out_bin filename in
    try 
      write_header output pdf;
      let offsets = write_objects output pdf.objects in
        write_trailer output pdf offsets;
        Out_channel.close output
    with
      e-> Out_channel.close output; raise e;
  ;;

let main () = let str = read_line () in
  pdf_to_file (pdf_echo str) "hello.pdf";;

main ()
