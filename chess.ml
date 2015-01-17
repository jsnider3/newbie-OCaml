(* The plan for this program is to read a series of chess boards from a file,
   and then determine if either party is in check.*)
(* Stretch goals are to check for mate and to check that the board is valid. *)

(* INPUT FORMAT *)
(* The first line is a single integer saying how many chess boards will be
   provided as input. Each chess board starts with a comment line that is 
   ignored to improve readability for humans. The chess board itself will be
   eight rows of eight chars. The white side will be on the bottom and black
   will be on top. Uppercase chars are black pieces and lowercase chars are
   white pieces.
   P/p = Pawn
   K/k = King
   Q/q = Queen
   R/r = Rook
   B/b = Bishop
   N/n = kNight
   X   = Unoccupied 
*)

(* Getting this line to compile was absurdly hard *)
(* open Core.Std;; *)

let rec readline aFile =
  (* read a line from a file and echo it *)
  let tLine = input_line aFile in
  print_endline tLine;
  tLine;;

let rec findPiece board piece row =
  try
    (row, String.index (List.nth board 0) piece);
  with e ->
    findPiece (List.tl board) piece (row + 1);;

let checkForBlackCheck board =
  let (xPos, yPos) = findPiece board 'K' 0 in
  (* TODO Actually fucking work *)
  print_string "(";
  print_int xPos;
  print_string ", ";
  print_int yPos;
  print_string ")\n";  
  1;;

let processBoard aFile =
  (* Take the board, read it in, check for check.*)

  (* Discard seperator line *)
  readline aFile;

  (* Read the board into a list of strings *)
  let board = ref [] in
    for num = 1 to 8 do
       board := readline aFile::!board 
    done;
    board := List.rev !board;  
    (* Before I added this List.rev line, there was a bug with findPiece.
       The bug was from the list being reversed relative to my expectations. 
       My first thought was to append to the list instead of prepending to it, 
       but http://stackoverflow.com/q/6732524/what-is-the-easiest-way-to-add-an-element-to-the-end-of-the-list 
       taught me that was inefficient and that the correct procedure was to
       prepend to the list and then reverse it at the end.*)
    checkForBlackCheck !board;;

let rec processBoards numBoards aFile =
  (* Basicall*)
  if numBoards > 0 then
  begin 
    processBoard aFile;
    processBoards (numBoards - 1) aFile;
  end;
  ();;

let chessMain () =
  (* I think it looks better organized with an explicit main *)
  let kFile = "chess.txt" in
  let tFile = open_in kFile in
  try
    (* Get the number of boards to process and start looping over them. *)
    let numBoards = int_of_string (input_line tFile) in
    processBoards numBoards tFile;
    close_in tFile
  with e ->
    close_in_noerr tFile;
    raise e;;

chessMain ();
