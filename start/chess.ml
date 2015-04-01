(* Basically, what this program does is read a series of chess boards from
   a file called chess.in, and determine if anyone is in check. *)

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
   _   = Unoccupied 
*)

(* Getting Core.Std installed was much harder than it needed to be.
   I have my ocamlinit set up, but because of the issue described at
   http://stackoverflow.com/q/20900465/ocaml-doesnt-load-ocamlinit-in-script-mode 
   I need to put these four here, otherwise Core won't be loaded.
   I might look into build systes for OCaml, in case one of them has a solution.
*)
#use "topfind"
#thread
#require "core"
open Core.Std

let get_exn aOption =
  (* Convenience function for getting the thing from an option, when we 
     can safely assume it's not None. *)
  match aOption with
    Some x -> x
   |_   -> invalid_arg "get_exn";;

let is_valid_spot aSpot =
  (* is spot on the 8x8 chess board? *)
  let (tRow, tCol) = aSpot in
  tRow > -1 && tRow < 8 && tCol < 8 && tCol > -1;;

let rec find_king aBoard aKing aRow =
  (* Return an (int,int) pair saying the coordinates of aKing.
     Die with an exception if not found *)
  match String.index (List.hd_exn aBoard) aKing with
    Some tCol -> (aRow, tCol);
    |_ -> find_king (List.tl_exn aBoard) aKing (aRow + 1);;

let get_piece_at_spot aBoard aSpot =
  let (tRow, tCol) = aSpot in
  let tRow = get_exn(List.nth aBoard tRow) in
  String.get tRow tCol;;

let add_pos aPos aOffset =
  let (tRow, tCol) = aPos in
  let (tDeltaY, tDeltaX) = aOffset in
  (tRow + tDeltaY, tCol + tDeltaX);; 

let get_team aPiece =
  match (Char.is_uppercase aPiece, Char.is_lowercase aPiece) with
    (true, false)  -> 1
   |(false, true) -> -1
   |_             -> invalid_arg "not a letter";;

let on_team aTeam aPiece =
  aTeam = get_team aPiece;;

let is_pawn aPiece =
  Char.uppercase aPiece = 'P';;

let is_rook aPiece =
  Char.uppercase aPiece = 'R';;

let is_bishop aPiece =
  Char.uppercase aPiece = 'B';;

let is_queen aPiece =
  Char.uppercase aPiece = 'Q';;

let is_knight aPiece =
  Char.uppercase aPiece = 'N';;

let is_empty_spot aPiece =
   aPiece = '_';;

let moves_diagonally aPiece =
  is_bishop aPiece || is_queen aPiece;;

let moves_sideways aPiece =
  is_rook aPiece || is_queen aPiece;;

let get_team_name aTeam =
  (* The reason 1 is Black and -1 is white is so that they are the same as the
     movement of the enemy pawns *) 
  match aTeam with
    1   -> "Black" ;
   |(-1)-> "White" ;
   |_   -> invalid_arg "get_team_name";;

let print_check_warning aTeam aPiece =
  (* Print [Black|White] is in check from [p|r|q|n|b]. *)
  print_string (get_team_name aTeam);
  print_string " is in check from ";
  print_char aPiece;
  print_endline ".";;

let rec look_for_check_helper aBoard aLoc aTeam aFilter aLoop aOffset =
  (* This is the workhorse of the entire program. Take an offset fro the King,
     use aFilter to see if anyone there is capable of moving that way, if so 
     print a warning, then continue in that direction if we can and should. *)
  let tLoc = add_pos aLoc aOffset in
  if is_valid_spot tLoc then
  begin
    let tPiece = get_piece_at_spot aBoard tLoc in
    if aFilter tPiece && get_team tPiece <> aTeam then
      print_check_warning aTeam tPiece;
    if aLoop && false = (is_empty_spot tPiece) then
      look_for_check_helper aBoard tLoc aTeam aFilter aLoop aOffset;
  end;
  ()
  ;;

let look_for_knight_check aBoard aKingPos aTeam =
  (* Is there a knight one move away? *)
  let tMoves = [(-2,-1);(-2,1);(2,-1);(2,1);(-1,-2);(-1,2);(1,-2);(1,2)] in
  List.iter tMoves (look_for_check_helper aBoard aKingPos aTeam is_knight false);;

let look_for_pawn_check aBoard aKingPos aTeam =
  (* Is there a pawn one move away? *)
  let tMoves = [(aTeam,-1);(aTeam,1)] in
  List.iter tMoves (look_for_check_helper aBoard aKingPos aTeam is_pawn false);;

let look_for_rook_check aBoard aKingPos aTeam =
  (* Is there a rook or a queen in a straight unblocked line from the king? *)
  let tMoves = [(0,-1);(-1,0);(1,0);(0,1)] in
  List.iter tMoves (look_for_check_helper aBoard aKingPos aTeam moves_sideways true);;

let look_for_bishop_check aBoard aKingPos aTeam =
  (* Is there a bishop or a queen in a straight unblocked line from the king? *)
  let tMoves = [(-1,-1);(-1,1);(1,-1);(1,1)] in
  List.iter tMoves (look_for_check_helper aBoard aKingPos aTeam moves_diagonally true);;

let check_for_check aBoard aKing =
  (* Is there someone who can kill aKing? *)
  let tKingPos = find_king aBoard aKing 0 in
  let tTeam = get_team aKing in
  look_for_knight_check aBoard tKingPos tTeam;
  look_for_pawn_check aBoard tKingPos tTeam;
  look_for_rook_check aBoard tKingPos tTeam;
  look_for_bishop_check aBoard tKingPos tTeam;;

let process_board aFile =
  (* Print and then discard comment.*)
  print_endline (List.hd_exn aFile);
  let tFile = List.tl_exn aFile in
  (* Check both teams for being in check. *)
  check_for_check tFile 'K';
  check_for_check tFile 'k';;

let rec process_boards aFile =
  let (tBoard,tFile) = List.split_n aFile 9 in
  process_board tBoard;
  match tFile with
    [] -> ();
    |_ -> process_boards tFile;
  ;;

let main () =
  (* I think it looks better organized with an explicit main *)
  let kFile = "chess.in" in
  let tFile = In_channel.read_lines kFile in
  (* Get the number of boards to process and start looping over them. *)
  let _ = int_of_string (List.hd_exn tFile) in
  let tFile = List.tl_exn tFile in
  process_boards tFile;;

main ();
