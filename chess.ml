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
   Everything else is unoccupied.` 
*)

(* Getting Core.Std installed was much harder than it needed to be.
   I have my ocamlinit set up, but because of the issue described at
   http://stackoverflow.com/q/20900465/ocaml-doesnt-load-ocamlinit-in-script-mode 
   I need to put these four here, otherwise Core won't be loaded
*)
#use "topfind"
#thread
#require "core"
open Core.Std

let get_exn a =
  match a with
    Some x -> x
   |_   -> invalid_arg "get_exn";;

let isValidSpot aSpot =
  let (tRow, tCol) = aSpot in
  tRow > -1 && tRow < 8 && tCol < 8 && tCol > -1;;

let rec findPiece board piece row =
  (* Return an (int,int) pair saying the coordinates of piece in board.
     Die with an exception if not found *)
  (* TODO Handle pieces that show up more than once, right now I'm just using
     it for kings. *)
  try
    (row, String.index_exn (List.hd_exn board ) piece);
  with e ->
    findPiece (List.tl_exn board) piece (row + 1);;

let getPieceAtSpot aBoard aSpot =
  let (tRow, tCol) = aSpot in
  let tRow = get_exn(List.nth aBoard tRow) in
  String.get tRow tCol;;

let addPos aPos aOffset =
  let (tRow, tCol) = aPos in
  let (tDeltaY, tDeltaX) = aOffset in
  (tRow + tDeltaY, tCol + tDeltaX);; 

let getTeam aPiece =
  match (Char.is_uppercase aPiece, Char.is_lowercase aPiece) with
    (true, false)  -> 1
   |(false, true) -> -1
   |_             -> invalid_arg "not a letter";;

let onTeam aTeam aPiece =
  aTeam = getTeam aPiece;;

let isPawn aPiece =
  aPiece = 'p' || aPiece = 'P';;

let isRook aPiece =
  aPiece = 'r' || aPiece = 'R';;

let isBishop aPiece =
  aPiece = 'b' || aPiece = 'B';;

let isQueen aPiece =
  aPiece = 'q' || aPiece = 'Q';;

let isKnight aPiece =
  aPiece = 'n' || aPiece = 'N';;

let movesDiagonal aPiece =
  isBishop aPiece || isQueen aPiece;;

let movesSideways aPiece =
  isRook aPiece || isQueen aPiece;;

let getTeamName aTeam =
  match aTeam with
    1   -> "Black" ;
   |(-1)-> "White" ;
   |_   -> invalid_arg "getTeamName";;

let printCheckWarning aTeam aPiece =
  print_string (getTeamName aTeam);
  print_string " is in check from ";
  print_char aPiece;
  print_endline ".";;

let rec lookForCheckHelper aBoard aLoc aTeam aFilter aLoop aOffset =
  let tLoc = addPos aLoc aOffset in
  if isValidSpot tLoc then
  begin
    let tPiece = getPieceAtSpot aBoard tLoc in
    if aFilter tPiece && getTeam tPiece <> aTeam then
      printCheckWarning aTeam tPiece;
    if aLoop then
      lookForCheckHelper aBoard tLoc aTeam aFilter aLoop aOffset;
  end
  ;;

let lookForKnightCheck aBoard aKingPos aTeam =
  let tMoves = [(-2,-1);(-2,1);(2,-1);(2,1);(-1,-2);(-1,2);(1,-2);(1,2)] in
  List.map tMoves (lookForCheckHelper aBoard aKingPos aTeam isPawn false);;

let lookForPawnCheck aBoard aKingPos aTeam =
  let tMoves = [(aTeam,-1);(aTeam,1)] in
  List.map tMoves (lookForCheckHelper aBoard aKingPos aTeam isPawn false);;

let lookForRookCheck aBoard aKingPos aTeam =
  let tMoves = [(0,-1);(-1,0);(1,0);(0,1)] in
  List.map tMoves (lookForCheckHelper aBoard aKingPos aTeam movesSideways true);;

let lookForBishopCheck aBoard aKingPos aTeam =
  let tMoves = [(-1,-1);(-1,1);(1,-1);(1,1)] in
  List.map tMoves (lookForCheckHelper aBoard aKingPos aTeam movesDiagonal true);;

let checkForCheck aBoard aKing =
  let tKingPos = findPiece aBoard aKing 0 in
  let tTeam = getTeam aKing in
  lookForKnightCheck aBoard tKingPos tTeam;
  lookForPawnCheck aBoard tKingPos tTeam;
  lookForRookCheck aBoard tKingPos tTeam;
  lookForBishopCheck aBoard tKingPos tTeam;;

let processBoard aFile =
  (* Take the board and check for checks.*)
  print_endline (List.hd_exn aFile);
  (* Discard seperator line *)
  let tFile = List.tl_exn aFile in
  checkForCheck tFile 'K';
  checkForCheck tFile 'k';;

let rec processBoards aFile =
  let (tBoard,tFile) = List.split_n aFile 9 in
  processBoard tBoard;
  match tFile with
    [] -> true;
    |_ -> processBoards tFile;
  ;;

let main () =
  (* I think it looks better organized with an explicit main *)
  let kFile = "chess.txt" in
  let tFile = In_channel.read_lines kFile in
  (* Get the number of boards to process and start looping over them. *)
  let _ = int_of_string (List.hd_exn tFile) in
  let tFile = List.tl_exn tFile in
  processBoards tFile;;

main ();
