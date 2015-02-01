open Core.Std

(* I would prefer to call kind "type", but that is very much not allowed in OCaml.*)
type kind = TInt | TReal | TBool | TChar | TFunc of (kind * kind) | TTuple of kind list | TyL of kind |
           TyR of kind | TList of (kind * int) | TRecord of (string * kind) list | TUnit | TSum of (kind * kind) | 
           TTop | TBottom | TStr

type expr = N of int | F of float| Add of (expr * expr) | Mul of (expr * expr) | Sub of (expr * expr)
    |And of (expr * expr) | Or of (expr * expr) |Not of expr |If of (expr * expr * expr) |Equal of (expr * expr) | B of bool
    |Lam of (kind * string * expr) | App of (expr * expr) | Var of string |Tuple of expr list
    |List of (expr * expr) 
    |Unit |Concat of (expr * expr) | Get of (expr * expr) | Head of expr | Tail of expr
    |Record of (string * expr) list | GetRec of (string * expr)
    |Fix of expr | LetN of ((string * expr) list * expr)  
    |TL of expr| TR of expr| Case of (expr * expr * expr) |As of (expr * kind) 
    |Seq of expr list |Set of (kind * string * expr) |Lookup of string |While of (expr * expr)
    |Top | Bottom
    |C of char

type value = VB of bool | VC of char | VTuple of value list | VList of (value * value) | VUnit | VL of value | VR of value |
             VN of int |VF of float| VLam of expr | VRecord of (string * value) list | VTop | VBottom

type env_type = (string, value) Hashtbl.t;;
type type_map = (string, kind) Hashtbl.t;;

(*
  string_of_expr ::expr->string
*)

let rec string_of_expr arg = match arg with
  N a -> "N " ^ string_of_int a
  |F f -> "F " ^ Float.to_string f
  |B b -> "B " ^ string_of_bool b
  |Add (a,b) -> "Add(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ ")"
  |Mul (a,b) -> "Mul(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ ")"
  |Sub (a,b) -> "Sub(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ ")"
  |And (a,b) -> "And(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ ")"
  |Or (a,b) -> "Or(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ ")"
  |Not a -> "Not(" ^ string_of_expr a ^ ")"
  |If (a,b,c)-> "If(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ "," ^ string_of_expr c ^ ")"
  |Equal (a,b) -> "Equal(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ ")"
  |Lam (a,b,c) -> "Lam(a," ^ b ^ "," ^ string_of_expr c ^ ")"
  |App (a,b) -> "App(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ ")"
  |Var s -> "Var " ^ s
  |Tuple lis -> "Tuple [lis]"
  |List (a,b) -> "List(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ ")"
  |Unit -> "Unit"
  |Concat (a,b) -> "Concat(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ ")"
  |Get (a,b) -> "Get(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ ")"
  |Head a -> "Head(" ^ string_of_expr a ^ ")"
  |Tail a -> "Tail(" ^ string_of_expr a ^ ")"
  |GetRec (a,b) -> "GetRec(" ^ a ^ "," ^ string_of_expr b ^ ")"
  |TL a -> "TL(" ^ string_of_expr a ^ ")"
  |TR a -> "TR(" ^ string_of_expr a ^ ")"
  |Case (a,b,c) -> "Case(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ "," ^ string_of_expr c ^ ")"
  |As (a,b) -> "As(" ^ string_of_expr a ^ ",kind)"
  |Lookup a -> "Lookup " ^ a
  |While (a,b) -> "While(" ^ string_of_expr a ^ "," ^ string_of_expr b ^ ")"
  |_ -> "TODO: string_of_expr"


let poly_set = Set.of_list ~comparator:Comparator.Poly.comparator

(*
  sub_type ::kind->kind->bool
*)
let rec subtype t1 t2 = match  (t1, t2) with
  (TInt, TReal) ->true
  |(TBottom, _) -> true
  |(_, TTop) -> true
  |((TRecord rec1),(TRecord rec2)) -> Set.length(Set.diff (poly_set rec2) (poly_set rec1)) = 0 
  |(TFunc(a,b),TFunc(c,d)) -> subtype c a && subtype b d
  |(a,b) -> a = b;;

(*
  common_type ::kind->kind->kind
*)
let common_type t1 t2 = match (t1, t2) with
  ((TRecord a),(TRecord b)) -> raise (Failure "TODO TRecord(intersect a b)")
  |(a,b) -> if subtype a b then b else if subtype b a then a else TTop

let echo_first f s = f;;
(*
  typecheck ::expr -> type_map -> kind
        suspicious expression -> lookup table -> type it returns
  Makes sure an expression uses types correctly and either returns 
  a value of a single type or returns an error.
*)      
let rec typecheck expr env = match expr with
  C _ -> TChar
  |N _ -> TInt
  |F _ -> TReal
  |B _ -> TBool
  |Unit -> TUnit
  |Top -> TTop
  |Bottom -> TBottom
  |Equal (_,_) -> TBool
  |Add (a, b) -> typecheck (Sub (a,b)) env
  |Mul (a, b) -> typecheck (Sub (a,b)) env
  |Sub (a, b) -> if subtype(typecheck a env) TReal && subtype(typecheck b env) TReal 
    then common_type (typecheck a env)(typecheck b env) 
    else raise (Failure "Can't do arithmetic on non-numbers.")
  |Or  (a,b) -> typecheck (And (a, b)) env
  |And (a, b) -> if subtype(typecheck a env) TBool && subtype(typecheck b env) TBool 
    then common_type (typecheck a env)(typecheck b env) 
    else raise (Failure "Can't do bool ops on non-bools.")
  |If (a, b, c) -> if subtype(typecheck a env) TBool 
    then common_type(typecheck b env)(typecheck c env) (*TODO DEBUG Original code checked that neither changed the state. *)
    else raise (Failure ("If guard " ^string_of_expr a ^ " is non-bool."))
  |Not a -> if subtype(typecheck a env) TBool then TBool else raise (Failure "Not of non-bool")                                                  
  |Tuple a -> TTuple (List.map a (fun a -> typecheck a env)) 
  |Head a -> begin
    match typecheck a env with
      TList (type1, _) -> type1
      |_ -> raise (Failure "Head only works on lists.")
    end
  |Tail a -> begin
    match typecheck a env with
      TList (listType, len) -> begin
        match a with
          List (_, Unit) -> TUnit 
          |List (_, _) -> TList (listType, (len-1))
          |_ -> raise (Failure "Tail only works on pairs and lists.")
        end
      |_ -> raise (Failure "Can't apply tail to non-lists")
    end
  |Concat (a, b) ->  begin
    match (typecheck a env, typecheck b env ) with
      (TList (type1, alen), TList (type2, blen)) -> TList ((common_type type1 type2), (alen + blen))
      |_ -> raise (Failure "Can't concat non-lists.")
    end
  |List (head, rest) -> begin
    match typecheck head env with
      TUnit -> raise (Failure "Lists cannot be headed by null.")
      |TList (_, _) -> raise (Failure "Lists cannot be headed by lists.")
      |goodType -> match typecheck rest env with
        TUnit -> TList (goodType, 1)
        |TList (type2, len) -> TList ((common_type goodType type2), (len+1))
        |type2 -> raise (Failure "List was terminated inappropriately.")
    end
  |Get (ind, mylist) -> begin
    match(typecheck ind env, typecheck mylist env ) with
      (TInt, TList (type1, _)) -> type1
      |_ -> raise (Failure "Get requires a list to work with.")
    end
  |Seq [a] -> typecheck a env
  |Seq (a::b) -> typecheck a env; typecheck (Seq b) env
  |App ((Fix lam),var) ->  begin
    match typecheck (Fix lam) env with
      TFunc(TFunc(from2,to2),TFunc(from1,to1))-> if subtype(typecheck var env)from2 && subtype from2 from1&&subtype to1 to2 
        then to1 
        else raise (Failure "Input to a lambda is of inappropriate type.")
      |_ -> raise (Failure "Typecheck failed, at an Application to a fix.")
    end
  |App (lam, var) -> begin
    match typecheck lam env  with
      TFunc(from1, to1)->if subtype(typecheck var env) from1 
        then to1
        else raise (Failure "Input to a lambda is of inappropriate type.")
      |_ -> raise (Failure "Application is done to a non-lambda.")
    end
  |Lam (t, s, b) -> (Hashtbl.replace env s t; TFunc(t,typecheck b env))
  |Fix (Lam (t, s, b)) -> typecheck (Lam (t, s, b)) env
  |Fix something -> raise (Failure "Typecheck for fix failed.")
  |Var st -> Hashtbl.find_exn env st
  |LetN (things,body) -> raise (Failure "TODO")
  |TL _ -> raise (Failure "TODO")
  |TR _ -> raise (Failure "TODO")
  |As (expr, ty) -> typecheck_as (expr, ty) env  
  |Case (expr, left, right) -> typecheck_case (expr,left,right) env
  |While (guard, body) -> if typecheck guard env = TBool
    then (typecheck body env; TUnit)
    else raise (Failure "Guard mus be boolean")
  |Lookup name -> Hashtbl.find_exn env name
  |Set (ty, name, expr) ->   if subtype (typecheck expr env)ty
    then match (Hashtbl.find env name) with
      Some ty1 -> if ty1 = ty 
        then TUnit  
        else raise (Failure "Attempt to change type of variable.")
      |_ -> Hashtbl.replace env name ty; TUnit
    else raise (Failure "Set has assignent of wrong type.")
  |Record fields -> TRecord (List.zip_exn(List.map fields fst)(List.map (List.map fields snd)(fun a -> typecheck a env)))
  |GetRec (str, (Record[(k,v)])) -> if k = str then typecheck v env else raise (Failure "Record doesn't possess the specified field." )
  |GetRec (str, (Record((k,v)::fields))) -> if k = str then typecheck v env  else typecheck (GetRec (str,Record fields)) env
  |_ -> invalid_arg "Not a valid expression."

and typecheck_case (expr, left, right) env = begin
  match typecheck expr env with
    TSum (l, r) -> (
      match (typecheck left env, typecheck right env) with
        (TFunc(a,b), TFunc(c,d)) -> (if subtype l a && subtype r c
          then common_type b d
          else raise (Failure "Typechecking failure for case lambda."))
        |_ -> raise (Failure "Case doesn't have two lambdas.")
      )
    |_-> raise (Failure "Case doesn't typecheck to sum.")
  end

and typecheck_as (expr, ty) env = match (expr,ty) with (* TODO DEBUG This code is suspicious *)
  (TL a,TSum (left, right))-> if subtype(typecheck a env)left
    then if left = right 
      then raise (Failure "Sums must be two different types. TL")
      else TSum (left, right)
    else raise (Failure "Typecheck of as failed. TL")
  |(TR b,TSum (left, right))-> if subtype(typecheck b env)right 
    then if left = right
      then raise (Failure "Sums must be two different types. TR")
      else TSum (left, right) 
    else raise (Failure "Typecheck of as failed. TR")
  |_ -> invalid_arg "typecheck_as"
;;


(*
subst :: string -> expr  ->      expr
           var     replacement   thingToSubThrough Done 
*)
let rec subst str rep body = match body with
  N a -> N a
  |F a -> F a
  |B a -> B a
  |C a -> C a
  |Unit -> Unit
  |Top -> Top
  |Bottom -> Bottom
  |Lookup name-> Lookup name
  |Var st->if(st=str) then rep else (Var st)
  |Add (arg1, arg2) -> Add ((subst str rep arg1),(subst str rep arg2))
  |Mul (arg1, arg2) -> Mul ((subst str rep arg1),(subst str rep arg2))
  |Sub (arg1, arg2) -> Sub ((subst str rep arg1),(subst str rep arg2))
  |And (arg1, arg2) -> And ((subst str rep arg1),(subst str rep arg2))
  |Or (arg1,arg2) -> Or ((subst str rep arg1),(subst str rep arg2))
  |Not arg1 -> Not (subst str rep arg1)
  |If (arg1, arg2, arg3) -> If ((subst str rep arg1),(subst str rep arg2),(subst str rep arg3))
  |Equal (arg1, arg2) -> Equal((subst str rep arg1),(subst str rep arg2))
  |Lam (t, st, b) -> if(st=str) then (Lam (t, st, b)) else Lam (t, st, (subst str rep b))
  |App (arg1, arg2) -> App ((subst str rep arg1),(subst str rep arg2))
  |Tuple a -> Tuple(List.map a (subst str rep))
  |Get (index, mylist) -> Get ((subst str rep index),(subst str rep mylist))
  |Tail a -> Tail(subst str rep a)
  |Head a -> Head(subst str rep a)
  |List (head, rest) -> List ((subst str rep head),(subst str rep rest))
  |Concat (a, b) -> List ((subst str rep a),(subst str rep b))
  |Fix expr-> Fix (subst str rep expr)
  |As (expr, ty)->As ((subst str rep expr),ty)
  |TL a->TL ( subst str rep a)
  |TR b->TR (subst str rep b)
  |Case (expr, left, right) -> Case (subst str rep expr,
                                     subst str rep left,
                                     subst str rep right)
  |Record fields -> Record (List.zip_exn(List.map fields fst)(List.map (List.map fields snd)(subst str rep)))
  |GetRec (str, record) -> GetRec (str, subst str rep record)
  |LetN (things, body)-> LetN ((List.zip_exn(List.map things fst)(List.map(List.map things snd)(subst str rep))), (subst str rep body) )
  |Seq a -> Seq (List.map a (subst str rep))
  |Set (ty, name, a) ->Set (ty, name, (subst str rep a))
  |While (guard, body) -> While ((subst str rep guard),(subst str rep body))

(*
  make_expr :: Val   ->expr
        result->input
  Inverts eval.
*)    
let rec make_expr v = match v with
  VB a -> B a
  |VN a -> N a
  |VTuple a -> Tuple (List.map a make_expr)
  |VLam lambda -> lambda
  |VList (a, b) -> List ((make_expr a),(make_expr b))
  |VRecord fields -> Record (List.zip_exn(List.map fields fst)(List.map (List.map fields snd)make_expr))
  |VUnit -> Unit
  |VC c -> C c
  |VF f -> F f
  |VL l -> TL (make_expr l)
  |VR r -> TR (make_expr r)
  |VTop -> Top
  |VBottom -> Bottom

(*
  eval ::expr -> env_type -> value
       input -> current_state -> result
*)
let rec eval expr state = match expr with
  N a -> VN a
  |F a -> VF a
  |C a -> VC a
  |Tuple a -> VTuple (List.map a (fun a -> eval a state))
  |B b -> VB b
  |Lam (t, str, body) -> VLam expr
  |List (a, b) -> VList (eval a state, eval b state)
  |Unit -> VUnit
  |Var _ -> raise (Failure "Can't evaluate variables")
  |Equal (a, b) -> VB(eval a state = eval b state) 
  |Record fields -> VRecord (List.zip_exn(List.map fields fst)(List.map (List.map fields snd)(fun a -> eval a state)))

(* Numerical Functions  *)

  |Mul (a, b) -> begin
    match (eval a state, eval b state) with
      (VN x, VN y) -> VN(x*y)
      |(VN x, VF y) -> VF ((Float.of_int x)*.y)
      |(VF x, VN y) -> VF(x*.(Float.of_int y))
      |(VF x, VF y) -> VF(x*.y)
      |_ -> invalid_arg "Invalid args for multiplication."
    end      
  |Add (a, b) -> begin
    match (eval a state, eval b state) with
      (VN x, VN y) -> VN(x+y)
      |(VN x, VF y) -> VF ((Float.of_int x)+.y)
      |(VF x, VN y) -> VF(x+.(Float.of_int y))
      |(VF x, VF y) -> VF(x+.y)
      |_ -> invalid_arg "Invalid args for addition."
    end
  |Sub (a, b) -> begin
    match (eval a state, eval b state) with
      (VN x, VN y) -> VN(x-y)
      |(VN x, VF y) -> VF ((Float.of_int x)-.y)
      |(VF x, VN y) -> VF(x-.(Float.of_int y))
      |(VF x, VF y) -> VF(x-.y)
      |_ -> invalid_arg "Invalid args for subtracton." 
    end
  |App (lam, var) -> begin
    match eval lam state with
      VLam(Lam (t, str, body)) -> eval (subst str var body) state
      |_ -> invalid_arg "Invalid args for application."
    end

(* Boolean Functions *)
  |If (condition, thenCase, elseCase) -> begin
    match eval condition state with
      VB true -> eval thenCase state 
      |VB false -> eval elseCase state
      |_ -> invalid_arg "Invalid condition for if."
    end
  |And (a, b) -> begin
    match (eval a state, eval b state) with
      (VB x, VB y) -> VB(x&&y)
      |something -> invalid_arg "Invalid args for and." 
    end
  |Or(a, b) -> begin
    match (eval a state, eval b state) with
      (VB x, VB y) -> VB(x||y)
      |_ -> invalid_arg "Invalid args for or."
    end     
  |Not a ->begin
    match eval a state with
      VB x -> VB(not x)
      |_ -> invalid_arg "Invalid arg for not."
    end 
(* List and pair functions *)
  |Concat (a, b) -> begin
    match a with
      Unit -> eval b state(* TODO Suspicious *)
      |List (head, rest) -> eval(List (head, (make_expr(eval(Concat (rest, b)) state)))) state
      |_ -> invalid_arg "Concat failed."
    end
  |Get (index, mylist) -> begin
    match eval index state with (* Get the indexth member of list. *)
      (VN num)->if(num<=0) 
        then invalid_arg "Index out of bounds."
        else if num = 1 
          then eval(Head mylist) state
          else eval(Get (N (num-1), make_expr(eval (Tail mylist) state))) state
      |_ -> invalid_arg "Not a number index"
    end
  |Head (List (a, _)) -> eval a state
  |Tail (List (_, b)) -> eval b state
  |GetRec (str, (Record [(k,v)])) -> if str = k then eval v state else invalid_arg "Key not found."
  |GetRec (str, (Record ((k,v)::record))) -> if str = k then eval v state else eval(GetRec (str, (Record record))) state
  |LetN ([(str,be)], body) -> eval (subst str be body) state
  |LetN (((str,be)::more), body) -> eval (LetN (more, (subst str be body))) state
  |Fix body -> eval (App (body, (Fix body))) state
  |As (expr, _) -> eval expr state 
  |TL a -> VL(eval a state)
  |TR a -> VR(eval a state)
  |Case (expr, left, right) -> begin
    match eval expr state with
      VL a -> eval(App (left, (make_expr a))) state
      |VR b -> eval(App (right,(make_expr b))) state
      |_ -> invalid_arg "Case of non-union."
    end
  |Seq [a] -> eval a state
  |(Seq (a::b)) -> eval a state;
    eval (Seq b) state
  |Set (_, name, a) -> Hashtbl.replace state name (eval a state); VUnit
  |Lookup name -> Hashtbl.find_exn state name
  |While (guard, body) -> begin
    match eval guard state with
      VB true -> eval body state;
                 eval(While (guard, body)) state
      |VB false -> VUnit
      |_-> invalid_arg "Loop guard non-bool."
    end
  |Top -> VTop
  |Bottom -> raise (Failure "Attempt to eval Bottom")
  |_ -> invalid_arg "Not a valid expression."

(*
  exec :: expr         -> Val
      thingToCheck -> What it returns
  Make sure the expr is typesafe and evaluate it if it is.
*)

let exec a = typecheck a (Hashtbl.create ~hashable:String.hashable ()); eval a (Hashtbl.create ~hashable:String.hashable ())

