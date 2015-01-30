#use "topfind"
#thread
#require "dynlink"
#camlp4o
#require "core"
#require "core_extended"
#require "core.top"
#require "batteries"
open Core.Std

type expr = N of int | F of float| Add of (expr * expr) | Mul of (expr * expr) | Sub of (expr * expr)
    |And of (expr * expr) | Or of (expr * expr) |Not of expr |If of (expr * expr * expr) |Equal of (expr * expr) | B of bool
    |Lam of (kind * string * expr) | App of (expr * expr) | Var of string |Tuple of expr list
    |List of (expr * expr) 
    |Unit | Done (* Remove and replace with Unit *)
    |Concat of (expr * expr) | Get of (expr * expr) | Head of expr | Tail of expr
    |Record of (string * expr) list | GetRec of (string * expr)
    |Fix of expr | LetN of ((string * expr) list * expr)  
    |TL of expr| TR of expr| Case of (expr * expr * expr) |As of (expr * kind) 
    |Seq of expr list |Set of (kind * string * expr) |Lookup of string |While of (expr * expr)
    |Top | Bottom
    |C of char

(* I would prefer to call kind "type", but that is very much not allowed in OCaml.*)
and kind = TInt | TReal | TBool | TChar | TFunc of (kind * kind) | TTuple of kind list | TyL of kind |
           TyR of kind | TList of (kind * int) | TRecord of (string * kind) list | TUnit | TSum of (kind * kind) | 
           TTop | TBottom | TStr

type value = VB of bool | VC of char | VTuple of value list | VList of (value * value) | VUnit | VL of value | VR of value | VDone|
             VN of int |VF of float| VLam of expr | VRecord of (string * expr) list | VTop | VBottom

type env_type = (string, value) Hashtbl.t;;
type type_map = (string, kind) Hashtbl.t;;

(*
  sub_type ::kind->kind->bool
*)
let rec subtype t1 t2 = match  (t1, t2) with
  (TInt, TReal) ->true
  |(TBottom, _) -> true
  |(_, TTop) -> true
  |((TRecord rec1),(TRecord rec2)) -> raise (Failure "Not yet implemented: Should be length(rec2 setminus rec1) = 0") 
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
  typecheck ::expr -> env_type -> kind
        suspicious expression -> lookup table -> type it returns
  Makes sure an expression uses types correctly and either returns 
  a value of a single type or returns an error.
*)      
(*typecheck ::expr->State TEnv kind --[(string,kind)]->([(string,kind)],kind)*)
let rec typecheck expr env = match expr with
  C _ -> TChar
  |N _ -> TInt
  |F _ -> TReal
  |B _ -> TBool
  |Unit -> TUnit
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
    else raise (Failure "If has non-bool condition")
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
  |Seq (a::b) -> typecheck a env
  |App ((Fix lam),var) ->  begin
    match typecheck (Fix lam) env with
      TFunc(TFunc(from2,to2),TFunc(from1,to1))-> if subtype(typecheck var env)from2 && subtype from2 from1&&subtype to1 to2 
        then to1 
        else raise (Failure "Input to a lambda is of inappropriate type.")
      |_ -> raise (Failure "Typecheck failed, at an Application to a fix.")
    end
  |App (lam, var) -> begin
    match typecheck lam env  with
      TFunc(from1, to1)->if subtype( typecheck var env) from1 
        then to1
        else raise (Failure "Input to a lambda is of inappropriate type.")
      |_ -> raise (Failure "Application is done to a non-lambda.")
    end
  |Lam (t, s, b) -> (Hashtbl.add env s t; TFunc(t,typecheck b env))
  |Fix (Lam (t, s, b)) -> typecheck (Lam (t, s, b)) env
  |Fix something -> raise (Failure "Typecheck for fix failed.")
  |Var st -> Hashtbl.find_exn env st
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
      |_ -> Hashtbl.add env name ty; TUnit
    else raise (Failure "Set has assignent of wrong type.")
  |Record fields -> TRecord (List.zip_exn(List.map fields fst)(List.map (List.map fields snd)(fun a -> typecheck a env)))
  |GetRec (str, (Record[(k,v)])) -> if k = str then typecheck v env else raise (Failure "Record doesn't possess the specified field." )
  |GetRec (str, (Record((k,v)::fields))) -> if k = str then typecheck v env  else typecheck (GetRec (str,Record fields)) env
  |_ -> raise (Failure "TODO Not yet implemented")

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
(*
  lookup_type ::string->TEnv->kind
  Searches the environment and returns the type of the variable specified.
*)
lookup_type ::string->State TEnv kind
lookup_type st  = do
  env<-get
  case Map.lookup st env of
    (Just x)->return x
    _->error $"Variable "++show st++" not found in environment."
(*
  purge_env::Env->expr->Env
  Removes the lambda variables from the environment when it's removed by an application.
*)
purge_env::expr->State TEnv Bool
purge_env(Lam t s b)=do
  env<-get
  put $Map.delete s env
  return True
purge_env (Fix b)= purge_env(b)
purge_env _=return False --error $"Attempt to purge something not part of an application. We have"++show thing
(*
  free::(string,kind)->TEnv->Bool
  Checks the environment to make sure that a given variable name is not already defined in the environment as having a different type. 
  I thought of making it crash if you declared a variable twice with the same type, but that would have been both problematic and picky.
*)
free::(string,kind)->State TEnv Bool
free(s,t)=do
  env<-get
  case Map.lookup s env of
    (Just ty)->return (t==ty)
    _->return True
    
  return True
  (*case env of
          []->return True
          (name,ty):rest->if(name==s&&not(t==ty))then return False else do{put rest;free(s,t)}
  *)
(*
  simplify_type ::kind -> kind
  Takes type and either returns TReal or TBool depending on the root.
*)
simplify_type ::kind -> kind
simplify_type(TInt)=TInt
simplify_type(TReal)=TReal
simplify_type(TBool)=TBool
simplify_type(TList ty _)=ty
simplify_type(TTuple (t1:t2))=case (simplify_type t1,simplify_type (TTuple t2)) of
              (TReal,TReal)->TReal
              (TReal,TNull)->TReal
              (TBool,TBool)->TBool
              (TBool,TNull)->TBool
              _->TNull
simplify_type(_)=TNull

(*
  exec :: expr         -> Val
      thingToCheck -> What it returns
  Make sure the expr is typesafe and if it evaluate it.
*)

exec ::expr ->Val
exec(a)= evalState(typecheck a)Map.empty `seq` (evalState(eval a )Map.empty)
*)
(*
subst :: string -> expr  ->      expr
           var     replacement   thingToSubThrough Done 
*)
let rec subst str rep body = match body with
  (N a) -> (N a)
  |(F a) -> (F a)
  |(B a) -> (B a)
  |(Unit) -> Unit
  |(Lookup name)-> Lookup name
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
  (* TODO |Tuple a -> Tuple(List.map(subst str rep) a)  *)
  |Get (index, mylist) -> Get ((subst str rep index),(subst str rep mylist))
  |Tail a -> Tail(subst str rep a)
  |Head a -> Head(subst str rep a)
  |List (head, rest) -> List ((subst str rep head),(subst str rep rest))
  |Fix expr-> Fix (subst str rep expr)
  |As (expr, ty)->As ((subst str rep expr),ty)
  |TL a->TL ( subst str rep a)
  |TR b->TR (subst str rep b)
  (* TODO |LetN things body-> LetN (zip(map fst things)(map(subst str rep)(map snd things))) (subst str rep body)  *)
  (* TODO |Seq a -> Seq (List.map (subst str rep) a) *)
  |Set (ty, name, a) ->Set (ty, name, (subst str rep a))
  |While (guard, body) -> While ((subst str rep guard),(subst str rep body))
  |_ ->raise(Failure "Invalid body for substitution.")
(*
  eval ::expr  ->Val
       input ->result
*)
(*
eval :: expr -> State Env Val

eval (N a) = return (VN a)
eval (F a) = return (VF a)
eval (C a) = return (VC a)
eval (Tuple a)=do
  env<-get
  return(VTuple (zipWith (evalState)(map eval a)(replicate (length a)env )))

eval (B b)=return(VB b)
eval (Lam t str body)=return(VLam (Lam t str body))
eval (List a b)=do
  env <-get
  first<-eval a
  s2nd<-eval b
  return (VList (first)(s2nd))
eval (Null)=return(VNull)
eval (Var _) = error "Can't evaluate variables."
eval (Equal a b)=do
  first<-eval a
  s2nd<-eval b
  return (VB(first==s2nd))
eval (Record fields)=return(VRecord fields)

--Numerical Functions 

eval (Mul a b) = do
  env <-get
  case (evalState(eval a) env,evalState(eval b)env) of
      (VN x, VN y) -> return(VN(x*y))
      (VN x, VF y) -> return(VF ((fromIntegral x)*y))
      (VF x, VN y) -> return(VF(x*(fromIntegral y)))
      (VF x, VF y) -> return(VF(x*y))
      something -> error $"Invalid args for multiplication. We have "++ show something++"."
          

eval (Add a b) = do
  env <-get
  case (evalState(eval a) env,evalState(eval b)env) of
      (VN x, VN y) -> return(VN(x+y))
      (VN x, VF y) -> return(VF ((fromIntegral x)+y))
      (VF x, VN y) -> return(VF(x+(fromIntegral y)))
      (VF x, VF y) -> return(VF(x+y))
      something -> error $"Invalid args for multiplication. We have "++ show something++"."
  
eval (Sub a b) = do
  env <-get
  case (evalState(eval a) env,evalState(eval b)env) of
      (VN x, VN y) -> return(VN(x-y))
      (VN x, VF y) -> return(VF ((fromIntegral x)-y))
      (VF x, VN y) -> return(VF(x-(fromIntegral y)))
      (VF x, VF y) -> return(VF(x-y))
      something -> error $"Invalid args for multiplication. We have "++ show something++"." 

eval (App lam var) = do
  env<-get
  case evalState(eval lam)env of
          (VLam(Lam t str body))-> eval ( subst str var body)
          something -> error $"Invalid args for application. We have "++ show something++" as our lambda."

--Boolean Functions         
eval(If condition thenCase elseCase)=do
  env<-get
  case evalState(eval condition)env of
          (VB True)->eval(thenCase) 
          (VB False)->eval(elseCase)
          something-> error $"Invalid condition for if. We have "++show something++"."

eval(And a b) = do
  env <-get
  case (evalState(eval a) env,evalState(eval b)env) of
      (VB x, VB y) -> return(VB(x&&y))
      something -> error $"Invalid args for multiplication. We have "++ show something++"." 
            
eval(Or a b)=do
  env <-get
  case (evalState(eval a) env,evalState(eval b)env) of
      (VB x, VB y) -> return(VB(x||y))
      something -> error $"Invalid args for multiplication. We have "++ show something++"."
            

eval(Not a)=do
  env <-get
  case(evalState(eval a) env) of
          (VB x)->return(VB(not x))
          (n)->error $"Attempt to not" ++show a 

--List and pair functions   
eval(Concat a b)=do
  env <-get
  case (a) of
            (Null) -> eval b
            (List head rest)->eval(List head (make_expr(evalState(eval(Concat rest b))env)))
            _ ->error $ "Concat failed. We have "++show (a,b)++"."
eval(Get index list)=do
  env <-get
  case evalState(eval index)env of --Get the indexth member of list.
            (VN num)->if(num<=0) then error "Index out of bounds."
                  else if num==1 
                    then eval(Head list) 
                    else eval(Get (N (num-1)) (make_expr(evalState(eval (Rest(list)))env)))
eval(Head (List a _))=eval a--Get the first element in list.
eval(Head (something))=eval something--I think this executing is a bug.
eval(Rest (List _ b))= eval b
eval(GetRec str (Record [(k,v)]))=if(str==k)then (eval v ) else error "Key not found."
eval(GetRec str (Record ((k,v):record)))=if(str==k)then eval v  else eval(GetRec str (Record record))
eval(LetN [(str,be)] body)=eval (subst str be body) 
eval(LetN ((str,be):more) body)=eval (LetN more (subst str be body)) 
eval(Fix body) =eval(App body (Fix body))--subst name (Fix name body) body)
eval(As expr _)=eval expr 
eval(TL a)=do
  env <-get
  return(VL(evalState(eval a)env))
eval(TR a)=do
  env <-get
  return(VR(evalState(eval a)env))
eval(Case expr left right)=do
  env <-get
  case evalState(eval expr)env of
              (VL a)->eval(App left (make_expr a))
              (VR b)->eval(App right(make_expr b))
              (thing)->error $"Case returned "++show thing++"."

eval(Seq [a])=  eval a
eval(Seq (a:b))=do
  env<-get
  put $execState(eval a)env
  eval (Seq b)
eval(Set _ name a)=do
  env<-get
  put $execState(set_helper(name,evalState(eval a)env))env
  return VDone
eval(Lookup str)=do
  env<-get
  return $evalState(lookup_state str)env
eval(While guard body)=do
  env<-get
  case evalState(eval guard)env of
                (VB True )->do
                      put $execState(eval body)env
                      eval(While guard body)
                (VB False)->return(VDone)
                _-> error$"Do while failure in false."
eval(Done) =return(VDone)
eval something = error $"No pattern to evaluate "++show something++"."

(*
  set_helper::(string,Val)->State Env Bool
  Redefines the value of a variable in the environment or gives it one if it was previously undefined.
*)  
set_helper::(string,Val)->State Env ()
set_helper (name,val) = do
  env<-get
  put$Map.insert name val env
(*
  lookup_state ::string->State Env Val
  Given the name of a variable either returns its value in the environment or crashes.
*)  
lookup_state ::string->State Env Val
lookup_state st  = do
  env<-get
  case Map.lookup st env of
    (Just x)->return x
    _->error $"Variable "++show st++" not found in environment."

(*
  make_expr :: Val   ->expr
        result->input
  Inverts eval.

*)    
make_expr :: Val -> expr 
make_expr(VB a)=(B a)
make_expr(VN a)=(N a)
make_expr(VTuple a)= Tuple (map make_expr a) 
make_expr(VLam (Lam t str body))=Lam t str body
make_expr(VList a b)=List (make_expr a)(make_expr b)
make_expr(VRecord stuff)=Record stuff
make_expr(VNull)=Null


(* Num tests *)
n1 = Mul (Add(N 2)(N 3))(N 4)
n2 = Add (N 2)  (Mul (N 3) (N 4))
n3 = Sub (N 10)(N 9)
n4 = N 123

(* List and Pair tests *)

(* p1 = Mul (Tuple[(N 2),(N 2)]) (Mul (Tuple[(N 3),(N 4)]) (Tuple[(N 3),(N 4)])) *)
p1A= VTuple[(VN 18),(VN 32)]
(* p2 = Or(Tuple[(B True),(B False)])(Tuple[(B False),(B False)]) *)
p2A= VTuple[(VB True),(VB False)]
p3 = Equal(Tuple[(N 2),(N 2)])(Tuple[(N 2),(N 2)])
p4 = Equal(Tuple[(N 2),(N 2)])(Tuple[(N 2),(N 3)])
(* p7 = Add (Tuple[(N 2),(N 2)]) (Add (Tuple[(N 3),(N 4)]) (Tuple[(N 3),(N 4)]))
   p8 = Sub (Tuple[(N 2),(N 2)]) (Sub (Tuple[(N 3),(N 4)]) (Tuple[(N 3),(N 4)]))
   p9 = Not(Tuple[B True, B False]) *)

(* Bool tests *)

b1= And (B True) (B True)
b2= And (B False) (B False)
b3= Or b1 (B False)
b4= Or (B False) (B False)
b5= Or(B True)(B False)
b6= And(B True)(B False)
b7= Or(B False)(B False)
b8= And(B True)(B True)
b9= Not (B True)
b10=Not (B False)
b11=Equal(N 5)(N 5)
b12=Equal(N 5)(N 6)

(* Eval Func tests *)
f1 = Lam (TInt)"x" (Mul (N 5)(Var "x"))
f1A=VLam(Lam (TInt)"x" (Mul (N 5)(Var "x")))
f2 = App f1 (N 1)
f3 = Lam (TInt)"x" (Mul (N 5)(Var "y"))
f3A= VLam(Lam (TInt)"x" (Mul (N 5)(Var "y")))
f4 = App f3 (N 1)(* Generates exception. *)
f5 = Lam (TInt)"y" (App (Lam (TInt) "x" (Mul (Var "x")(Var "y")))(Var "y"))
f5A = VLam(Lam (TInt) "y" (App (Lam (TInt)"x" (Mul (Var "x")(Var "y")))(Var "y")))
f6 = App f5 (N 5)

(* Subst tests *)
s1Q=subst ("x")(N 5) (Lam (TReal)"y"(Mul (Var  "x")(Var "y")))
s1A=(Lam (TReal)"y"(Mul (N 5)(Var "y")))
s2Q=subst ("x")(N 5) (Lam (TReal)"y"(Mul (Var  "z")(Var "y")))
s2A=(Lam (TReal)"y"(Mul (Var  "z")(Var "y")))
s3Q=subst ("x")(N 5) (Lam (TReal)"y"(Sub (Var  "z")(Var "y")))
s3A=(Lam (TReal)"y"(Sub (Var  "z")(Var "y")))
s4Q=subst ("x")(N 5) ((Mul (Var  "x")(Var "x")))
s4A=((Mul (N 5)(N 5)))
s5Q=subst ("y")(N 12) (If (Equal (N 5)(Var "y"))(Mul (Var "y")(Var "y"))(Add (Var "y")(Var "y")))
s5A = If(Equal (N 5)(N 12))(Mul (N 12)(N 12))(Add (N 12)(N 12))
(* s6Q= subst ("x")(N 4) (Mul (Tuple[(N 2),Var "x"]) (Mul (Tuple[Var "x",(N 4)]) (Tuple[(N 3),Var "x"]))) *)
(* s6A= Mul (Tuple [N 2,N 4]) (Mul (Tuple[N 4,N 4])(Tuple[N 3,N 4])) *)
s6Evaled=VTuple[VN 24,VN 64]
(* s7Q= subst ("x")(B True) (And (Tuple[(B True),Var "x"]) (And (Tuple[Var "x",(B False)]) (Tuple[(B True),Var "x"]))) *)
(* s7A= (And (Tuple[B True,B True]) (And (Tuple[B True,B False]) (Tuple[B True,B True]))) *)
(* s7Evaled=VTuple[VB True,VB False] *)
(* s8Q= subst ("x")(B True) (Or (Tuple[(B True),Var "x"]) (Or (Tuple[Var "x",(B False)]) (Tuple[(B True),Var "x"]))) *)
(* s8A= (Or (Tuple[B True,B True]) (Or (Tuple[B True,B False]) (Tuple[B True,B True]))) *)
(* s8Evaled=VTuple[VB True,VB True] *)
s9=subst ("x")(B True) ((Not (Var  "x")))
s9A=Not (B True)
s10 = subst ("x")(N 3) (Get (Var "x")(List (N 1) (List (N 2)(List (Var "x")(Null)))))
s10A= Get (N 3)(List (N 1) (List (N 2)(List (N 3)(Null))))
s11=subst ("x")(B True) ((And (Var  "x")(Var "x")))
s11A=((And(B True)(B True)))
s12 = subst ("x")(N 1)(Rest (List (Var "x") (List (N 1)(Null))))
s12A=Rest (List (N 1) (List (N 1)(Null)))
s13 = subst ("x")(N 1)(List(N 5)(List (Var "x")(Null)))
s13A = List(N 5)(List (N 1)(Null))
s14 = subst ("x")(N 1) $Head(List (N 1) (List (N 2)(List (Var "x")(Null))))
s14A=Head ((List (N 1) (List (N 2)(List (N 1)(Null)))))
s15=subst ("x")(B True) ((Or (Var  "x")(Var "x")))
s15A=((Or(B True)(B True)))

(* kind tests that succeed. *)
t1 = Lam TBool "x" (If (Var "x")(N 5)(N 6))
t2 = App t1 (B True)
t3 = Lam TInt "y" (Lam TBool "x" (If (Var "x")(Var "y")(N 6)))
t4 = And (B True)(B True)
t5 = Equal (Null)(B True)
t6 = Concat(List (N 5)(Null))(List (N 1)(Null))
t8 = List(N 5)(List (N 1)(Null))
t9 = Lam (TList TReal 3) "x" (Equal (Var "x")(List (N 1) (List (N 3)(List (N 2)(Null)))))
t10 = Get (N 3)(List (N 1) (List (N 2)(List (N 3)(Null))))
t11 = Rest (List (N 1) (List (N 1)(Null)))
t12 = (List (F 1.5) (List (N 2)(List (N 3)(Null))))
(*t12 = Mul t8 t8
  t13 = Add t8 t8
  t14 = Sub t8 t8
  t15 = List(B True)(List (B False)(Null))
  t16 = And t15 t15
  t17 = Not t15
  t18 = Or t15 t17 *)

(* expressions that return a value but fail typechecking. *)
maybe1 = If(B True)(N 4)(B True) (*Mixing types in if statements.*)
maybe2 = If(B False)(N 4)(B True) (*Mixing types in if statements. *)
maybe3 = Concat(List (N 5)(Null))(List (B True)(Null)) (* Mixing types in lists. *)
maybe3Ans= VList (VN 5)(VList (VB True)(VNull))
maybe4 =App(Lam TBool "x" (If (B True)(N 5)(N 6)))(N 5) (* Input to lambda is of wrong type. *)
maybe5=Case(sum1)(Lam TReal "x" (Var "x"))(Lam TBool "x" (Var "x"))

(* expressions that crash and fail typechecking. *)
fail1 = If(N 5)(N 4)(N 3)
fail2 = And (N 5)(B True)
fail3 = Case(N 5)(N 4)(N 3)

(* Record tests *)
rec1=Record[("age",N 18),("shoe-size",N 14)]
rec1T=TRecord[("age",TInt),("shoe-size",TInt)]
rec2=GetRec "shoe-size" rec1
rec3=GetRec "age" rec1
rec4=Record[("age",N 18),("shoe-size",N 14),("numfeet",N 2)]
rec4T=TRecord[("age",TInt),("shoe-size",TInt),("numfeet",TInt)]

(* SumTests *)
sum1=If(B True)(As (TL (N 5))(TSum TInt TBool))(As (TR (B True))(TSum TInt TBool))
sum2=If(B False)(As (TL (N 5))(TSum TInt TBool))(As (TR (B True))(TSum TInt TBool))
case1=Case(sum1)(Lam TReal "x" (Var "x"))(Lam TBool "x" (If(Var "x")(N 4)(N 3)))
case2=Case(sum2)(Lam TReal "x" (Var "x"))(Lam TBool "x" (If(Var "x")(N 4)(N 3)))
sum2Point5=(If(Var "x")(As (TL (If(Var "x")(N 5)(N 4)))(TSum TReal TBool))(As (TR (Var "x"))(TSum TReal TBool)))
sum3=Lam TBool "x" sum2Point5
sum4=App sum3 (B True)
sum5=App sum3 (B False)
case3=Case(sum4)(Lam TReal "x" (Var "x"))(Lam TBool "x" (If(Var "x")(N 4)(N 3)))
case4=Case(sum5)(Lam TReal "x" (Var "x"))(Lam TBool "x" (If(Var "x")(N 4)(N 3)))

(* SeqTests *)
while1=While(B True)(N 3)
assign1=Seq[Set TInt "x" (N 1),Lookup "x"]
assign2=Seq[Set TInt "x" (N 1),Set TInt "y" (N 2),Lookup "x"]

(* FloatTests *)
fl1=Mul(F 3.4)(N 3)
fl2=Mul(N 3)(F 3.2)
fl3=Mul(F 3.4)(F 3.2)
fl4=Add(F 3.4)(N 3)
fl5=Add(N 3)(F 3.2)
fl6=Add(F 3.4)(F 3.2)
fl7=Sub(F 3.4)(N 3)
fl8=Sub(N 3)(F 3.2)
fl9=Sub(F 3.4)(F 3.2)

(* Typing continued *)
typ0000=App(Lam (TReal:->TReal) "x" (App(Var "x")(N 3)))(Lam TReal "y" (Var "y"))--Applying TReal->TReal to TReal->TReal. Succeeds
typ0001=App(Lam (TReal:->TInt) "x" (App(Var "x")(N 3)))(Lam TReal "y" (Var "y"))--Applying TReal->TReal to TReal->TInt. Fails.
typ0010=App(Lam (TInt:->TReal) "x" (App(Var "x")(N 3)))(Lam TReal "y" (Mul (Var "y")(F 3)))--Applying TReal->TReal to TInt->TReal. Succeeds
typ0011=App(Lam (TInt:->TInt) "x" (App(Var "x")(N 3)))(Lam TReal "y" (Mul (Var "y")(F 3.4)))--Applying TReal->TReal to TInt->TInt. Fails.
typ0100=App(Lam (TReal:->TReal) "x" (App(Var "x")(N 3)))(Lam TReal "y" ((N 3)))--Applying TReal->TInt to TReal->TReal. Succeeds
typ0101=App(Lam (TReal:->TInt) "x" (App(Var "x")(N 3)))(Lam TReal "y" ((N 3)))--Applying TReal->TInt to TReal->TInt. Succeeds
typ0110=App(Lam (TInt:->TReal) "x" (App(Var "x")(N 3)))(Lam TReal "y" ((N 3)))--Applying TInt->TReal to TReal->TInt. Fails
typ0111=App(Lam (TInt:->TInt) "x" (App(Var "x")(N 3)))(Lam TReal "y" (N 3))--Applying TReal->TInt to TInt TInt. Succeeds.
typ1000=App(Lam (TReal:->TReal) "x" (App(Var "x")(N 3)))(Lam TInt "y" (Mul (Var "y")(F 3.4)))--Applying TInt->TReal to TR->TR
typ1001=App(Lam (TReal:->TInt) "x" (App(Var "x")(N 3)))(Lam TInt "y" (Mul (Var "y")(F 3.4)))--Applying TI->TR to TR->TI
typ1010=App(Lam (TInt:->TReal) "x" (App(Var "x")(N 3)))(Lam TInt "y" (Mul (Var "y")(F 3)))--Applying TInt->TReal to TInt->TReal. Succeeds
typ1011=App(Lam (TInt:->TInt) "x" (App(Var "x")(N 3)))(Lam TInt "y" (Mul (Var "y")(F 3.4)))--Applying TInt->TReal to TInt->TInt. Fails.
typ1100=App(Lam (TReal:->TReal) "x" (App(Var "x")(N 3)))(Lam TInt "y" (N 3))--Applying TInt->TInt to TReal->TReal.Fails
typ1101=App(Lam (TReal:->TInt) "x" (App(Var "x")(N 3)))(Lam TInt "y" (N 3))--Applying TI->TI to TR->TI. Fails
typ1110=App(Lam (TInt:->TReal) "x" (App(Var "x")(N 3)))(Lam TInt "y" ((Var "y")))--App TI->TI to TI->TR
typ1111=App(Lam (TInt:->TInt) "x" (App(Var "x")(N 3)))(Lam TInt "y" ((Var "y")))

(* tests paired with their expected answers *)
numTests = [(n1,VN 20),(n2,VN 14),(n3,VN 1),(n4,VN 123) ,(s4A,VN 25),
      (s5A,VN 24),(maybe1,(VN 4)),(maybe2,(VB True)), --(s6A,s6Evaled),
      (maybe3,maybe3Ans),(maybe4,VN 5),(fl1,VF (3.4*3)),(fl2,VF 9.6),(fl3,VF 10.88)
      ,(fl4,VF 6.4),(fl5,VF 6.2),(fl6,VF (3.4+3.2)),(fl7,VF (3.4-3)),(fl8,VF (3-3.2)),(fl9,VF (3.4-3.2))]

pairTests=[(p3,VB True),(p4,VB False)]--(p1,p1A),(p2,p2A),

boolTests=[(b1,VB True),(b2,VB False),(b3,VB True),(b4,VB False)
      ,(b5,VB True),(b6,VB False),(b7,VB False),(b8,VB True)
      ,(b9,VB False),(b10,VB True),(b11,VB True),(b12,VB False)
      ,(t5,VB False)]
      
execTests=[(n1,VN 20),(n2,VN 14),(n3,VN 1),(n4,VN 123),(s4A,VN 25),
      (s5A,VN 24) -- ,(s6A,s6Evaled)
      ,(f1,f1A),(f2,VN 5),(f5,f5A)
      ,(f6,VN 25),(t4,VB True),(t5,VB False),(t6,(VList (VN 5)(VList (VN 1)(VNull))))
      ,(t8,VList (VN 5)(VList (VN 1)(VNull)))
      ,(t9, VLam (Lam (TList TReal 3) "x" (Equal (Var "x")(List (N 1) (List (N 3)(List (N 2)(Null)))))))
      ,(t10,VN 3),(t11,VList (VN 1)(VNull))--,(t12,VList (VN 25)(VList (VN 1)(VNull))),(t13,VList (VN 10)(VList (VN 2)(VNull)))
      --,(t14,VList (VN 0)(VList (VN 0)(VNull))),(t15,VList (VB True)(VList (VB False)(VNull)))
      --,(t16,VList (VB True)(VList (VB False)(VNull))),(t17,VList (VB False)(VList (VB True)(VNull))),(t18,VList (VB True)(VList (VB True)(VNull)))
      --,(p7,VTuple[VN 8,VN 10]),(p8,VTuple[VN 2,VN 2]) --,(s7A,VTuple[VB True,VB False])
      ,(sum1,VL(VN 5)),(sum2,VR(VB True)),(case1,VN 5),(case2,VN 4),(rec1,VRecord[("age",N 18),("shoe-size",N 14)])
      ,(rec2,VN 14),(rec3,VN 18),(App fibonacci (N 4),VN 3),(sum4,VL(VN 5)),(sum5,VR(VB False)),(case3,VN 5),(case4,VN 3)
      ,(s14A,VN 1),(Done,VDone)]--,(s15A,VN 6)] --(s8A,s8Evaled),(p9,VTuple[VB False,VB True]),
      
funcTests=[(f1,f1A),(f2,VN 5),(f3,f3A),(f5,f5A)
      ,(f6,VN 25)]
    
subTests=[(s1Q,s1A),(s2Q,s2A),(s3Q,s3A),(s4Q,s4A),(s5Q,s5A), --(s6Q,s6A),(s7Q,s7A),(s8Q,s8A),
       (s9,s9A),(s10,s10A),(s11,s11A),(s12,s12A),(s13,s13A),(s14,s14A),(s15,s15A)]

typeTests=[ (n1,TInt),(n2,TInt),(n3,TInt),(n4,TInt),(b1,TBool),
      (b2,TBool),(b3,TBool),(b4,TBool),(b5,TBool),(b6,TBool),
      (b7,TBool),(b8,TBool),(b9,TBool),(b10,TBool),(b11,TBool),
      (b12,TBool),(f1,TInt :-> TInt),(f2,TInt),(t1,TBool :-> TInt),
      (t2,TInt),(t3,TInt :-> (TBool :-> TInt)),(t4,TBool),(Null,TNull),
      (t6,TList TInt 2),(t10,TInt),(t11,TList TInt 1),(sum1,TSum TInt TBool), --(s7A,TTuple [TBool,TBool]),
      (sum2,TSum TInt TBool),(case1,TReal),(case2,TReal),(factorial,(TInt :->TInt):->(TInt:->TInt)),
      (Tuple [N 3,N 2, B True],TTuple[TInt,TInt,TBool]),(run,TInt),
      (while1,TDone),(assign1,TInt),(t12,TList TReal 3),(rec1,rec1T),(rec4,rec4T)]
      
subtypeTests=[(TInt,TReal,True),(TReal,TReal,True),(TReal,TInt,False),(rec4T,rec1T,True),(rec1T,rec4T,False)
        ,(TTop,TBottom,False),(TBottom,TTop,True),(rec1T,rec4T,False)]

(* are tests paired up with their actual results? *)
testResults = map (\(t,v)-> evalState(eval t)Map.empty==v) numTests
(* fst and snd *)
pairTestResults = map (\(t,v)-> exec t==v) pairTests
boolTestResults = map (\(t,v)-> exec t==v) boolTests
funcTestResults = map (\(t,v)-> exec t==v) funcTests
execTestResults = map (\(t,v)-> exec t==v) execTests
subTestResults  = map (\(t,v)-> t==v) subTests
typeTestResults = map (\(t,v)-> evalState(typecheck t)Map.empty==v) typeTests
subtypeTestResults = map (\(t,r,v)-> subtype t r==v) subtypeTests


factorial = Fix (Lam (TInt :-> TInt)"fac"(Lam TInt "x" ((If (Equal (Var "x")(N 1))(N 1)(Mul (Var "x")(App((Var "fac")) (Sub (Var "x") (N 1))))))) )
run=App factorial (N 4)
fibonacci=Lam (TInt) "limit" 
  (Seq[Set TInt "x0" (N 0),
    Set TInt "x1" (N 1),
    Set TInt "count" (N 0),
    While(Not(Equal (Lookup "count")(Var "limit")))
    (Seq [
      Set TInt "x0"(Add(Lookup "x0")(Lookup "x1")),
      Set TInt "x1"(Sub(Lookup "x0")(Lookup "x1")),
      Set TInt "count" (Add(Lookup "count")(N 1))
      ]),
    Lookup "x0"
  ])
  
maybeWhile=Seq[Set TInt "cnt" (N 0) ,
    While(Not(Equal (Lookup "cnt")(N 2)))
    (Seq [
      If(Equal (Lookup "cnt")(N 1)) (Lookup "x")(N 0),
      If(Equal (Lookup "cnt")(N 0)) (Set TInt "x" (N 0))(Done),
      Set TInt "cnt" (Add(Lookup "cnt")(N 1))
      ])  
      ]
(* were all tests okay? *)
okay = (and testResults)&&(and boolTestResults)  &&  (and subTestResults)  &&  (and funcTestResults)  && (and typeTestResults)  &&(and pairTestResults) &&(and execTestResults)&&(and subtypeTestResults)

main = do
  putStrLn("testResults passed=" ++show (and testResults))
  putStrLn("boolTestResults passed=" ++show (and boolTestResults))
  putStrLn("subTestResults passed=" ++show (and subTestResults))
  putStrLn("funcTestResults passed=" ++show (and funcTestResults))
  putStrLn("typeTestResults passed=" ++show (and typeTestResults))
  putStrLn("pairTestResults passed=" ++show (and pairTestResults))
  putStrLn("execTestResults passed=" ++show (and execTestResults))
  putStrLn("subtypeTestResults passed=" ++show (and subtypeTestResults))
  putStrLn("all passed=" ++show okay)
*)
