open Core.Std;;
open Interpreter;;
(* Num tests *)
let n1 = Mul ((Add((N 2),(N 3))),(N 4))
let n2 = Add ((N 2),  (Mul ((N 3), (N 4))))
let n3 = Sub ((N 10),(N 9))
let n4 = N 123

(* List and Pair tests *)

let p1 = Mul (Tuple[N 2;N 2], Mul(Tuple[N 3;N 4], Tuple[N 3;N 4]))
let p1A = VTuple[VN 18;VN 32]
let p2A = VTuple[VB true;VB false]
let p3 = Equal(Tuple[N 2;N 2],Tuple[N 2;N 2])
let p4 = Equal(Tuple[N 2;N 2],Tuple[N 2;N 3])

(* Bool tests *)

let b1 = And (B true, B true)
let b2 = And (B false, B false)
let b3 = Or (b1, B false)
let b4 = Or (B false, B false)
let b5 = Or(B true,B false)
let b6 = And(B true,B false)
let b7 = Or(B false,B false)
let b8 = And(B true,B true)
let b9 = Not (B true)
let b10 = Not (B false)
let b11 = Equal(N 5,N 5)
let b12 = Equal(N 5,N 6)

(* Eval Func tests *)
let f1 = Lam (TInt,"x", (Mul (N 5,Var "x")))
let f1A = VLam(Lam (TInt,"x", (Mul (N 5,Var "x"))))
let f2 = App (f1, N 1)
let f3 = Lam (TInt,"x", Mul (N 5,Var "y"))
let f3A = VLam(Lam (TInt,"x",Mul (N 5,Var "y")))
let f4 = App (f3, N 1)(* Generates exception. *)
let f5 = Lam (TInt,"y",App (Lam (TInt,"x" ,Mul (Var "x",Var "y")),Var "y"))
let f5A = VLam(Lam (TInt, "y", (App (Lam (TInt,"x", Mul (Var "x",Var "y")),Var "y"))))
let f6 = App (f5, N 5)

(* Subst tests *)
let s1Q = subst ("x")(N 5) (Lam (TReal,"y",Mul (Var  "x",Var "y")))
let s1A = Lam (TReal,"y",Mul (N 5,Var "y"))
let s2Q = subst ("x")(N 5) (Lam (TReal,"y",(Mul (Var  "z",Var "y"))))
let s2A = Lam (TReal,"y",Mul (Var  "z",Var "y"))
let s3Q = subst ("x")(N 5) (Lam (TReal,"y",(Sub (Var  "z",Var "y"))))
let s3A = Lam (TReal,"y",Sub (Var  "z",Var "y"))
let s4Q = subst ("x")(N 5) (Mul (Var  "x",Var "x"))
let s4A = Mul (N 5,N 5)
let s5Q = subst ("y")(N 12) (If ((Equal (N 5,Var "y")),(Mul (Var "y",Var "y")),(Add (Var "y",Var "y"))))
let s5A = If(Equal (N 5,N 12),Mul (N 12,N 12),Add (N 12,N 12))
let s6Evaled = VTuple[VN 24;VN 64]
let s9 = subst ("x")(B true) (Not (Var  "x"))
let s9A = Not (B true)
let s10 = subst ("x")(N 3) (Get (Var "x",List (N 1,List (N 2,List (Var "x",Unit)))))
let s10A = Get (N 3,List (N 1,List (N 2,List (N 3,Unit))))
let s11 = subst ("x")(B true) (And (Var  "x",Var "x"))
let s11A = And(B true,B true)
let s12 = subst ("x")(N 1)(Tail (List (Var "x",List (N 1,Unit))))
let s12A = Tail (List (N 1,List (N 1,Unit)))
let s13 = subst ("x")(N 1)(List(N 5,List (Var "x",(Unit))))
let s13A = List(N 5,List (N 1,Unit))
let s14 = subst ("x")(N 1) (Head(List (N 1,List (N 2,List (Var "x",Unit)))))
let s14A = Head ((List (N 1,List (N 2,List (N 1,Unit)))))
let s15 = subst ("x")(B true) ((Or (Var  "x",Var "x")))
let s15A = Or(B true,B true)

(* kind tests that succeed. *)
let t1 = Lam (TBool, "x", If (Var "x",N 5,N 6))
let t2 = App (t1, B true)
let t3 = Lam (TInt, "y", Lam (TBool, "x", If (Var "x",Var "y",N 6)))
let t4 = And (B true,B true)
let t5 = Equal (Unit,B true)
let t6 = Concat(List (N 5,Unit),List (N 1,Unit))
let t8 = List(N 5,List (N 1,Unit))
let t9 = Lam (TList (TReal, 3), "x" ,Equal (Var "x",List (N 1,List (N 3,List (N 2,Unit)))))
let t10 = Get (N 3,List (N 1,List (N 2,List (N 3,Unit))))
let t11 = Tail (List (N 1,List (N 1,Unit)))
let t12 = List (F 1.5,List (N 2,List (N 3,Unit)))

(* expressions that return a value but fail typechecking. *)
let maybe1 = If(B true,N 4,B true) (*Mixing types in if statements.*)
let maybe2 = If(B false,N 4,B true) (*Mixing types in if statements. *)
let maybe3 = Concat(List (N 5,Unit),List (B true,Unit)) (* Mixing types in lists. *)
let maybe3Ans = VList (VN 5,VList (VB true,VUnit))
let maybe4 = App(Lam (TBool, "x", If (B true,N 5,N 6)),N 5) (* Input to lambda is of wrong type. *)
(*let maybe5 = Case(sum1,Lam (TReal, "x", Var "x"),Lam (TBool, "x", Var "x"))*)

(* expressions that crash AND fail typechecking. *)
let fail1 = If(N 5,N 4,N 3)
let fail2 = And (N 5,B true)
let fail3 = Case(N 5,N 4,N 3)

(* Record tests *)
let rec1 = Record[("age",N 18);("shoe-size",N 14)]
let rec1T = TRecord[("age",TInt);("shoe-size",TInt)]
let rec2 = GetRec ("shoe-size", rec1)
let rec3 = GetRec ("age", rec1)
let rec4 = Record[("age",N 18);("shoe-size",N 14);("numfeet",N 2)]
let rec4T = TRecord[("age",TInt);("shoe-size",TInt);("numfeet",TInt)]

(* SumTests *)
let sum1 = If(B true,As (TL (N 5),TSum (TInt, TBool)),As (TR (B true),TSum (TInt, TBool)))
let sum2 = If(B false,As (TL (N 5),TSum (TInt, TBool)),As (TR (B true),TSum (TInt, TBool)))
let case1 = Case(sum1,Lam (TReal, "x", Var "x"),Lam (TBool, "x", If(Var "x",N 4,N 3)))
let case2 = Case(sum2,Lam (TReal, "x", Var "x"),Lam (TBool, "x", If(Var "x",N 4,N 3)))
let sum2Point5 = If(Var "x",As (TL (If(Var "x",N 5,N 4)),TSum (TReal, TBool)),As (TR (Var "x"),TSum (TReal, TBool)))
let sum3 = Lam (TBool, "x", sum2Point5)
let sum4 = App (sum3, B true)
let sum5 = App (sum3, B false)
let case3 = Case(sum4,Lam (TReal, "x", Var "x"),Lam (TBool, "x", If(Var "x",N 4,N 3)))
let case4 = Case(sum5,Lam (TReal, "x", Var "x"),Lam (TBool, "x", If(Var "x",N 4,N 3)))

(* SeqTests *)
let while1 = While(B true,N 3)
let assign1 = Seq[Set (TInt, "x", N 1);Lookup "x"]
let assign2 = Seq[Set (TInt, "x", N 1);Set (TInt, "y", N 2);Lookup "x"]

(* FloatTests *)
let fl1 = Mul(F 3.4,N 3)
let fl2 = Mul(N 3,F 3.2)
let fl3 = Mul(F 3.4,F 3.2)
let fl4 = Add(F 3.4,N 3)
let fl5 = Add(N 3,F 3.2)
let fl6 = Add(F 3.4,F 3.2)
let fl7 = Sub(F 3.4,N 3)
let fl8 = Sub(N 3,F 3.2)
let fl9 = Sub(F 3.4,F 3.2)

(* Typing continued *)
let typ0000 = App(Lam (TFunc(TReal,TReal), "x", App(Var "x",N 3)),Lam (TReal, "y", Var "y"))(*Applying TReal->TReal to TReal->TReal. Succeeds*)
let typ0001 = App(Lam (TFunc(TReal,TInt),"x", App(Var "x",N 3)),Lam (TReal, "y", Var "y"))(*Applying TReal->TReal to TReal->TInt. Fails.*)
let typ0010 = App(Lam (TFunc(TInt,TReal), "x", App(Var "x",N 3)),Lam (TReal, "y",Mul (Var "y",F 3.0)))(*Applying TReal->TReal to TInt->TReal. Succeeds*)
let typ0011 = App(Lam (TFunc(TInt,TInt), "x", App(Var "x",N 3)),Lam (TReal, "y", Mul (Var "y",F 3.4)))(*Applying TReal->TReal to TInt->TInt. Fails.*)
let typ0100 = App(Lam (TFunc(TReal,TReal), "x", App(Var "x",N 3)),Lam (TReal, "y", N 3))(*Applying TReal->TInt to TReal->TReal. Succeeds*)
let typ0101 = App(Lam (TFunc(TReal,TInt), "x", App(Var "x",N 3)),Lam (TReal, "y", N 3))(*Applying TReal->TInt to TReal->TInt. Succeeds*)
let typ0110 = App(Lam (TFunc(TInt,TReal), "x", App(Var "x",N 3)),Lam (TReal, "y", N 3))(*Applying TInt->TReal to TReal->TInt. Fails*)
let typ0111 = App(Lam (TFunc(TInt,TInt), "x", App(Var "x",N 3)),Lam (TReal, "y", N 3))(*Applying TReal->TInt to TInt TInt. Succeeds.*)
let typ1000 = App(Lam (TFunc(TReal,TReal), "x", App(Var "x",N 3)),Lam (TInt, "y", Mul (Var "y",F 3.4)))(*Applying TInt->TReal to TR->TR*)
let typ1001 = App(Lam (TFunc(TReal,TInt), "x", App(Var "x",N 3)),Lam (TInt, "y", Mul (Var "y",F 3.4)))(*Applying TI->TR to TR->TI*)
let typ1010 = App(Lam (TFunc(TInt,TReal), "x", App(Var "x",N 3)),Lam (TInt, "y", Mul (Var "y",F 3.0)))(*Applying TInt->TReal to TInt->TReal. Succeeds*)
let typ1011 = App(Lam (TFunc(TInt,TInt), "x", App(Var "x",N 3)),Lam (TInt, "y", Mul (Var "y",F 3.4)))(*Applying TInt->TReal to TInt->TInt. Fails.*)
let typ1100 = App(Lam (TFunc(TReal,TReal), "x", App(Var "x",N 3)),Lam (TInt, "y", N 3))(*Applying TInt->TInt to TReal->TReal.Fails*)
let typ1101 = App(Lam (TFunc(TReal,TInt), "x", App(Var "x",N 3)),Lam (TInt, "y", N 3))(*Applying TI->TI to TR->TI. Fails*)
let typ1110 = App(Lam (TFunc(TInt,TReal), "x", App(Var "x",N 3)),Lam (TInt, "y", Var "y"))(*App TI->TI to TI->TR*)
let typ1111 = App(Lam (TFunc(TInt,TInt), "x", App(Var "x",N 3)),Lam (TInt, "y", Var "y"))

(* tests paired with their expected answers *)
let numTests = [(n1,VN 20);(n2,VN 14);(n3,VN 1);(n4,VN 123);(s4A,VN 25);
      (s5A,VN 24);(maybe1,(VN 4));(maybe2,(VB true));
      (maybe3,maybe3Ans);(maybe4,VN 5);(fl1,VF (3.4*.3.));(fl2,VF 9.6);(fl3,VF 10.88)
      ;(fl4,VF 6.4);(fl5,VF 6.2);(fl6,VF (3.4+.3.2));(fl7,VF (3.4-.3.));(fl8,VF (3.-.3.2));(fl9,VF (3.4-.3.2))]

let pairTests=[(p3,VB true);(p4,VB false)]

let boolTests=[(b1,VB true);(b2,VB false);(b3,VB true);(b4,VB false)
      ;(b5,VB true);(b6,VB false);(b7,VB false);(b8,VB true)
      ;(b9,VB false);(b10,VB true);(b11,VB true);(b12,VB false)
      ;(t5,VB false)]

let factorial = Fix (Lam (TFunc(TInt,TInt),"fac",Lam (TInt, "x", If (Equal (Var "x",N 1),N 1,Mul (Var "x",App(Var "fac",Sub (Var "x",N 1)))))))
let run=App (factorial, N 4)
let fibonacci=Lam (TInt, "limit", 
  (Seq[Set (TInt, "x0", N 0);
    Set (TInt, "x1", N 1);
    Set (TInt, "count", N 0);
    While(Not(Equal (Lookup "count",Var "limit")),
    (Seq [
      Set (TInt, "x0", Add(Lookup "x0",Lookup "x1"));
      Set (TInt, "x1", Sub(Lookup "x0",Lookup "x1"));
      Set (TInt, "count", Add(Lookup "count",N 1))
      ]));
    Lookup "x0"
  ]))     

let execTests=[(n1,VN 20);(n2,VN 14);(n3,VN 1);(n4,VN 123);(s4A,VN 25);
      (s5A,VN 24);(f1,f1A);(f2,VN 5);(f5,f5A)
      ;(f6,VN 25);(t4,VB true);(t5,VB false);(t6,(VList (VN 5,VList (VN 1,VUnit))))
      ;(t8,VList (VN 5,VList (VN 1,VUnit)))
      ;(t9, VLam (Lam (TList (TReal, 3), "x", Equal (Var "x",List (N 1,List (N 3,List (N 2,Unit)))))))
      ;(t10,VN 3);(t11,VList (VN 1,VUnit));(sum1,VL(VN 5));(sum2,VR(VB true));(case1,VN 5)](*;(case2,VN 4)
      ;(rec1,VRecord[("age",N 18);("shoe-size",N 14)]);(rec2,VN 14);(rec3,VN 18)
      ;(App (fibonacci, N 4),VN 3);(sum4,VL(VN 5));(sum5,VR(VB false));(case3,VN 5);(case4,VN 3)
      ;(s14A,VN 1);(Unit,VUnit)]*)
      
let funcTests=[(f1,f1A);(f2,VN 5);(f3,f3A);(f5,f5A);(f6,VN 25)]
    
let subTests=[(s1Q,s1A);(s2Q,s2A);(s3Q,s3A);(s4Q,s4A);(s5Q,s5A);(s9,s9A);
      (s10,s10A);(s11,s11A);(s12,s12A);(s13,s13A);(s14,s14A);(s15,s15A)]

let typeTests=[ (n1,TInt);(n2,TInt);(n3,TInt);(n4,TInt);(b1,TBool);
      (b2,TBool);(b3,TBool);(b4,TBool);(b5,TBool);(b6,TBool);
      (b7,TBool);(b8,TBool);(b9,TBool);(b10,TBool);(b11,TBool);
      (b12,TBool);(f1,TFunc(TInt,TInt));(f2,TInt);(t1,TFunc(TBool,TInt));
      (t2,TInt);(t3,TFunc(TInt,TFunc(TBool,TInt)));(t4,TBool);(Unit,TUnit);
      (t6,TList (TInt, 2));(t10,TInt);(t11,TList (TInt, 1));(sum1,TSum (TInt, TBool));
      (sum2,TSum (TInt, TBool));(case1,TReal);(case2,TReal);(factorial,TFunc(TFunc(TInt,TInt),TFunc(TInt,TInt)));
      (Tuple [N 3;N 2; B true],TTuple[TInt;TInt;TBool]);(run,TInt);
      (while1,TUnit);(assign1,TInt);(t12,TList (TReal, 3));(rec1,rec1T);(rec4,rec4T)]
      
let subtypeTests=[(TInt,TReal,true);(TReal,TReal,true);(TReal,TInt,false);(rec4T,rec1T,true);(rec1T,rec4T,false)
        ;(TTop,TBottom,false);(TBottom,TTop,true);(rec1T,rec4T,false)]

(* are tests paired up with their actual results? *)
let testResults = List.map numTests (fun(t,v) -> eval t (Hashtbl.create ~hashable:String.hashable ()) = v)
let pairTestResults = List.map pairTests (fun(t,v) -> exec t = v)
let boolTestResults = List.map boolTests (fun(t,v) -> exec t = v)
let funcTestResults = List.map funcTests (fun(t,v) -> eval t (Hashtbl.create ~hashable:String.hashable ()) = v)
let execTestResults = List.map execTests (fun(t,v) -> exec t = v)
let subTestResults  = List.map subTests (fun(t,v) -> t = v)
let typeTestResults = List.map typeTests (fun(t,v)-> typecheck t (Hashtbl.create ~hashable:String.hashable ()) = v)
let subtypeTestResults = List.map subtypeTests (fun(t,r,v)-> subtype t r = v)

let maybeWhile = Seq[Set (TInt, "cnt", N 0);
    While(Not(Equal (Lookup "cnt",N 2)),
    Seq [
      If(Equal (Lookup "cnt",N 1),Lookup "x",N 0);
      If(Equal (Lookup "cnt",N 0),Set (TInt, "x", N 0),Unit);
      Set (TInt, "cnt", Add(Lookup "cnt",N 1))
      ])  
      ]

let all mylist = List.for_all mylist (fun a -> a)

(* were all tests okay? *)
let okay = (all testResults) && (all boolTestResults) && (all subTestResults) &&  
           (all funcTestResults) && (all typeTestResults) && (all pairTestResults) &&
           (all execTestResults) && (all subtypeTestResults)

let main () = 
  print_endline("testResults passed=" ^ string_of_bool (all testResults));
  print_endline("boolTestResults passed=" ^ string_of_bool(all boolTestResults));
  print_endline("subTestResults passed=" ^ string_of_bool(all subTestResults));
  print_endline("funcTestResults passed=" ^ string_of_bool(all funcTestResults));
  print_endline("typeTestResults passed=" ^ string_of_bool(all typeTestResults));
  print_endline("pairTestResults passed=" ^ string_of_bool(all pairTestResults));
  print_endline("execTestResults passed=" ^ string_of_bool(all execTestResults));
  print_endline("subtypeTestResults passed=" ^ string_of_bool (all subtypeTestResults));
  print_endline("all passed=" ^ string_of_bool okay);;

main ()
