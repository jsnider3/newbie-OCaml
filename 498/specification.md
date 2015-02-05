# 498 Specification
### By Josh Snider


##Types
The types available in 498 are: TInt, TReal, TBool, TChar, TTuple, TSum, TyL, TyR, TTop, 
TBottom, TUnit, TList, TRecord, and TFunc.

###TInt
TInt represents the natural numbers and is analogous to the int type in python, java, and C++. Values of this type can 
be created with (N #) where the #-sign is replaced with the actual int. TInt is a subtype of TReal  

###TReal
TInt represents the real numbers and is analogous to the float type in python, java, and C++. Values of this type can 
be created with (F #) where the #-sign is replaced with the actual number.

####Addition, Subtraction, and Multiplication
Numbers can be adding, subtracting, and multiplied with each other. Expressions to do this take the form of 
Add(x,y), Mul(x,y), and Sub(x,y) with x and y being expressions that evaluate to either TInt or TReal. These functions
return a value of TInt if both arguments are members of TInt and a value of TReal otherwise.

###TChar
Values of TChar can be created with (C c) where c is any char enclosed in single quotes. There are no useful functions for
working with TChars.

###TTuple
TTuple represents a tuple. It can be of any arity and have members of any type. There are no useful functions for working with
TTuples, but a TTuple is evaluated and typechecked as if each member was an independent expression. They are declared with the 
form Tuple [a;b;c;d;...] with a, b, c, and d being any expressions.

###TSum, TyL, and TyR
TSum represents a tagged union of two types. TyL represents a value of the first type and is created as (L a) where a is a
value of any type. TyR represents a value of the second type and is created as (R a) where a is a value of any type. The function
As(val, type) should be used to convert a TyL or TyR into a TSum in order for typechecking to work properly. TSums are 
prohibited from having both types being the same. The function Case(expr, left, right) can be used to take an expression as 
its first argument, and then apply it to one of two lambdas. It is applied to the second argument of case if it's a TyL
and the third argument of Case if it's a TyR. The first and second lambdas for case must take the types wrapped by TyL and 
TyR as their arguments respectively.

###TTop
TTop is the top type. Its main value is to be the type of any expression that may return values of types that would not
otherwise be subtypes of each other. It can be declared with Top, if desired.  There are no useful built-in functions
that take arguments of type TTop.

###TBottom
TBottom is the bottom type and is a subtype of all other types and has no subtypes besides itself. It can be declared with
Bottom, if desired. Any attempt to evaluate a Bottom will result in an error.

###TUnit
TUnit is the unit type. It has one value, which is Unit. Its main use is as the return type of Set and While.

###TList

A TList is similar to a list in lisp. A list has a fixed type and a length. A list is represented as a pair, where the
first element is a value of the list's type and the second is either Unit (signifying the end of the list) or a list of the same
type and with length one less. There are no lists of length 0. Lists have a number of useful functions that operate on them.
Head takes a single list as an argument and returns the first element of it. Tail takes a single list and returns the second 
element. Tail's return type is either of type TUnit or TList 'a (len-1), which is known at typechecking. Concat takes two lists
and returns a single list whose elements are the first list in order, followed by the secon list in order. Get takes a TInt i and a
list and returns the ith number in the list, for some reason this is 1-indexed.

###TRecord
TRecord is equivalent to a python dictionary. It consists of a number of strings paired with expressions. GetRec can be used
to lookup an expression from a TRecord with its correspondings string. Strings must be unique, expressions they map to not at all.
A record a is a subtype of another record b, if all of the key's in b are present in a and have the same type.
 
###TFunc
TFunc(a,b) represents a function from a to b. It is declared as Lam(t,s,e) where t is the a type, s is a string representing
the variable name, and e is an expression. App(f,v) can be used to replace all occurences of (Var s) in the Lam's e with v. 
Fix b can be used to make recursion, and is evaluated the same as App (body, (Fix body)) is.

##Control Flow Constructs
###If
If expressions behave in the obvious way, if their first argument is true then they evaluate to their second argument. Else,
they evaluate to their third argument.

###While
While is also straightforward. If it's first arguent is true it evaluates it's body and loops. It returns Unit.

###Sequences
Seq[a;b;c;...] is a sequence, each element is evaluated and it's final value is the value of the final expression. 
Empty sequences are not allowed.

##Lookup and Set
Set(k,s,e) allows you to save the value of e in the current state as a variable named s of type k. It's an error if e is not
of type k. Lookup s returns whatever value was most recently saved in the variable s. Calling Lookup on an undefined variable
is an error.
