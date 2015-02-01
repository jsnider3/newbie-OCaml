DEPENDENCIES  
The Haskell code requires ghc, libghc-mtl-dev, and libghc-parallel-dev.
  The OCaml code requires the Jane Street core library. 

HOW TO RUN  
The Haskell interpreter is compiled with ghc Original.hs and run with ./Original.
The OCaml code is built with make and run as ./tests.

THE LANGUAGE  
Currently, "498" is a software artifact. It has ints, floats, booleans, states,
 structs, tagged unions, state, recursion, lambdas, and loops. It is at the end
 of the day, an ungodly mess of a language. This is not surprising given
it's history, the original Haskell was my independent study project back in 
undergrad. I partially refactored it at the end and then later when I had the urge.  

I will at the end of the translation into OCaml and subsequent refactoring, produce
a specification of the language defined by Interpreter.ml.
