all: 498
	@true

498: Interpreter.cmx
	ocamlfind ocamlopt -o 498 -linkpkg -package core -package core_kernel -thread -w -10 Interpreter.cmx

Interpreter.cmx: Interpreter.ml Interpreter.cmi
	ocamlfind ocamlopt -c -package core -package core_kernel -thread -w -10 Interpreter.ml

Interpreter.cmi: Interpreter.mli
	ocamlfind ocamlopt -c -package core -package core_kernel -thread -w -10 Interpreter.mli

Interpreter.mli: Interpreter.ml
	ocamlfind ocamlc -i -package core -package core_kernel -thread -w -10 Interpreter.ml > Interpreter.mli

clean:
	rm *.cmx *.cmi *.o 498

