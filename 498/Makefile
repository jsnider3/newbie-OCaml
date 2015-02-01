all: tests
	@true

tests: Interpreter.cmx tests.ml
	ocamlfind ocamlopt -g -o tests -linkpkg -package core -package core_kernel -thread -w -10 Interpreter.cmx tests.ml

Interpreter.cmx: Interpreter.ml Interpreter.cmi
	ocamlfind ocamlopt -g -c -package core -package core_kernel -thread -w -10 Interpreter.ml

Interpreter.cmi: Interpreter.mli
	ocamlfind ocamlopt -g -c -package core -package core_kernel -thread -w -10 Interpreter.mli

Interpreter.mli: Interpreter.ml
	ocamlfind ocamlc -i -package core -package core_kernel -thread -w -10 Interpreter.ml > Interpreter.mli

clean:
	rm *.cmx *.cmi *.o tests

