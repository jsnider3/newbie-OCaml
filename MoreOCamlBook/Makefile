FILE=C11Sets

all: a.out
	@(a.out && echo "Tests passed") || true

a.out: ${FILE}.cmx
	@ocamlfind ocamlopt -g -linkpkg -package core -package core_kernel -thread -w -10 ${FILE}.cmx
	@echo "Linking executable"

${FILE}.cmx: ${FILE}.ml ${FILE}.cmi
	@ocamlfind ocamlopt -g -c ${FILE}.cmx -package core -package core_kernel -thread -w -10 ${FILE}.ml
	@echo "Compiling object code"

${FILE}.cmi: ${FILE}.mli
	@ocamlfind ocamlopt -g -c -package core -package core_kernel -thread -w -10 ${FILE}.mli
	@echo "Compiling interface"

${FILE}.mli: ${FILE}.ml
	@ocamlfind ocamlc -i -package core -package core_kernel -thread -w -10 ${FILE}.ml > ${FILE}.mli
	@echo "Making header"

clean:
	@rm a.out *.mli *.cmx *.cmi *.o tests 2>/dev/null || true
	@echo "Cleaning"

