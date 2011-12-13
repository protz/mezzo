.PHONY: all clean graph doc

# The variables below should be determined by a configure script...
FIND       := find
-include Makefile.local

USE_OCAMLFIND := $(shell if `which ocamlfind > /dev/null`; then echo "-use-ocamlfind"; fi)
OCAMLBUILD := ocamlbuild $(USE_OCAMLFIND) -classic-display -use-menhir \
  -menhir "menhir --explain --infer -la 1" \
  -cflags "-g" -lflags "-g"
INCLUDE    := -Is sets,typing,parsing,ulex,lib,pprint
MAIN	   := hamlet
TEST	   := test
BUILDDIRS  := $(shell $(FIND) _build -maxdepth 1 -type d -printf "-I _build/%f ")
MY_DIRS	   := lib parsing sets typing


all:
	$(OCAMLBUILD) $(INCLUDE) $(MAIN).native $(TEST).native
	ln -sf $(MAIN).native $(MAIN)
	ln -sf $(TEST).native $(TEST)

clean:
	rm -f *~ $(MAIN) $(MAIN).native $(TEST) $(TEST).native
	$(OCAMLBUILD) -clean

graph: all
	ocamldoc -dot $(BUILDDIRS)\
	   -I $(shell ocamlbuild -where)\
	   -I $(shell ocamlc -where)\
	   $(shell menhir --suggest-comp-flags --table)\
	   $(shell $(FIND) $(MY_DIRS) -iname '*.ml' -or -iname '*.mli')\
	   hamlet.ml\
	   -o graph.dot
	sed -i 's/rotate=90;//g' graph.dot
	dot -Tsvg graph.dot > misc/graph.svg
	rm -f graph.dot

doc: graph
	ocamldoc -html $(BUILDDIRS) \
	  -I `ocamlc -where` -d doc \
	  -intro doc/main \
	  $(shell $(FIND) _build -maxdepth 2 -iname '*.mli')
	sed -i 's/iso-8859-1/utf-8/g' doc/*.html
	sed -i 's/<\/body>/<p align="center"><img src="..\/misc\/graph.svg" \/><\/p><\/body>/' doc/index.html
	cp -f misc/ocamlstyle.css doc/style.css

test: all
	OCAMLRUNPARAM=b=1 ./hamlet -debug tests/basic.hml
