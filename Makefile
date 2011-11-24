.PHONY: all clean graph doc

USE_OCAMLFIND := $(shell if `which ocamlfind > /dev/null`; then echo "-use-ocamlfind"; fi)
OCAMLBUILD := ocamlbuild $(USE_OCAMLFIND) -classic-display -use-menhir \
  -menhir "menhir --explain --infer -la 1" \
  -cflags "-g" -lflags "-g"
INCLUDE    := -Is sets,typing,parsing,ulex,lib 
MAIN	   := hamlet
TEST	   := test
BUILDDIRS  := $(shell gfind _build -maxdepth 1 -type d -printf "-I _build/%f ")
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
	   $(shell find $(MY_DIRS) -iname '*.ml' -or -iname '*.mli')\
	   hamlet.ml\
	   -o graph.dot
	dot -Tpng graph.dot > misc/graph.png
	convert misc/graph.png -rotate 90 misc/graph.png
	rm -f graph.dot

doc: graph
	ocamldoc -html $(BUILDDIRS) \
	  -I `ocamlc -where` -d doc \
	  -intro doc/main \
	  $(shell find _build -maxdepth 2 -iname '*.mli')
	sed -i 's/iso-8859-1/utf-8/g' doc/*.html
	sed -i 's/<\/body>/<img src="..\/misc\/graph.png" \/><\/body>/' doc/index.html
	cp -f misc/ocamlstyle.css doc/style.css
