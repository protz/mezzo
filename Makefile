.PHONY: all clean graph doc index

# The variables below should be determined by a configure script...
FIND       := find
-include Makefile.local

USE_OCAMLFIND := $(shell if `which ocamlfind > /dev/null`; then echo "-use-ocamlfind"; fi)
OCAMLBUILD := ocamlbuild $(USE_OCAMLFIND) -use-menhir \
  -menhir "menhir --explain --infer -la 1" \
  -cflags "-g" -lflags "-g" -classic-display
INCLUDE    := -Is sets,typing,parsing,ulex,lib,pprint,utils,fix
MAIN	   := mezzo
TESTSUITE  := testsuite
BUILDDIRS  := $(shell $(FIND) _build -maxdepth 1 -type d -printf "-I _build/%f ")
MY_DIRS	   := lib parsing sets typing utils


all:
	$(OCAMLBUILD) $(INCLUDE) $(MAIN).byte $(TESTSUITE).byte
	ln -sf $(MAIN).byte $(MAIN)
	ln -sf $(TESTSUITE).byte $(TESTSUITE)

clean:
	rm -f *~ $(MAIN) $(MAIN).native $(TEST) $(TEST).native $(TESTSUITE) $(TESTSUITE).native
	$(OCAMLBUILD) -clean

graph: all
	-ocamlfind ocamldoc -dot $(BUILDDIRS)\
	   -I $(shell ocamlbuild -where)\
	   -I $(shell ocamlc -where)\
	   $(shell menhir --suggest-comp-flags --table)\
	   $(shell $(FIND) $(MY_DIRS) -iname '*.ml' -or -iname '*.mli')\
	   mezzo.ml\
	   -o graph.dot
	sed -i 's/rotate=90;//g' graph.dot
	dot -Tsvg graph.dot > misc/graph.svg
	sed -i 's/^<text\([^>]\+\)>\([^<]\+\)/<text\1><a xlink:href="..\/doc\/\2.html" target="_parent">\2<\/a>/' misc/graph.svg
	sed -i 's/Times Roman,serif/DejaVu Sans, Helvetica, sans/g' misc/graph.svg
	rm -f graph.dot

doc: graph
	ocamldoc -html $(BUILDDIRS) \
	  -I `ocamlc -where` -d doc \
	  -intro doc/main \
	  $(shell $(FIND) _build -maxdepth 2 -iname '*.mli')
	sed -i 's/iso-8859-1/utf-8/g' doc/*.html
	sed -i 's/<\/body>/<p align="center"><object type="image\/svg+xml" data="..\/misc\/graph.svg"><\/object><\/p><\/body>/' doc/index.html
	cp -f misc/ocamlstyle.css doc/style.css

test: all
	OCAMLRUNPARAM=b ./testsuite

tags:
	otags $(shell $(FIND) $(MY_DIRS) -iname '*.ml' -or -iname '*.mli')

# Hacky target to build a specific file with all the right ocamlbuild flags. Say
# you want to compile foo.ml, do: FILE=foo.ml make build-one
build-one:
	$(OCAMLBUILD) $(INCLUDE) $(FILE).native

# Hacky target to print the signature of a file; do:
# FILE=typing/foo.ml make print-sig
print-sig:
	ocamlc -i $(BUILDDIRS) $(FILE)

index:
	$(shell cd viewer && ./gen_index.sh)

# TAG=m1 make release
release:
	git archive --format tar --prefix mezzo-$(TAG)/ $(TAG) | bzip2 -9 > ../mezzo-$(TAG).tar.bz2
