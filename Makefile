.PHONY: all %.byte tests/%.mz clean graph doc index report count

# The variables below should be determined by a configure script...
# On my MacOS laptop, find does not understand -printf; gfind does. -fpottier
FIND       := find
-include Makefile.local

OCAMLBUILD := ocamlbuild -use-ocamlfind -use-menhir \
  -menhir "menhir --explain --infer -la 1" \
  -cflags "-g" -lflags "-g" -classic-display
INCLUDE    := -Is sets,typing,parsing,ulex,lib,pprint,utils,fix
MAIN       := mezzo
TESTSUITE  := testsuite
BUILDDIRS   = -I _build $(shell $(FIND) _build -maxdepth 1 -type d -printf "-I _build/%f ")
MY_DIRS    := lib parsing sets typing utils
PACKAGES   := -package menhirLib,ocamlbuild,yojson,stdlib,ulex

all: configure.ml
	$(OCAMLBUILD) $(INCLUDE) $(MAIN).native $(TESTSUITE).native
	ln -sf $(MAIN).native $(MAIN)
	ln -sf $(TESTSUITE).native $(TESTSUITE)

configure.ml: configure
	./configure

clean:
	rm -f *~ $(MAIN) $(MAIN).native $(TESTSUITE) $(TESTSUITE).native
	$(OCAMLBUILD) -clean

test: all
	OCAMLRUNPARAM=b ./testsuite

# Re-generate the TAGS file
tags: all
	otags $(shell $(FIND) $(MY_DIRS) -iname '*.ml' -or -iname '*.mli')

# When you need to build a small program linking with all the libraries (to
# write a test for a very specific function, for instance).
%.byte:
	$(OCAMLBUILD) $(INCLUDE) $*.byte

# For easily debugging inside an editor. When editing tests/foo.mz, just do (in
# vim): ":make %".
tests/%.mz: mezzo.byte
	OCAMLRUNPARAM=b ./mezzo.byte -I tests -nofancypants $@

# For printing the signature of an .ml file
%.mli: all
	ocamlfind ocamlc $(PACKAGES) -i $(BUILDDIRS) $*.ml

# The index of all the nifty visualizations we've built so far
index:
	$(shell cd viewer && ./gen_index.sh)

# TAG=m1 make release
release:
	git archive --format tar --prefix mezzo-$(TAG)/ $(TAG) | bzip2 -9 > ../mezzo-$(TAG).tar.bz2

report:
	bisect-report -I _build -html report coverage*.out

coverage:
	BISECT_FILE=coverage ./testsuite

graph: all
	-ocamlfind ocamldoc -dot $(BUILDDIRS)\
	  $(PACKAGES)\
	  -o graph.dot\
	  $(shell $(FIND) $(MY_DIRS) -iname '*.ml' -or -iname '*.mli')\
	  configure.ml mezzo.ml
	sed -i 's/rotate=90;//g' graph.dot
	dot -Tsvg graph.dot > misc/graph.svg
	sed -i 's/^<text\([^>]\+\)>\([^<]\+\)/<text\1><a xlink:href="\2.html" target="_parent">\2<\/a>/' misc/graph.svg
	sed -i 's/Times Roman,serif/DejaVu Sans, Helvetica, sans/g' misc/graph.svg
	rm -f graph.dot

doc: graph
	-ocamlfind ocamldoc -html $(BUILDDIRS) \
	  -package stdlib,ulex -d ../misc/doc \
	  -intro ../misc/doc/main \
	  -charset utf8 -css-style ../../src/misc/ocamlstyle.css\
	  configure.ml mezzo.ml\
	  $(shell $(FIND) _build -maxdepth 2 -iname '*.mli')
	sed -i 's/<\/body>/<p align="center"><object type="image\/svg+xml" data="graph.svg"><\/object><\/p><\/body>/' ../misc/doc/index.html
	cp -f misc/graph.svg ../misc/doc/graph.svg

count:
	sloccount parsing typing utils viewer lib mezzo.ml
