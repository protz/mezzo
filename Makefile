.PHONY: all clean

USE_OCAMLFIND := $(shell if `which ocamlfind > /dev/null`; then echo "-use-ocamlfind"; fi)
OCAMLBUILD := ocamlbuild $(USE_OCAMLFIND) -classic-display -use-menhir \
  -menhir "menhir --explain --infer -la 1" \
  -cflags "-g" -lflags "-g"
INCLUDE    := -Is sets,typing,parsing,ulex,lib 
MAIN       := hamlet
TEST	   := test

.PHONY: clean foo

all: $(MAIN).native $(TEST).native

%.native: foo
	$(OCAMLBUILD) $(INCLUDE) $*.native
	ln -sf $*.native $*

clean:
	rm -f *~ $(MAIN) $(MAIN).native $(TEST) $(TEST).native
	$(OCAMLBUILD) -clean
