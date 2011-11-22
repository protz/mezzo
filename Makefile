.PHONY: all clean

OCAMLBUILD := ocamlbuild -classic-display -use-menhir -menhir "menhir --explain --infer -la 1" -cflags "-g" -lflags "-g"
INCLUDE    := -Is sets -Is typing -Is parsing -Is ulex -Is lib
MAIN       := hamlet
TEST	   := test

all: $(MAIN).native $(TEST).native

%.native:
	$(OCAMLBUILD) $(INCLUDE) $*.native
	ln -sf $*.native $*

clean:
	rm -f *~ $(MAIN) $(MAIN).native $(TEST) $(TEST).native
	$(OCAMLBUILD) -clean

