.PHONY: all clean

OCAMLBUILD := ocamlbuild -classic-display -use-menhir -cflags "-g" -lflags "-g"
INCLUDE    := -Is sets
MAIN       := Main

all:
	$(OCAMLBUILD) $(INCLUDE) $(MAIN).native
	ln -sf $(MAIN).native $(MAIN)

clean:
	rm -f *~ $(MAIN) $(MAIN).native
	$(OCAMLBUILD) -clean

