.PHONY: all install uninstall clean

OCAMLBUILD := ocamlbuild -use-ocamlfind -cflags "-g" -lflags "-g" -classic-display
OCAMLFIND  := ocamlfind
TO_BUILD   := MezzoLib.cma MezzoLib.cmxa

all:
	$(OCAMLBUILD) $(TO_BUILD)

install: all
	$(OCAMLFIND) install mezzolib META \
		$(patsubst %,_build/%,$(TO_BUILD)) \
		_build/*.a _build/*.cmx _build/*.cmi

uninstall:
	$(OCAMLFIND) remove mezzolib || true

clean:
	$(OCAMLBUILD) -clean

