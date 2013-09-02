# Compile the Mezzo core library using the Mezzo compiler.

.PHONY: all clean

TO_BUILD   := MezzoCoreLib.cma MezzoCoreLib.cmxa MezzoCoreLib.cmxs
OCAMLBUILD := ocamlbuild -classic-display -use-ocamlfind -package mezzolib
OCAMLFIND  := ocamlfind

all:
	$(OCAMLBUILD) $(TO_BUILD)

install: all
	$(OCAMLFIND) install mezzocorelib META \
		$(patsubst %,_build/%,$(TO_BUILD)) \
		_build/*.a _build/*.cmx _build/*.cmi _build/*.mzi

uninstall:
	$(OCAMLFIND) remove mezzocorelib || true

clean:
	$(OCAMLBUILD) -clean

