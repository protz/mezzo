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
		$(shell find _build \( -iname '*.a' -or -iname '*.cmx' -or -iname '*.cmi' -or -iname '*.mzi' \) -and -not -iname 'myocamlbuild.*')

uninstall:
	$(OCAMLFIND) remove mezzocorelib || true

clean:
	$(OCAMLBUILD) -clean

