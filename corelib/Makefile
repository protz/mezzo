# Compile the Mezzo core library using the Mezzo compiler.

.PHONY: all clean

OCAMLBUILD := ocamlbuild -classic-display -use-ocamlfind -package mezzolib

all:
	cd ../mezzolib && make uninstall && make install
	$(OCAMLBUILD) MezzoCoreLib.cma
# $(patsubst %.mz,%.cmo,$(wildcard *.mz))

clean:
	$(OCAMLBUILD) -clean

