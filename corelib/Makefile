# Compile the Mezzo core library using the Mezzo compiler.

.PHONY: all clean

OCAMLBUILD := ocamlbuild -classic-display -use-ocamlfind

all:
	$(OCAMLBUILD) $(patsubst %.mz,%.cmo,$(wildcard *.mz))

clean:
	$(OCAMLBUILD) -clean

# %.ml: %.mz
# 	../mezzo -c $< >/dev/null

# %.d: %.ml
# 	ocamldep $< > $@

# %.cmo: %.ml
# 	ocamlc -c $<
