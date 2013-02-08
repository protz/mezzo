.PHONY: all clean

all: $(patsubst %.mz,%.cmo,$(wildcard *.mz))

-include $(patsubst %.mz,%.d,$(wildcard *.mz))

# Compile the Mezzo core library using the Mezzo compiler.

clean:
	rm -f *.ml *.mli

%.ml: %.mz
	../mezzo -c $< >/dev/null

%.d: %.ml
	ocamldep $< > $@

%.cmo: %.ml
	ocamlc -c $<
