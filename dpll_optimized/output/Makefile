FSTAR_HOME?=../../..

ifeq ($(OS),Windows_NT)
  OCAMLPATH := $(shell cygpath -m $(FSTAR_HOME)/lib);$(OCAMLPATH)
else
  OCAMLPATH := $(FSTAR_HOME)/bin:$(OCAMLPATH)
endif

# with dune
Main.exe: $(wildcard *.ml)
	OCAMLPATH="$(OCAMLPATH)" dune build
	cp _build/default/Main.exe .

#with ocamlbuild
Main.native: $(wildcard *.ml)
	OCAMLPATH="$(OCAMLPATH)" ocamlbuild -tag thread -use-ocamlfind -quiet -pkg batteries -pkg fstarlib -cflags -w,-8 Main.native

clean:
	rm -rf _build Main.native Main.exe