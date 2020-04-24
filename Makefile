LIBS := unix,str

all: olisp.native

olisp.native:
	ocamlbuild -libs $(LIBS) olisp.native 

clean: 
	ocamlbuild -clean