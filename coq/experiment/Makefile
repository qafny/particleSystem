COQC=coqc
COQDIR=.
OCDIR=.
EXDIR=.
OCAMLC=ocamlopt
OCAMLFLAGS=-I $(EXDIR)

.PHONY: all extract build run clean clobber

all: extract build

extract:
	@ $(COQC) -q -R . QBlue QBlueSyntax.v \
	&& $(COQC) -q -R . QBlue QBlueType.v \
	&& $(COQC) -q -R . QBlue QBlueSemantics.v \
	&& $(COQC) -q -R . QBlue QBlueCompiler.v \
	&& $(COQC) -q -R . QBlue Main1.v \
	&& $(COQC) -q -R . QBlue Extract.v
	@echo "[ok] Extracted to $(EXDIR)"


build: extract
	@set -e; \
	# 1) Interfaces (.mli) -> .cmi in dep order (if any)
	ocamldep -sort -I $(EXDIR) ./*.mli 2>/dev/null > $(EXDIR)/ifiles.list || true; \
	for f in `cat $(EXDIR)/ifiles.list 2>/dev/null || true`; do \
	  [ -f "$$f" ] && $(OCAMLC) $(OCAMLFLAGS) -c "$$f"; \
	done; \
	# 2) Implementations (.ml) -> .cmx in dep order
	ocamldep -sort -I $(EXDIR) ./*.ml > $(EXDIR)/mfiles.list; \
	for f in `cat $(EXDIR)/mfiles.list`; do \
	  $(OCAMLC) $(OCAMLFLAGS) -c "$$f"; \
	done; \
	# 3) Link everything with main.ml (using the same list)
	MFILES=`cat $(EXDIR)/mfiles.list`; \
	$(OCAMLC) $(OCAMLFLAGS) -O3 -o $(OCDIR)/demo $$MFILES ; \
	echo "[ok] Built $(OCDIR)/demo"


run: build
	./$(OCDIR)/demo

clean:
	@rm -f $(OCDIR)/demo
	@rm -f $(OCDIR)/*.{o,cmi,cmx,cmxa,a} 2>/dev/null || true
	@rm -f $(EXDIR)/*.{o,cmi,cmx,cmxa,a} 2>/dev/null || true
	@rm -f $(EXDIR)/*files.list
	@rm -f $(COQDIR)/*.{glob,vos,vo,vok} 2>/dev/null || true

clobber: clean
	@rm -f $(EXDIR)/*.{mli,ml}  2>/dev/null || true
