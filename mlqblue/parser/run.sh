rm -f *.cmi *.cmo parser.ml parser.mli lexer.ml test

GEN=../qbluelib

# compile the generated module first (produces QBlueSyntax.cmi/.cmo in GEN)
ocamlc -I "$GEN" -c "$GEN/QBlueSyntax.ml"

# generate parser/lexer
menhir --infer --ocamlc "ocamlc -I $GEN" parser.mly
ocamllex lexer.mll

# compile everything that needs QBlueSyntax (must see QBlueSyntax.cmi)
ocamlc -I "$GEN" -c parser.mli
ocamlc -I "$GEN" -c parser.ml
ocamlc -I "$GEN" -c lexer.ml
ocamlc -I "$GEN" -c revert_to_lowprog.ml
ocamlc -I "$GEN" -c main.ml

# link: include QBlueSyntax.cmo from GEN first
ocamlc -I "$GEN" -o test \
  "$GEN/QBlueSyntax.cmo" parser.cmo lexer.cmo revert_to_lowprog.cmo main.cmo

./test "+1.0*XX  - 2.3*XY"


