rm -f *.cmi *.cmo parser.ml parser.mli lexer.ml test

ocamlc -c syntax.ml
menhir --infer parser.mly
ocamllex lexer.mll
ocamlc -c parser.mli
ocamlc -c parser.ml
ocamlc -c lexer.ml
ocamlc -c revert_to_lowprog.ml
ocamlc -c main.ml
ocamlc -o test syntax.cmo parser.cmo lexer.cmo revert_to_lowprog.cmo main.cmo
./test "+1.0*XX + 2.3*XY"


