%{
  open QBlueSyntax

  let rec list_to_map_aux l n =
    match l with
    | [] -> (fun _ -> Coq_paulii)
    | x :: xs ->
        let rest = list_to_map_aux xs (n + 1) in
        (fun i -> if i = n then x else rest i)

  let list_to_map l = list_to_map_aux l 0
%}

/* Define the tokens of the language: */
%token <float> FLOAT
%token PLUS MINUS TIMES XPau YPau ZPau IPau EOF

/* Define the "goal" nonterminal of the grammar: */
%start program
%type <lowprog> program

%%


program:
  terms EOF { $1 }

terms:
    signed_term                         { [$1] }
  | terms signed_term                   { $1 @ [$2] }
;

/* Each term must start with + or - */
signed_term:
  PLUS expression
    { $2 }
| MINUS expression
    { let ((a, _), op) = $2 in ((-. a, 0.0), op) }
;

expression:
    FLOAT TIMES paulis                  { (($1, 0.0), list_to_map $3) }
;

paulis:
     pauli                              {[$1]}
   | pauli paulis                       {$1::$2}
   
pauli:
     XPau                              {Coq_paulix}
   | YPau                              {Coq_pauliy}
   | ZPau                              {Coq_pauliz}
   | IPau                              {Coq_paulii}

