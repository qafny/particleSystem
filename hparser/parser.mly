%{
    open Common
 
%}

/* Define the tokens of the language: */
%token <float> FLOAT
%token <int> NAT
%token PLUS TIMES MINUS UNDER LPAR RPAR EOF

/* Define the "goal" nonterminal of the grammar: */
%start main
%type <((float * float) * int -> Common.blueExp list) list> main

[(float * float) * int -> [blueExp]]

%%

main:
    expression      			           { [$1] }
  | expression PLUS main 	                   { $1::$3 }

expression:
   FLOAT TIMES LPAR paulis RPAR				{ HTensor (($1,0.0),$4) }

paulis:
     op UNDER NAT                              {fun n -> if n = $3 then [$1] else []}
   | op UNDER NAT paulis                       {fun n -> if n = $3 then $1::($4 n) else $4 n}
   
op:
       PLUS  {HCrea}
     | MINUS {HAnni}
