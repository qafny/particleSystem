%{
    open Common
    
%}

/* Define the tokens of the language: */
%token <float> FLOAT
%token PLUS TIMES NEG XPau YPau ZPau IPau EOF

/* Define the "goal" nonterminal of the grammar: */
%start main
%type <Common.lowprog> main

%%

main:
    PLUS expression      			   { [$2] }
  | PLUS expression main 	                   { $2::$3 }

expression:
   FLOAT TIMES paulis				{ (($1,0.0),$3) }

paulis:
     pauli                              {[$1]}
   | pauli paulis                       {$1::$2}
   
pauli:
     XPau                              {Coq_paulix}
   | YPau                              {Coq_pauliy}
   | ZPau                              {Coq_pauliz}
   | IPau                              {Coq_paulii}

