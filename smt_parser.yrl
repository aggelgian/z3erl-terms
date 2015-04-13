Nonterminals
term letdef localdefs localdef expr.

Terminals '(' ')' '/'
'let' nil int flt lst tpl atm bin tnil tcons inil icons bnil bcons
integer bitval strlit floatlit.

Rootsymbol term.

term -> expr : '$1'.

letdef -> '(' 'let' '(' localdefs ')' expr ')' : {'let', '$4', '$6'}.

localdefs -> localdef : ['$1'].
localdefs -> localdefs localdef : ['$2' | '$1'].

localdef -> '(' strlit expr ')' : {unwrap('$2'), '$3'}.

expr -> letdef : '$1'.
expr -> strlit : {var, unwrap('$1')}.
expr -> integer : unwrap('$1').
expr -> nil : nil.

%% Integers
expr -> '(' int expr ')' : {int, '$3'}.

%% Floats
expr -> '(' flt expr ')' : {flt, '$3'}.
expr -> '(' '/' floatlit floatlit ')' : (unwrap('$3') / unwrap('$4')).

%% Atoms
expr -> '(' atm expr ')' : {atm, '$3'}.
expr -> inil : inil.
expr -> '(' icons expr expr ')' : {icons, '$3', '$4'}.

%% Lists
expr -> '(' lst expr expr ')' : {lst, '$3', '$4'}.

%% Tuples
expr -> '(' tpl expr ')' : {tpl, '$3'}.
expr -> tnil : tnil.
expr -> '(' tcons expr expr ')' : {tcons, '$3', '$4'}.

%% Bitstrings
expr -> '(' bin expr ')' : {bin, '$3'}.
expr -> bnil : bnil.
expr -> '(' bcons bitval expr ')' : {bcons, unwrap('$3'), '$4'}.

Erlang code.

unwrap({_,_,V}) -> V.
