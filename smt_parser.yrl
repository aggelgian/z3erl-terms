Nonterminals
term letdef localdefs localdef expr modelrepr funDefs funDef funparams funparam type.

Terminals '(' ')' '/' '='
'let' 'define-fun' 'as-array' '_' model ite
base nil int flt lst tpl atm bin tnil tcons inil icons bnil bcons mmap func fun1
integer bitval strlit floatlit.

Rootsymbol term.

term -> expr : '$1'.

letdef -> '(' 'let' '(' localdefs ')' expr ')' : {'let', '$4', '$6'}.

localdefs -> localdef : ['$1'].
localdefs -> localdefs localdef : ['$2' | '$1'].

localdef -> '(' strlit expr ')' : {unwrap('$2'), '$3'}.

modelrepr -> '(' model funDefs ')' : '$3'.

funDefs -> funDef : ['$1'].
funDefs -> funDefs funDef : ['$2' | '$1'].

funDef -> '(' 'define-fun' expr '(' ')' type expr  ')' : {fundef, '$3', {funinfo, [], '$6', '$7'}}.
funDef -> '(' 'define-fun' expr '(' funparams ')' type expr  ')' : {fundef, '$3', {funinfo, '$5', '$7', '$8'}}.

funparams -> funparam : ['$1'].
funparams -> funparams funparam : ['$2' | '$1'].

funparam -> '(' expr type ')' : {param, '$2', '$3'}.

type -> expr : '$1'.
type -> '(' strlit strlit strlit ')' : {var, string:join(["(", unwrap('$2'), unwrap('$3'), unwrap('$4'), ")"], " ")}.

expr -> modelrepr : '$1'.

expr -> letdef : '$1'.
expr -> strlit : {var, unwrap('$1')}.
expr -> integer : unwrap('$1').
expr -> nil : nil.

%% BaseTerm
expr -> '(' base expr ')' : {base, '$3'}.

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

%% As array
expr -> '(' '_' 'as-array' expr ')' : {as_array, '$4'}.

%% Maps
expr -> '(' mmap expr ')' : {mmap, '$3'}.

%% Funs
expr -> '(' fun1 expr ')' : {fun1, '$3'}.
expr -> '(' func expr ')' : {func, '$3'}.

%% Operators
expr -> '(' ite expr expr expr ')' : {'if', '$3', '$4', '$5'}.
expr -> '(' '=' expr expr ')' : {eq, '$3', '$4'}.

Erlang code.

unwrap({_,_,V}) -> V.
