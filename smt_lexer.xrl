Definitions.

D  = [0-9]
L  = [A-Za-z]
Cs = (base|nil|int|flt|lst|tpl|atm|bin|tnil|tcons|inil|icons|bnil|bcons)
WS = [\000-\s]

Rules.

let              : {token, {'let', TokenLine}}.
{Cs}             : {token, {atom(TokenChars), TokenLine}}.
[()\/]           : {token, {atom(TokenChars), TokenLine}}.
{D}+             : {token, {integer, TokenLine, list_to_integer(TokenChars)}}.
\#b(0|1)+        : {token, {bitval, TokenLine, bits(TokenChars)}}.
{D}+\.{D}+       : {token, {floatlit, TokenLine, list_to_float(TokenChars)}}.
{L}+(\!{D}+)?    : {token, {strlit, TokenLine, TokenChars}}.
{WS}+            : skip_token.

Erlang code.

bits([$\#, $b | Bits]) -> Bits.

atom(Cs) ->
  try
    list_to_existing_atom(Cs)
  catch
    error:badarg -> list_to_atom(Cs)
  end.
