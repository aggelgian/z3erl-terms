-module(smt).
-compile(export_all).

-define(IS_WHITESPACE(X), X =:= $\s orelse X =:= $\n orelse X =:= $\t orelse X =:= $\r).

%% Define the type system.
type_system() ->
  Ds = [
    %% Term
    {"Term", [ {"nil", []}
             , {"int", [{"ival", "Int"}]}
             , {"flt", [{"fval", "Real"}]}
             , {"lst", [{"hd", "Term"}, {"tl", "Term"}]}
             , {"tpl", [{"tval", "TermList"}]}
             , {"atm", [{"aval", "IntList"}]}
             , {"bin", [{"bval", "BitList"}]}
             ]},
    %% TermList
    {"TermList", [ {"tnil", []}
                 , {"tcons", [{"thd", "Term"}, {"ttl", "TermList"}]}
                 ]},
    %% IntList
    {"IntList", [ {"inil", []}
                , {"icons", [{"ihd", "Int"}, {"itl", "IntList"}]}
                ]},
    %% BitList
    {"BitList", [ {"bnil", []}
                , {"bcons", [{"bhd", "(_ BitVec 1)"}, {"btl", "BitList"}]}
                ]}
  ],
  z3erl:declare_datatypes([], Ds).

%% Auxiliary funs

%% Term
nil() -> z3erl:constructor("nil", []).
int(X) -> z3erl:constructor("int", [X]).
flt(X) -> z3erl:constructor("flt", [X]).
lst(X, Xs) -> z3erl:constructor("lst", [X, Xs]).
tpl(X) -> z3erl:constructor("tpl", [X]).
atm(X) -> z3erl:constructor("atm", [X]).
bin(X) -> z3erl:constructor("bin", [X]).
is_nil(X) -> z3erl:is_constructor("nil", X).
is_int(X) -> z3erl:is_constructor("int", X).
is_flt(X) -> z3erl:is_constructor("flt", X).
is_lst(X) -> z3erl:is_constructor("lst", X).
is_tpl(X) -> z3erl:is_constructor("tpl", X).
is_atm(X) -> z3erl:is_constructor("atm", X).
is_bin(X) -> z3erl:is_constructor("bin", X).
ival(X) -> z3erl:accessor("ival", X).
fval(X) -> z3erl:accessor("fval", X).
tval(X) -> z3erl:accessor("tval", X).
aval(X) -> z3erl:accessor("aval", X).
bval(X) -> z3erl:accessor("bval", X).
hdval(X) -> z3erl:accessor("hd", X).
tlval(X) -> z3erl:accessor("tl", X).
%% TermList
tnil() -> z3erl:constructor("tnil", []).
tcons(X, Xs) -> z3erl:constructor("tcons", [X, Xs]).
is_tnil(X) -> z3erl:is_constructor("tnil", X).
is_tcons(X) -> z3erl:is_constructor("tcons", X).
thd(X) -> z3erl:accessor("thd", X).
ttl(X) -> z3erl:accessor("ttl", X).
%% IntList
inil() -> z3erl:constructor("inil", []).
icons(X, Xs) -> z3erl:constructor("icons", [X, Xs]).
is_inil(X) -> z3erl:is_constructor("inil", X).
is_icons(X) -> z3erl:is_constructor("icons", X).
ihd(X) -> z3erl:accessor("ihd", X).
itl(X) -> z3erl:accessor("itl", X).
%% BitList
bnil() -> z3erl:constructor("bnil", []).
bcons(X, Xs) -> z3erl:constructor("bcons", [X, Xs]).
is_bnil(X) -> z3erl:is_constructor("bnil", X).
is_bcons(X) -> z3erl:is_constructor("bcons", X).
bhd(X) -> z3erl:accessor("bhd", X).
btl(X) -> z3erl:accessor("btl", X).

%% Encode an Erlang term to its representation.
encode([]) ->
  nil();
encode(X) when is_integer(X) ->
  int(integer_to_list(X));
encode(X) when is_float(X) ->
  flt(float_to_list(X, [{decimals, 10}]));
encode([X|Xs]) ->
  lst(encode(X), encode(Xs));
encode(X) when is_tuple(X) ->
  tpl(encode_tlist(tuple_to_list(X)));
encode(X) when is_atom(X) ->
  atm(encode_ilist(atom_to_list(X)));
encode(X) when is_bitstring(X) ->
  bin(encode_blist(X)).

encode_tlist([]) ->
  tnil();
encode_tlist([X|Xs]) ->
  tcons(encode(X), encode_tlist(Xs)).

encode_ilist([]) ->
  inil();
encode_ilist([X|Xs]) ->
  icons(integer_to_list(X), encode_ilist(Xs)).

encode_blist(<<>>) ->
  bnil();
encode_blist(<<X:1, Xs/bitstring>>) ->
  case X of
    0 -> bcons("#b0", encode_blist(Xs));
    1 -> bcons("#b1", encode_blist(Xs))
  end.

%% Set variables
is_variable({'var', _}) -> true;
is_variable(_) -> false.

variables(Symbs) ->
  Vs = ["x" ++ integer_to_list(I) || I <- lists:seq(1, length(Symbs))],
  Smt = [z3erl:declare_const(V, "Term") || V <- Vs],
  Env = ets:new(?MODULE, [set, protected]),
  ets:insert(Env, lists:zip(Symbs, Vs)),
  {Vs, Env, Smt}.

%% Communicate with solver
load(Port, Axs) ->
  lists:foreach(fun(Ax) -> port_command(Port, [Ax, io_lib:nl()]) end, Axs).

get_response(Port) ->
  receive {Port, {data, Resp}} -> Resp after 1000 -> throw(noreponse) end.

check(Port) ->
  load(Port, [z3erl:check()]),
  parse(get_response(Port)).

eval(Port, V) ->
  load(Port, [z3erl:eval(V)]),
  parse(get_response(Port)).


check_one(Term) ->
  Port = open_port({spawn, "z3 -smt2 -in"}, [in, out]),
  InitVars = [{'var', "x"}],
  {[X], Env, VarsDef} = variables(InitVars),
  load(Port, [type_system(), VarsDef]),
  Axs = [
    z3erl:assert(
      z3erl:equal(X, encode(Term))
    )
  ],
  load(Port, Axs),
  R = case check(Port) of
        "sat" -> eval(Port, X);
        Msg -> {error, Msg}
      end,
  ets:delete(Env),
  port_close(Port),
  R.

main() ->
  Tests = [42, ok, {42,ok}, <<1>>, [42|ok], [42, foo, <<1,4:5>>, {}], 3.14],
  F = fun(T) ->
      io:format("Testing ~p ... ", [T]),
      R = check_one(T),
      case R =:= T of
        true -> io:format("OK~n");
        false -> io:format("FAIL~n  ~p~n", [R])
      end
    end,
  lists:foreach(F, Tests).




%% PARSER

parse(Str) ->
  try
    {ok, Tokens, _EndLine} = smt_lexer:string(Str),
    {ok, Term} = smt_parser:parse(Tokens),
    try_decode(Term)
  catch
    error:_ -> Str
  end.

try_decode(Term) ->
%  io:format("Decoding ~p~n", [Term]),
  try
    decode(Term, dict:new())
  catch
    error:_ -> Term
  end.

decode({var, SAT}, _Env) when SAT =:= "sat" ->
  SAT;
decode({var, X}, Env) ->
  dict:fetch(X, Env);
decode(nil, _Env) ->
  [];
decode({int, {var, _}=X}, Env) ->
  decode(X, Env);
decode({int, X}, _Env) ->
  X;
decode({flt, X}, _Env) ->
  X;
decode({atm, {var, _}=X}, Env) ->
  decode(X, Env);
decode({atm, X}, Env) ->
  L = decode_ilist(X, [], Env),
  to_atom(L);
decode({lst, X, Xs}, Env) ->
  [decode(X, Env)|decode(Xs, Env)];
decode({tpl, {var, _}=X}, Env) ->
  decode(X, Env);
decode({tpl, X}, Env) ->
  L = decode_tlist(X, [], Env),
  list_to_tuple(L);
decode({bin, {var, _}=X}, Env) ->
  decode(X, Env);
decode({bin, X}, Env) ->
  decode_blist(X, [], Env);
decode({'let', Defs, X}, Env) ->
  F = fun({K, V}, Acc) -> dict:store(K, decode_partial(V, Acc), Acc) end,
  decode(X, lists:foldl(F, Env, Defs)).


decode_ilist(inil, Acc, _Env) ->
  lists:reverse(Acc);
decode_ilist({icons, X, {var, Var}}, Acc, Env) ->
  Val = dict:fetch(Var, Env),
  F = fun(I, Is) -> [I|Is] end,
  lists:foldl(F, [X|Val], Acc);
decode_ilist({icons, X, Xs}, Acc, Env) ->
  decode_ilist(Xs, [X|Acc], Env).

decode_tlist(tnil, Acc, _Env) ->
  lists:reverse(Acc);
decode_tlist({tcons, X, {var, Var}}, Acc, Env) ->
  Val = dict:fetch(Var, Env),
  F = fun(T, Ts) -> [T|Ts] end,
  lists:foldl(F, [decode(X, Env)|Val], Acc);
decode_tlist({tcons, X, Xs}, Acc, Env) ->
  decode_tlist(Xs, [decode(X, Env)|Acc], Env).

decode_blist(bnil, Acc, _Env) ->
  F = fun(Bits, Bin) ->
      N = list_to_integer(Bits),
      L = length(Bits),
      <<N:L, Bin/bitstring>>
    end,
  lists:foldl(F, <<>>, Acc);
decode_blist({bcons, Bits, {var, Var}}, Acc, Env) ->
  Val = dict:fetch(Var, Env),
  F = fun(Bs, Bin) ->
      N = list_to_integer(Bs),
      L = length(Bs),
      <<N:L, Bin/bitstring>>
    end,
  lists:foldl(F, Val, [Bits|Acc]);
decode_blist({bcons, Bits, Rest}, Acc, Env) ->
  decode_blist(Rest, [Bits|Acc], Env).


decode_partial(inil=X, Env) -> decode_ilist(X, [], Env);
decode_partial({icons, _, _}=X, Env) -> decode_ilist(X, [], Env);
decode_partial(tnil=X, Env) -> decode_tlist(X, [], Env);
decode_partial({tcons, _, _}=X, Env) -> decode_tlist(X, [], Env);
decode_partial(bnil=X, Env) -> decode_blist(X, [], Env);
decode_partial({bcons, _, _}=X, Env) -> decode_blist(X, [], Env);
decode_partial(X, Env) -> decode(X, Env).

to_atom(L) ->
  try
    list_to_existing_atom(L)
  catch
    error:badarg -> list_to_atom(L)
  end.
