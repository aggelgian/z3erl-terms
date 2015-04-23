-module(smt).
-compile(export_all).

-define(IS_WHITESPACE(X), X =:= $\s orelse X =:= $\n orelse X =:= $\t orelse X =:= $\r).

%% Define the type system.
type_system() ->
  BDs = [
    %% BaseTerm
    {"BaseTerm", [ {"nil", []}
             , {"int", [{"ival", "Int"}]}
             , {"flt", [{"fval", "Real"}]}
             , {"lst", [{"hd", "BaseTerm"}, {"tl", "BaseTerm"}]}
             , {"tpl", [{"tval", "BaseTermList"}]}
             , {"atm", [{"aval", "IntList"}]}
             , {"bin", [{"bval", "BitList"}]}
             ]},
    %% BaseTermList
    {"BaseTermList", [ {"tnil", []}
                 , {"tcons", [{"thd", "BaseTerm"}, {"ttl", "BaseTermList"}]}
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
  Base = z3erl:declare_datatypes([], BDs),
  FDs = [
    %% Fun
    {"FunTerm", [ {"fun1", [{"f1val", "(Array BaseTerm BaseTerm)"}]}
                ]}
  ],
  Fun = z3erl:declare_datatypes([], FDs),
  EDs = [
    %% Term
    {"Term", [ {"base", [{"btval", "BaseTerm"}]}
             , {"mmap", [{"mval", "(Array BaseTerm BaseTerm)"}]}
             , {"func", [{"fnval", "FunTerm"}]}
             ]}
  ],
  Ext = z3erl:declare_datatypes([], EDs),
  [Base, Fun, Ext].

%% Auxiliary funs

%% Term
base(X) -> z3erl:constructor("base", [X]).
mmap(X) -> z3erl:constructor("mmap", [X]).
func(X) -> z3erl:constructor("func", [X]).
is_base(X) -> z3erl:is_constructor("base", X).
is_mmap(X) -> z3erl:is_constructor("mmap", X).
is_func(X) -> z3erl:is_constructor("func", X).
btval(X) -> z3erl:accessor("btval", X).
mval(X) -> z3erl:accessor("mval", X).
fnval(X) -> z3erl:accessor("fnval", X).
%% BaseTerm
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
%% BaseTermList
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
%% FunTerm
fun1(X) -> z3erl:constructor("fun1", [X]).
is_fun1(X) -> z3erl:is_constructor("fun1", X).
f1val(X) -> z3erl:accessor("f1val", X).

%% Encode an Erlang term to its representation.
encode(X) when is_function(X) ->
  throw(todo);
encode(X) when is_map(X) ->
  encode_map(X);
encode(X) ->
  {[], base(encode_base(X))}.

encode_base([]) ->
  nil();
encode_base(X) when is_integer(X) ->
  int(integer_to_list(X));
encode_base(X) when is_float(X) ->
  flt(float_to_list(X, [{decimals, 10}]));
encode_base([X|Xs]) ->
  lst(encode_base(X), encode_base(Xs));
encode_base(X) when is_tuple(X) ->
  tpl(encode_tlist(tuple_to_list(X)));
encode_base(X) when is_atom(X) ->
  atm(encode_ilist(atom_to_list(X)));
encode_base(X) when is_bitstring(X) ->
  bin(encode_blist(X)).

encode_tlist([]) ->
  tnil();
encode_tlist([X|Xs]) ->
  tcons(encode_base(X), encode_tlist(Xs)).

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

encode_map(X) ->
  A = "a" ++ integer_to_list(cnt_array()),
  Smt = z3erl:declare_const(A, "(Array BaseTerm BaseTerm)"),
  F = fun(K, V, Acc) ->
      EK = encode_base(K),
      EV = encode_base(V),
      Ax = z3erl:assert(z3erl:equal( "(select "++A++" "++EK++")", EV )),
      [Ax|Acc]
    end,
  MsAxs = maps:fold(F, [], X),
  {[Smt|MsAxs], mmap(A)}.

cnt_array() ->
  case get(array_cnt) of
    undefined ->
      put(array_cnt, 1),
      1;
    N ->
      put(array_cnt, N+1),
      N+1
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
  receive {Port, {data, {_Flag, Resp}}} -> Resp after 300000 -> throw(noreponse) end.

check(Port) ->
  load(Port, [z3erl:check()]),
  parse(get_response(Port)).

get_model(Port) ->
  load(Port, [z3erl:get_model(), "(display 42)"]),
  loop_eval_response(Port, []).

eval(Port, V) ->
  load(Port, [z3erl:eval(V), "(display 42)"]),
  loop_eval_response(Port, []).

loop_eval_response(Port, Acc) ->
  case get_response(Port) of
    "42" ->
      Ps = lists:reverse(Acc),
      parse(string:join(Ps, ""));
    R ->
%      io:format("Got ~p~n", [R]),
      loop_eval_response(Port, [R|Acc])
  end.

%% TEST

test() ->
  Port = open_port({spawn, "z3 -smt2 -in"}, [in, out, {line, 10000000}]),
  InitVars = [{'var', "x"}, {'var', "y"}],
  {[X, Y], Env, VarsDef} = variables(InitVars),
  Pms = [
%    "(set-option :pp.single_line true)"
  ],
  load(Port, [Pms | type_system()] ++ [VarsDef]),
  {EncAxs, EncX} = encode(#{1 => 1, 2 => 2, ok => ok, 3.14 => {}}),
%  {EncAxs, EncX} = encode(1),
  load(Port, EncAxs),
  Axs = [
%    z3erl:assert(
%%      z3erl:equal(X, encode(<<1>>))
%      is_mmap(X)
%    ),
    z3erl:assert(
      z3erl:equal(X, EncX)
    ),
    z3erl:assert(
%      z3erl:equal(Y, encode(<<1, 42>>))
      is_func(Y)
    ),
    z3erl:assert(z3erl:equal("(select "++f1val(fnval(Y))++" (int 42))", encode_base("Bazinga!")))
  ],
  load(Port, Axs),
  case check(Port) of
    "sat" ->
      {model, Md} = get_model(Port),
      [{X, true, Vx}] = ets:lookup(Md, X),
      io:format("~p~n  ~p~n", [X, Vx]),
      [{Y, true, Vy}] = ets:lookup(Md, Y),
      io:format("~p~n  ~p~n", [Y, Vy]),
      case is_function(Vy, 1) of
        false -> ok;
        true -> io:format("Applying Function to 42 : ~p~n", [catch Vy(42)])
       end;
    Msg -> {error, Msg}
  end,
  ets:delete(Env),
  port_close(Port).


check_one(Term) ->
  Port = open_port({spawn, "z3 -smt2 -in"}, [in, out, {line, 10000000}]),
  InitVars = [{'var', "x"}],
  {[X], Env, VarsDef} = variables(InitVars),
  Pms = [
%    "(set-option :pp.single_line true)"
  ],
  load(Port, [Pms | type_system()] ++ [VarsDef]),
  {EncAxs, EncTerm} = encode(Term),
  load(Port, EncAxs),
  Axs = [
    z3erl:assert(
      z3erl:equal(X, EncTerm)
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
  {ok, Bin} = file:read_file("z3erl.erl"),
  Tests = [42, ok, {42,ok}, <<1>>, [42|ok], [42, foo, <<1,4:5>>, {}], 3.14
%    , Bin
  ],
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
    try
      decode_ast(Term)
    catch
      error:_ -> io:format("~p~n~n", [Term])
    end
  catch
    error:_ -> io:format("~p~n~n", [Str])
  end.

decode_ast(AST) when is_list(AST) ->
  Md = ets:new(?MODULE, [set, protected]),
  F = fun({fundef, {var, V}, FunInfo}, Acc) ->
      ets:insert(Md, {V, false, FunInfo}),
      [V|Acc]
    end,
  Ks = lists:foldl(F, [], AST),
  lists:foreach(fun(K) -> decode_fun(K, Md) end, Ks),
  {model, Md};
decode_ast(AST) ->
  decode(AST, [], dict:new(), none).


decode_fun(Key, Md) ->
  [{Key, IsEvaluated, Val}] = ets:lookup(Md, Key),
  case IsEvaluated of
    true -> ok;
    false ->
      Decd = decode_funinfo(Val, Md),
      ets:insert(Md, [{Key, true, Decd}])
  end.

decode_funinfo({funinfo, Params, {var, _RetType}, Body}, Md) ->
  Ps = [P || {param, {var, P}, {var, _Type}} <- Params],
  decode(Body, Ps, dict:new(), Md).



decode({var, SAT}, _Pms, _Env, _Md) when SAT =:= "sat" ->
  SAT;
decode({var, X}, _Pms, Env, Md) ->
  case dict:is_key(X, Env) of
    true -> dict:fetch(X, Env);
    false ->
      decode_fun(X, Md),
      [{X, true, Val}] = ets:lookup(Md, X),
      Val
  end;
decode({base, X}, Pms, Env, Md) ->
  decode(X, Pms, Env, Md);
decode(nil, _Pms, _Env, _Md) ->
  [];
decode({int, {var, _}=X}, Pms, Env, Md) ->
  decode(X, Pms, Env, Md);
decode({int, X}, _Pms, _Env, _Md) when is_integer(X) ->
  X;
decode({flt, {var, _}=X}, Pms, Env, Md) ->
  decode(X, Pms, Env, Md);
decode({flt, X}, _Pms, _Env, _Md) when is_float(X) ->
  X;
decode({atm, {var, _}=X}, Pms, Env, Md) ->
  decode(X, Pms, Env, Md);
decode({atm, X}, Pms, Env, Md) ->
  L = decode_ilist(X, [], Pms, Env, Md),
  to_atom(L);
decode({lst, X, Xs}, Pms, Env, Md) ->
  [decode(X, Pms, Env, Md) | decode(Xs, Pms, Env, Md)];
decode({tpl, {var, _}=X}, Pms, Env, Md) ->
  decode(X, Pms, Env, Md);
decode({tpl, X}, Pms, Env, Md) ->
  L = decode_tlist(X, [], Pms, Env, Md),
  list_to_tuple(L);
decode({bin, {var, _}=X}, Pms, Env, Md) ->
  decode(X, Pms, Env, Md);
decode({bin, X}, Pms, Env, Md) ->
  decode_blist(X, [], Pms, Env, Md);
decode({'let', Defs, Body}, Pms, Env, Md) ->
  F = fun({K, V}, Acc) ->
      EV = decode_partial(V, Pms, Acc, Md),
      dict:store(K, EV, Acc)
    end,
  decode(Body, Pms, lists:foldl(F, Env, Defs), Md);
decode({mmap, X}, Pms, Env, Md) ->
  Val = decode(X, Pms, Env, Md),
  case is_map(Val) of
    true  -> Val;
    false -> #{}
  end;
decode({fun1, X}, Pms, Env, Md) ->
  Val = decode(X, Pms, Env, Md),
  case is_map(Val) of
    true  -> fun(K) -> maps:get(K, Val) end;
    false -> fun(_) -> Val end
  end;
decode({as_array, {var, X}}, _Pms, _Env, Md) ->
  decode_fun(X, Md),
  [{X, true, Val}] = ets:lookup(Md, X),
  Val;
decode({'if', _, _, _}=X, Pms, Env, Md) ->
  decode_if(X, #{}, Pms, Env, Md);
decode({func, X}, Pms, Env, Md) ->
  decode(X, Pms, Env, Md).

decode_ilist(inil, Acc, _Pms, _Env, _Md) ->
  lists:reverse(Acc);
decode_ilist({var, Var}, Acc, _Pms, Env, _Md) ->
  Val = dict:fetch(Var, Env),
  F = fun(I, Is) -> [I|Is] end,
  lists:foldl(F, Val, Acc);
decode_ilist({icons, X, Xs}, Acc, Pms, Env, Md) ->
  decode_ilist(Xs, [X|Acc], Pms, Env, Md).

decode_tlist(tnil, Acc, _Pms, _Env, _Md) ->
  lists:reverse(Acc);
decode_tlist({var, Var}, Acc, _Pms, Env, _Md) ->
  Val = dict:fetch(Var, Env),
  F = fun(T, Ts) -> [T|Ts] end,
  lists:foldl(F, Val, Acc);
decode_tlist({tcons, X, Xs}, Acc, Pms, Env, Md) ->
  DX = decode(X, Pms, Env, Md),
  decode_tlist(Xs, [DX|Acc], Pms, Env, Md).

decode_blist(bnil, Acc, _Pms, _Env, _Md) ->
  F = fun(Bits, Bin) ->
      N = list_to_integer(Bits),
      L = length(Bits),
      <<N:L, Bin/bitstring>>
    end,
  lists:foldl(F, <<>>, Acc);
decode_blist({var, Var}, Acc, _Pms, Env, _Md) ->
  Val = dict:fetch(Var, Env),
  F = fun(Bits, Bin) ->
      N = list_to_integer(Bits),
      L = length(Bits),
      <<N:L, Bin/bitstring>>
    end,
  lists:foldl(F, Val, Acc);
decode_blist({bcons, Bits, Rest}, Acc, Pms, Env, Md) ->
  decode_blist(Rest, [Bits|Acc], Pms, Env, Md).

decode_if({var, Var}, Acc, _Pms, Env, _Md) ->
  Val = dict:fetch(Var, Env),
  maps:merge(Val, Acc);
decode_if({'if', {eq, {var, P}, CExpr}, TExpr, FExpr}, Acc, Pms, Env, Md) ->
  Key = decode(CExpr, Pms, Env, Md),
  Val = case TExpr of
          {var, Var} -> dict:fetch(Var, Env);
          _ -> decode(TExpr, Pms, Env, Md)
        end,
  decode_if(FExpr, maps:put(Key, Val, Acc), Pms, Env, Md);
decode_if(_, Acc, _Pms, _Env, _Md) ->
  Acc.

decode_partial(inil, Pms, Env, Md) ->
  decode_ilist(inil, [], Pms, Env, Md);
decode_partial({icons, _, _}=X, Pms, Env, Md) ->
  decode_ilist(X, [], Pms, Env, Md);
decode_partial(tnil, Pms, Env, Md) ->
  decode_tlist(tnil, [], Pms, Env, Md);
decode_partial({tcons, _, _}=X, Pms, Env, Md) ->
  decode_tlist(X, [], Pms, Env, Md);
decode_partial(bnil, Pms, Env, Md) ->
  decode_blist(bnil, [], Pms, Env, Md);
decode_partial({bcons, _, _}=X, Pms, Env, Md) ->
  decode_blist(X, [], Pms, Env, Md);
decode_partial({'if', _, _, _}=X, Pms, Env, Md) ->
  decode_if(X, #{}, Pms, Env, Md);
decode_partial(X, Pms, Env, Md) ->
  decode(X, Pms, Env, Md).


to_atom(L) ->
  try
    list_to_existing_atom(L)
  catch
    error:badarg -> list_to_atom(L)
  end.
