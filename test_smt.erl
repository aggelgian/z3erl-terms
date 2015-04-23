-module(test_smt).
-compile(export_all).

test_all() ->
  F = fun(Title, Tests) ->
      io:format("~n====== ~s ======~n~n", [Title]),
      test_category(Tests)
    end,
  Xs = [
    {
      "BITSTRINGS",
      [<<42:(100*8)>>, <<42:(500*8)>>, <<42:(1024*8)>>, <<42:(2048*8)>>]
    },
    {
      "LISTS OF INTS",
      [lists:seq(1, 100), lists:seq(1, 1000), lists:seq(1, 10000), lists:seq(1, 20000)]
    }
  ],
  [F(A, B) || {A, B} <- Xs].

test_category(Tests) ->
  io:format("Size of term | Length of encoded term | Encode time | Send time | Parse & Solve time | Get time~n"),
  io:format("-------------+------------------------+-------------+-----------+--------------------+---------~n"),
  F = fun(T) ->
      {R, EncT, TEnc, TLoad, TSolve, TGet} = test_one(T),
      R = T,
      {Unit, Sz} = sz(R),
      io:format("~6.w ~s | ~16.w chars | ~10.4fs | ~8.4fs | ~17.4fs | ~7.4fs~n", [Sz, Unit, length(EncT), TEnc, TLoad, TSolve, TGet])
    end,
  lists:foreach(F, Tests).

test_one(Term) ->
  Port = open_port({spawn, "z3 -smt2 -in"}, [in, out, {line, 10000000}]),
  InitVars = [{'var', "x"}],
  T1 = erlang:now(),
  {[X], Env, VarsDef} = smt:variables(InitVars),
  InitAxs = [smt:type_system()] ++ [VarsDef],
  {EncAxs, EncTerm} = smt:encode(Term),
  Axs = [z3erl:assert(z3erl:equal(X, EncTerm))],
  T2 = erlang:now(),
  smt:load(Port, InitAxs),
  smt:load(Port, EncAxs),
  smt:load(Port, Axs),
  T3 = erlang:now(),
  "sat" = smt:check(Port),
  T4 = erlang:now(),
  {model, Md} = smt:get_model(Port),
  [{X, true, R}] = ets:lookup(Md, X),
  T5 = erlang:now(),
  ets:delete(Env),
  port_close(Port),
  {R, EncTerm, tdiff(T1,T2), tdiff(T2,T3), tdiff(T3,T4), tdiff(T4,T5)}.

tdiff(T1, T2) ->
  timer:now_diff(T2, T1) / 1000000.

sz(T) when is_bitstring(T) ->
  {"bytes", size(T)};
sz(T) when is_list(T) ->
  {"items", length(T)}.
