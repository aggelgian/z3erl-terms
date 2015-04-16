-module(z3erl).
-compile(export_all).

-export_type([smt2/0, datatype/0]).

-type datatype() :: {Name :: string(), [{Constructor :: string(), [{Accessor :: string(), Type :: string()}]}]}.
-type smt2() :: string().

%% Declares datatypes.
-spec declare_datatypes([Sort :: string()], [datatype()]) -> smt2().
declare_datatypes(Ps, Ds) ->
  DeclOne = fun({Tp, Cs}) -> ["(", Tp, " ", [declare_clause(C) || C <- Cs], ")"] end,
  Decls = ["(", [DeclOne(D) || D <- Ds], ")"],
  lists:flatten(["(", "declare-datatypes (", string:join(Ps, " "), ") ", Decls, ")"]).

declare_clause({Constr, Ps}) ->
  L = [["(", A, " ", Tp, ")"] || {A, Tp} <- Ps],
  ["(", Constr, L, ")"].

%% Declares constants.
-spec declare_const(Name :: string(), Type :: string()) -> smt2().
declare_const(X, Tp) ->
  string:join(["(declare-const ", X, " ", Tp, ")"], "").

%% Add an assertion
-spec assert(smt2()) -> smt2().
assert(Stmt) -> "(assert " ++ Stmt ++ ")".

%% Check for satisfiability.
-spec check() -> smt2().
check() -> "(check-sat)".

%% Get a variable's interpretation.
-spec eval(string()) -> smt2().
eval(X) -> "(eval " ++ X ++ ")".

get_value(X) -> "(get-value (" ++ X ++ "))".

get_model() -> "(get-model)".

-spec is_constructor(string(), string()) -> smt2().
is_constructor(Constr, X) -> string:join(["(is-", Constr, " ", X, ")"], "").

-spec accessor(string(), string()) -> smt2().
accessor(Acs, X) -> string:join(["(", Acs, " ", X, ")"], "").

-spec constructor(string(), [string()]) -> smt2().
constructor(Constr, []) -> Constr;
constructor(Constr, Ps) -> "(" ++ Constr ++ " " ++ string:join(Ps, " ") ++ ")".

%% Operators

equal(X, Y) -> string:join(["(= ", X, " ", Y, ")"], "").
not_equal(X, Y) -> string:join(["(not (= ", X, " ", Y, "))"], "").
