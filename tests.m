:- module tests.
:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is cc_multi.

:- implementation.
:- import_module list.
:- import_module pop.
:- import_module solutions.
:- import_module map.
:- import_module set.
:- import_module poset.
:- import_module logic.



%encoding of the sussmann anomaly
%(in the future plans will be read from files, so this will not be quite as painfull)



:- func on(logic.object, logic.object) = logic.disjunct.
on(A, B) = disjunct("on", [A, B]).
:- func clear(logic.object) = logic.disjunct.
clear(A) = disjunct("clear", [A]).
:- func a = logic.object.
a = object("a").
:- func b = logic.object.
b = object("b").
:- func c = logic.object.
c = object("c").
:- func table = logic.object.
table = object("table").


    
:- func sussman_operators(logic.var_supply, logic.var_supply) = list.list(operator).
:- mode sussman_operators(in, out) = out is det.
sussman_operators(!VarSup) =
    [
    operator(
	action(name("Move", [B, X, Y]),
	    [on(B, X), clear(B), clear(Y)],
	    [on(B, Y), clear(X)],
	    [on(B, X), clear(Y)]
	),
	[{B, X}, {B, Y}, {X, Y}, {B, table}, {Y, table}]
    ), operator(
	    action(name("MoveToTable", [A, Z]),
		[on(A,Z), clear(A)],
		[on(A, table), clear(Z)],
		[on(A, Z)]
	    ),
	[{A, Z}, {A, table}, {Z, table}]
    )]:-
    create_wrap_var(B, !VarSup),
    create_wrap_var(X, !VarSup),
    create_wrap_var(Y, !VarSup),
    create_wrap_var(A, !VarSup),
    create_wrap_var(Z, !VarSup).

:- pred print_action(pop.action, io.state, io.state).
:- mode print_action(in, di, uo) is det.
print_action(Action, !IO):-
    io.nl(!IO),
    logic.write(Action^name, !IO),
    io.nl(!IO),
    io.write_list(Action^preconds, ",", logic.write, !IO),
    nl(!IO),
    write_list(Action^effects_add, ",", logic.write, !IO),
    nl(!IO),
    write_list(Action^effects_remove, ",", logic.write, !IO),
    io.nl(!IO),
    io.nl(!IO).

%It works now(again)! Declarative debugging is the king.

main(!IO):-
    VarSup = logic.init_var_supply,
    sussman_operators(VarSup, _) = Domain,
    Objects = [a, b, c, table],
    InitialN = name("initial-state", []),
    GoalN = name("goal-state", []),
    NullAction = set.from_list([
	action(
	    InitialN,
	    [],
	    [on(a, table), on(b, table), on(c, a), clear(b), clear(c)],
	    []),
	action(
	    GoalN,
	    [on(a, b), on(b, c)],
	    [],
	    [])
	]),
    poset.add(InitialN, GoalN, poset.init, NullOrder),
    NullPlan = plan(NullAction, NullOrder, set.init),
    Closure = {InitialN, GoalN},
    Agenda = [{on(b, c), GoalN}, {on(a, b), GoalN}],
    (if
	pop(Agenda, Closure, Domain, Objects, NullPlan, plan(Actions, OutOrder, _))
    then
	poset.to_total(OutOrder, OutPlan),
	write_list(OutPlan, ", ", logic.write, !IO),
	nl(!IO),
	nl(!IO),
	poset.debug_to_list(OutOrder, OutList),
	write_list(OutList, "\n", (pred({X, Y}::in, !.YO::di, !:YO::uo) is det :-
	    logic.write(X, !YO), write_string(":",!YO), logic.write(Y, !YO)), !IO),
	write_list(set.to_sorted_list(Actions), " ,", print_action, !IO)
    else
	io.write("No solution found.", !IO),
	nl(!IO)
    ).
