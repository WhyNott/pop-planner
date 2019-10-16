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

%In case I ever loose bash history:

%mmc --grade asm_fast.gc.decldebug.stseg --intermod-opt --make tests


% ------------------------ sussmann anomaly ----------------------------


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

% action(
	%     InitialN,
	%     [],
	%     [on(a, table), on(b, table), on(c, a), clear(b), clear(c)],
	%     []),
	% action(
	%     GoalN,
	%     [on(a, b), on(b, c)],
	%     [],
	%     [])
    % ]),

% --------------------------- cargo transportation ----------------------------


:- func at(logic.object, logic.object) = logic.disjunct.
at(A, B) = disjunct("at", [A, B]).
:- func cargo(logic.object) = logic.disjunct.
cargo(C) = disjunct("cargo", [C]).
:- func plane(logic.object) = logic.disjunct.
plane(P) = disjunct("plane", [P]).
:- func airport(logic.object) = logic.disjunct.
airport(A) = disjunct("airport", [A]).
:- func in(logic.object, logic.object) = logic.disjunct.
in(A, B) = disjunct("in", [A, B]).

:- func c1 = logic.object.
c1 = object("c1").
:- func c2 = logic.object. 
c2 = object("c2").
:- func sfo = logic.object.
sfo = object("sfo").
:- func jfk = logic.object.
jfk = object("jfk").
:- func p1 = logic.object.
p1 = object("p1").
:- func p2 = logic.object.
p2 = object("p2").

:- func airport_operators(logic.var_supply, logic.var_supply) = list.list(operator).
:- mode airport_operators(in, out) = out is det.
airport_operators(!VarSup) =
    [
    operator(
	action(name("Load", [C1, P1, A1]),
	    [at(C1, A1), at(P1, A1), cargo(C1),
	    plane(P1), airport(A1)],
	    [in(C1, P1)],
	    [at(C1, A1)]
	),
	[]
    ),
    operator(
	action(name("Unload", [C2, P2, A2]),
	    [in(C2, P2), at(P2, A2), cargo(C2),
	    plane(P2), airport(A2)],
	    [at(C2, A2)],
	    [in(C2, P2)]
	), 
	[]
    ),
    operator(	    
	action(name("Fly", [P, From, To]),
	    [at(P, From), plane(P), airport(From),
	    airport(To)],
	    [at(P, To)],
	    [at(P, From)]
	),
	[{From, To}]
    )]:-
    create_wrap_var(P1, !VarSup),
    create_wrap_var(P2, !VarSup),
    create_wrap_var(C1, !VarSup),
    create_wrap_var(C2, !VarSup),
    create_wrap_var(A1, !VarSup),
    create_wrap_var(A2, !VarSup),
    create_wrap_var(P, !VarSup),
    create_wrap_var(From, !VarSup),
    create_wrap_var(To, !VarSup).

	
	% action(
	%     InitialN,
	%     [],
	%     [at(c1, sfo), at(c2, jfk), at(p1, sfo), at(p2, jfk),
	%     cargo(c1), cargo(c2), plane(p1), plane(p2),
	%     airport(jfk), airport(sfo)],
	%     []),
	% action(
	%     GoalN,
	%     [at(c1, jfk), at(c2, sfo)],
	%     [],
	%     [])
	% ])
%Objects = [c1, c2, sfo, jfk, p1, p2],

%--------------- spare tire problem --------------

%at(A, B) is already defined in the cargo transportation problem
%it will work just fine here as well

:- func tire(logic.object) = logic.disjunct.
tire(A) = disjunct("tire", [A]).

:- func flat = logic.object.
flat = object("flat").

:- func spare = logic.object.
spare = object("spare").
:- func axle = logic.object.
axle = object("axle").
:- func trunk = logic.object.
trunk = object("trunk").
:- func floor = logic.object.
floor = object("floor"). %ground is a reserved mercury keyword, lol

:- func tire_operators(logic.var_supply, logic.var_supply) = list.list(operator).
:- mode tire_operators(in, out) = out is det.
tire_operators(!VarSup) =
    [
    operator(
	action(name("Remove", [A, B]),
	    [at(A, B)],
	    [at(A, floor)],
	    [at(A, B)]
	),
	    []
   ),
   operator(
       action(name("PutOn", [T, Axle]),
	   [tire(T), at(T, floor), at(flat, NotAxle)],
	   [at(T, axle)],
	   [at(T, floor)]
       ),
	   [{NotAxle, axle}]
   ),
   operator(
       action(name("LeaveOvernight", []),
	   [],
	   [],
	   [at(spare, floor), at(spare, axle), at(spare, trunk),
	   at(flat, floor), at(flat, axle), at(flat, trunk)]
       ),
	   []
   )]:-
   create_wrap_var(A, !VarSup),
   create_wrap_var(B, !VarSup),
   create_wrap_var(T, !VarSup),
   create_wrap_var(Axle, !VarSup),
   create_wrap_var(NotAxle, !VarSup).


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



% There is a limitation to my planning algorithm: it does not handle multiple same actions very well (or at all)
% In theory, adding support for multiple occurances of the same action should not be difficult. All I need to do is to add a counter field to the action type, and then have it set so that if a new action is instantiated, it gets a 1 higher number on the counter then the highest initially existing.
%But that would force me to make my action-getting predicate nondeterministic, rather then if-else based.
%I need to test if the actual implementations of planning algorithms allow for multiple occurances of the same action.


main(!IO):-
    VarSup = logic.init_var_supply,
    %    sussman_operators(VarSup, _) = Domain,
    %airport_operators(VarSup, _) = Domain,
    tire_operators(VarSup, _) = Domain,
    Objects = [flat, spare, axle, trunk, floor],
    InitialN = name("initial-state", []),
    GoalN = name("goal-state", []),
    NullAction = set.from_list([
	action(
	    InitialN,
	    [],
	    [tire(flat), tire(spare), at(flat, axle), at(spare, trunk)],
	    []),
	action(
	    GoalN,
	    [at(spare, axle)],
	    [],
	    [])
	]),
    poset.add(InitialN, GoalN, poset.init, NullOrder),
    NullPlan = plan(NullAction, NullOrder, set.init),
    Closure = {InitialN, GoalN},
    Agenda = [{at(spare, axle), GoalN}],
    (if
	pop(Agenda, Closure, Domain, Objects, NullPlan, plan(Actions, OutOrder, _)),
	poset.consistent(OutOrder)
	
    then
	poset.to_total(OutOrder, OutPlan),
	write_list(OutPlan, ", ", logic.write, !IO),
	nl(!IO),
	nl(!IO),
	poset.debug_to_list(OutOrder, OutList) ,
	write_list(OutList, "\n", (pred({X, Y}::in, !.YO::di, !:YO::uo) is det :-
	    logic.write(X, !YO), write_string(":",!YO), logic.write(Y, !YO)), !IO),
	write_list(set.to_sorted_list(Actions), " ,", print_action, !IO)
    else
	io.write("No solution found.", !IO),
	nl(!IO)
    ).
