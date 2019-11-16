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

%for time profiling:

%mmc --grade asm_fast.gc.prof.stseg --intermod-opt --make tests
%

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

% action(
% 	    InitialN,
% 	    [],
% 	    [tire(flat), tire(spare), at(flat, axle), at(spare, trunk)],
% 	    []),
% 	action(
% 	    GoalN,
% 	    [at(spare, axle)],
% 	    [],
% 	    [])
	
%--------------- gripper problem --------------

% Plan:
%   pick(ball1, rooma, left)
%   move(rooma, roomb)
%   drop(ball1, roomb, left)
%   move(roomb, rooma)
%   pick(ball2, rooma, left)
%   pick(ball3, rooma, right)
%   move(rooma, roomb)
%   drop(ball2, roomb, left)
%   drop(ball3, roomb, right)


:- func room(logic.object) = logic.disjunct.
room(R) = disjunct("room", [R]).
:- func ball(logic.object) = logic.disjunct.
ball(B) = disjunct("ball", [B]).
:- func gripper(logic.object) = logic.disjunct.
gripper(G) = disjunct("gripper", [G]).
:- func at_robby(logic.object) = logic.disjunct.
at_robby(R) = disjunct("at_robby", [R]).
% at(A, B) is already defined
:- func freee(logic.object) = logic.disjunct.
freee(G) = disjunct("free", [G]).
:- func carry(logic.object, logic.object) = logic.disjunct. 
carry(O, G) = disjunct("carry", [O, G]).

:- func room_a = logic.object.
room_a = object("room_a").  
:- func room_b = logic.object.
room_b = object("room_b").  
:- func ball1 = logic.object. 
ball1 = object("ball1").      
:- func ball2 = logic.object. 
ball2 = object("ball2").      
:- func ball3 = logic.object. 
ball3 = object("ball3").      
:- func ball4 = logic.object. 
ball4 = object("ball4").      
:- func left = logic.object. 
left  = object("left").       
:- func right = logic.object. 
right = object("right").  

:- func gripper_operators(logic.var_supply, logic.var_supply) = list.list(operator).
:- mode gripper_operators(in, out) = out is det.

gripper_operators(!VarSup) =
    [
    operator(
	action(name("move", [From, To]),
	    [room(From), room(To), at_robby(From)],
	    [at_robby(To)],
	    [at_robby(From)]
	),
	    []
	),
%move 2: electric bungaloo
    % 	    operator(
    % 		action(name("move2", [From, To]),
    % 	    [room(From), room(To), at_robby(From)],
    % 	    [at_robby(To)],
    % 	    [at_robby(From)]
    % 	),
    % 	    []
    % ),
    operator(
	action(name("pick", [Obj, Room, Gripper]),
	    [ball(Obj), room(Room), gripper(Gripper)],
	    [at(Obj, Gripper)],
	    [at(Obj, Room)]
	),
	    []
   ),
   operator(
       action(name("drop", [Obj2, Room2, Gripper2]),
	   [ball(Obj2), room(Room2), gripper(Gripper2), carry(Obj2, Gripper2), at_robby(Room2)],
	   [at(Obj2, Room2), freee(Gripper2)],
	   [carry(Obj2, Gripper2)]
       ),
	   []
   )]:-
   create_wrap_var(From, !VarSup),
   create_wrap_var(To, !VarSup),
   create_wrap_var(Obj, !VarSup),
   create_wrap_var(Room, !VarSup),
   create_wrap_var(Gripper, !VarSup),
   create_wrap_var(Obj2, !VarSup),
   create_wrap_var(Room2, !VarSup),
   create_wrap_var(Gripper2, !VarSup).





%--------------- 2 robots problem --------------
%open_door
%move_in(r1)
%open_door
%move_in(r2)

%note to self: it would make 200 times more sense if disjuncts were
    %called 'properties' or 'state properties' instead
:- func inside(logic.object) = logic.disjunct.
inside(R) = disjunct("inside", [R]).
:- func outside(logic.object) = logic.disjunct.
outside(R) = disjunct("outside", [R]).
:- func door_open = logic.disjunct.
door_open = disjunct("door_open", []).
:- func door_closed = logic.disjunct.
door_closed = disjunct("door_closed", []).

:- func robot1 = logic.object.
robot1 = object("robot1").
:- func robot2 = logic.object.
robot2 = object("robot2").

:- func robot_operators(logic.var_supply, logic.var_supply) = list.list(operator).
:- mode robot_operators(in, out) = out is det.

robot_operators(!VarSup) =
    [
    operator(
	action(name("open_door", [], repeated_top_copy(2)),
	    [door_closed],
	    [door_open],
	    [door_closed]
    ), [] ),

	    operator(
		action(name("move_in", [Robot]),
		    [outside(Robot), door_open],
		    [inside(Robot), door_closed],
		    [outside(Robot), door_open]
		), [] )
		    ]:-
			create_wrap_var(Robot, !VarSup).


	% action(
	%     InitialN,
	%     [],
	%     [outside(robot1), outside(robot2), door_closed],
	%     []),
	% action(
	%     GoalN,
	%     [inside(robot1), inside(robot2)],
	%     [],
	%     [])
        % ]),






%I'm scared.



	
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



%I hate to say it, but my planner is just really fucking slow.

%Sooner or later, the performace heuristics will become a neccesity.

%In the meantime, I will turn this module into a regression test suite.

%TODO: implement a predicate that verifies that a plan is correct, by applying all the actions step by step and seeing if one arrives at the goal.
%(Seems like a liberal application of fold should be sufficient)



main(!IO):-
    VarSup = logic.init_var_supply,
    %    sussman_operators(VarSup, _) = Domain,
    %airport_operators(VarSup, _) = Domain,
    %tire_operators(VarSup, _) = Domain,
    gripper_operators(VarSup, _) = Domain,
    %robot_operators(VarSup, _) = Domain,
    Objects = [room_a, room_b, ball1, ball2, ball3, ball4, left, right],
    %Objects = [c1, c2, sfo, jfk, p1, p2],
    %Objects = [robot1, robot2],
    InitialN = name("initial-state", []),
    GoalN = name("goal-state", []),
    NullAction = set.from_list([
	action(
	    InitialN,
	    [],
	    [room(room_a), room(room_b), ball(ball1), ball(ball2),
	    ball(ball3), ball(ball4), gripper(left), gripper(right),
	    at_robby(room_a), at(ball2, room_a),
	    at(ball3, room_a), at(ball4, room_a)],
	    []),
	action(
	    GoalN,
	    [at(ball1, room_b), at(ball2, room_b), at(ball3, room_b)],
	    [],
	    [])
        ]),

    poset.add(InitialN, GoalN, poset.init, NullOrder),
    NullPlan = plan(NullAction, NullOrder, set.init),
    Closure = {InitialN, GoalN},
    Agenda = [{at(ball1, room_b), GoalN}, {at(ball2, room_b), GoalN}, {at(ball3, room_b), GoalN}],
    (if
	pop(Agenda, Closure, Domain, Objects, NullPlan, plan(Actions, OutOrder, _)),
	poset.consistent(OutOrder)
	
    then
	poset.to_total(OutOrder, OutPlan),
	write_list(OutPlan, ", ", logic.write, !IO),
	nl(!IO),
	nl(!IO),
	% poset.debug_to_list(OutOrder, OutList) ,
	% write_list(OutList, "\n", (pred({X, Y}::in, !.YO::di, !:YO::uo) is det :-
	%     logic.write(X, !YO), write_string(":",!YO), logic.write(Y, !YO)), !IO),
	write_list(set.to_sorted_list(Actions), " ,", print_action, !IO)
    else
	io.write("No solution found.", !IO),
	nl(!IO)
    ).
