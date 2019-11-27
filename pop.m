:- module pop.
:- interface.
:- import_module logic.
:- import_module list.
:- import_module set.
:- import_module poset.
:- import_module planner_data_structures.

:- type causal_link
         ---> causal_link(
	     producer :: action_name,
	     consumer :: action_name,
	     proposition :: ground_literal
	 ).

:- type plan ---> plan(
    a :: set(action),
    o :: poset(action_name),
    l :: set(causal_link)
).

:- type agenda == list({ground_literal, action_name}).


:- pred pop(agenda, {action_name, action_name}, list(operator), list(object), plan, plan).
:- mode pop(in, in, in, in, in, out) is nondet.


:- implementation.
:- import_module bfs.
:- import_module bool.
:- import_module map.
:- import_module solutions.
:- import_module int.
:- import_module require.
:- import_module maybe.
:- import_module io.


:- type node ---> node(plan :: plan, agenda :: agenda).

%These node update predicates help make code more readable.
%No more 'O_5', 'L_3', etc. State variables all the way.
%I wish there was a more natural way to do this though.


:- pred update_A(action, node, node).
:- mode update_A(in, in, out) is det.
update_A(Value, OldNode, NewNode):-
    OldNode = node(plan(A, O, L), Agenda),
    NewNode = node(plan(set.insert(A, Value), O, L), Agenda).

:- pred replace_A(set(action), node, node).
:- mode replace_A(in, in, out).
replace_A(NewA, OldNode, NewNode):-
    OldNode = node(plan(_, O, L), Agenda),
    NewNode = node(plan(NewA, O, L), Agenda).


:- pred update_O(action_name, action_name, node, node).
:- mode update_O(in, in, in, out) is det.
update_O(Before, After, OldNode, NewNode):-
    OldNode = node(plan(A, O, L), Agenda),
    NewNode = node(plan(A, poset.add(Before, After, O), L), Agenda).

:- pred update_L(causal_link, node, node).
:- mode update_L(in, in, out) is det.
update_L(NewLink, OldNode, NewNode):-
    OldNode = node(plan(A, O, L), Agenda),
    NewNode = node(plan(A, O, set.insert(L, NewLink)), Agenda).

%This one just takes a new agenda altogether.
:- pred update_Agenda(agenda, node, node).
:- mode update_Agenda(in, in, out) is det.
update_Agenda(NewAgenda, OldNode, NewNode):-
    OldNode = node(Plan, _),
    NewNode = node(Plan, NewAgenda).

%method to increment a name counter of an action
%useful for when we have more then 1 same action in our plan

:- func action_decrement(action) = action is semidet.
action_decrement(action(N, P, Ea, Er)) =
	action(name_decrement(N), P, Ea, Er).

:- func action_dethrone(action) = action.
action_dethrone(action(N, P, Ea, Er)) =
	action(name_dethrone(N), P, Ea, Er).



%How to bind operators:
%You need a specific term. You check if any of the terms in an operator's effects unifies with it. If one does, you check if the bindings are allowed. Then you pick (nondeterministically) values for the rest of the variables, again checking if the bindings are allowed for each one of them. Then you construct a ground action from the operator, and add it to the actions.  






:- pred bind_operator(operator, list.list(object), action, logic.substitution).
:- mode bind_operator(in, in, out, in) is nondet.
bind_operator(Operator, Objects, Action, MGU_init):-
    Lambda =
	(pred(Var::in, MGUin::in, MGUout::out) is nondet :-
	    member(X, Objects),
	    logic.unify(Var, X, Operator^noncodesignants, MGUin, MGUout)
	),
	    Operator^free_action^name = name(Name, Vars, C),
	    list.foldl(Lambda, Vars, MGU_init, MGU),
	    Action = action(
		name(Name, apply_sub_to_list(Vars, MGU), C),
		apply_sub_to_list(Operator^free_action^preconds, MGU),
		apply_sub_to_list(Operator^free_action^effects_add, MGU),
		apply_sub_to_list(Operator^free_action^effects_remove, MGU)
	    ).	    

		
%The belly of the beast.
%As an experiment, I want to be able to define a flag on an action that
%allows it to be repeated and then only do the repeating procedure
%if it has that flag set.

%So, the process goes this way:
%1. Find out whether there is already an action in Actions with right
%preconditions
%4. If it doesnt have a repeatable flag, choose it
%3. If it does have a repeatable flag, choose it
%nondeterministically OR
%Find out if it has the highest possible counter among all of its kind in
%actions and only if it does, add a new fresh replicant action with an 
%increased counter (if you do that, make sure to give an updated Actions 
%set out where the hinterto highest-counter action no longer has the 
%'newest' flag set)


:- pred get_suitable_action(ground_literal, set(action), maybe(set(action)), list(operator), list(object), action, bool).
:- mode get_suitable_action(in, in, out, in, in, out, out) is nondet.
get_suitable_action(Q, A, AOut, Domain, Objects, Result, IsFresh):-

    
   (if
       member(Action, A),
       member(Q, Action^effects_add)
   then
       (if
	   Action^name^repeat = unique
       then
	   Action = Result,
	   IsFresh = no,
	   AOut = no
       else
	   Action = Result,
	   IsFresh = no,
	   AOut = no
       ;
	   Action^name^repeat = repeated_top_copy(_),
	   action_decrement(Action) = Result,
	   AOut = yes(set.insert(set.delete(A, Action), action_dethrone(Action))),
	   IsFresh = yes
       )
   else
	%All the stuff related to grounding the operator will go here
	member(Operator, Domain),
	member(Term, Operator^free_action^effects_add),
	unify(Term, Q, Operator^noncodesignants, sub_init, MGU),
	bind_operator(Operator, Objects, Result, MGU),
	IsFresh = yes,
        AOut = no
).

	
:- pred add_precond_to_agenda(action_name, list.list(ground_literal), list.list({ground_literal, action_name}), list.list({ground_literal, action_name})).
:- mode add_precond_to_agenda(in, in, in, out) is det.
add_precond_to_agenda(Action, Precond, !Agenda):-
    (if
	Precond = [Conjunct|Xs]
    then
	!:Agenda = [{Conjunct, Action}|!.Agenda],
	add_precond_to_agenda(Action, Xs, !Agenda)
    else
	!:Agenda = !.Agenda
    ).

:- pred link_threathens(causal_link, poset(action_name), set(action), action).
:- mode link_threathens(in, in, in, out) is nondet.
link_threathens(causal_link(A_p, A_c, Q), Order, Actions, A_t):-
    member(A_t, Actions),
    A_p \= A_t^name,
    A_c \= A_t^name,
    member(Q, A_t^effects_remove), 
    poset.orderable(A_p, A_t^name, Order),
    poset.orderable(A_t^name, A_c, Order).

:- pred action_threathens(action, poset(action_name), set(causal_link), action_name, action_name).
:- mode action_threathens(in, in, in, out, out) is nondet.
action_threathens(A_t, Order, Links, A_p, A_c):-
    member(Q, A_t^effects_remove),
    A_p \= A_t^name,
    A_c \= A_t^name,
    member(causal_link(A_p, A_c, Q), Links), 
    poset.orderable(A_p, A_t^name, Order),
    poset.orderable(A_t^name, A_c, Order).

:- pred fix_constraint(action_name, action_name, action_name, node, node).
:- mode fix_constraint(in, in, in, in, out) is nondet.
fix_constraint(A_p, A_t, A_c, !Node):-
    poset.orderable(A_t, A_p, !.Node^plan^o),
    update_O(A_t, A_p, !Node)
    ;
    poset.orderable(A_c, A_t, !.Node^plan^o),
    update_O(A_c, A_t, !Node).

%neither of these two functions has great complexity
%but I will worry about that later

:- pred verify_link_threat(causal_link, node, node).
:- mode verify_link_threat(in,  in, out) is nondet.
verify_link_threat(causal_link(Add, Need, Q), !Node ):-
    (if
	link_threathens(causal_link(Add, Need, Q), !.Node^plan^o, !.Node ^ plan ^ a, A_t)
    then
	fix_constraint(Add, name(A_t), Need, !Node),
	verify_link_threat(causal_link(Add, Need, Q), !Node)
    else
	!.Node = !:Node
    ).

:- pred verify_action_threat(action, node, node).
:- mode verify_action_threat(in, in, out) is nondet.
verify_action_threat(Action, !Node):-
    (if
	action_threathens(Action, !.Node^plan^o, !.Node^plan^l, A_p, A_c)
    then
	fix_constraint(A_p, Action^name, A_c, !Node),
	verify_action_threat(Action, !Node)
    else
	!.Node = !:Node
    ).






%Seach problem:
%+ Node :: a tuple of the plan and an agenda
%+ Goal :: node where the agenda is empty
%+ successor function ::
% Any arbitrary flaw is taken from agenda 
%  A successor is such that an arbitrary action is chosen (either a newly instantiated one or a reused one from plan which can be ordered before). Out of the <A, O, L> and Agenda, the successor node:
% + To L we add a causal link between the new action and the one from the flaw, over the predicate from the flaw.
% + To O we add an ordering such that the new action in before the action from the flaw. In addition, if the action has been just freshly added (and not reused), we must also add that it is after the initial action and before the goal action.
% + To A we add the new action, if it is fresh.
% + From Agenda, we remove the flaw. If the new action is fresh, we add a new flaw for every predicate of its precondition.
%In addition, for the successor to be viable, there must be no action threathening any of the causal links. In order to make sure this is the case, ordering contraints will need to be added into L at correct times. If consistent ordering contrains cannot be procured, then it is not a valid successor (and hence it will fail).




:- pred flaw_selection(list.list({logic.disjunct, action_name}),  set.set(action), list.list(operator), list.list(logic.object), logic.disjunct, action, bool.bool, action_name, maybe.maybe(set.set(action))).
:- mode flaw_selection(in, in, in, in, out, out, out, out, out) is nondet.
flaw_selection(Agenda,  A, Domain, Objects, Q, Result, IsFresh, Need, AOut):-
    
    Maximum = 10000000000000, %Does mercury have a way to get the highest possible integer value?
 
   
    Fold = (pred({Q_n, Ne}::in, {Num_old, Set_old}::in, New::out) is semidet:-
	Lambda = (pred({Q_n1, AO, Res, IsF, Ne1}::out) is nondet:-
	    Q_n= Q_n1,
	    Ne1 = Ne,
	    get_suitable_action(Q_n, A, AO, Domain, Objects, Res, IsF)),
	solutions_set(Lambda, Set),
	Count = set.count(Set),
	Count \= 0, %if there is a flaw that cannot be refined, there is no hope
	(if
	    Count < Num_old
	then
	    New = {Count, Set}
	else
	    New = {Num_old, Set_old}
	)
    ),

	    list.foldl(Fold, Agenda, {Maximum, set.init}, {Countie, SelectedFlaw}),
%	    trace [io(!IO)] (io.write(Countie, !IO), io.nl(!IO)),
	    member({Q, AOut, Result, IsFresh, Need}, SelectedFlaw).	    


	  
%Okay, since I'm on a newer version of mercury now, with all these cool brand new compiler grades, maybe trailing works now. My unfortunate current predicament would be a nice test of this, actually! Lets inset printouts from time to time, and get it sorted out.

%So, its not working for the gripper problem for some reason.
%Turns out, it finds all these possible actions for depth 0 just fine. But when it comes to finding any further, it just doesn't, it finds 0.

%Hmm, I need to think about this. Still, its pretty good I now have this diagnostic system!


pop(Agenda, {Initial, Final}, Operators, Objects, !Plan):-
    bfs(node(!.Plan, Agenda), node(!:Plan, _), Successor, Goal),
    Goal = (pred(Node::in) is semidet :- Node = node(_, [])),
    
    Successor = (pred(!.Node::in, !:Node::out) is nondet :-
	flaw_selection(!.Node ^ agenda, (!.Node ^ plan ^ a), Operators, Objects, Q, Action, IsFresh, Need, AOut),
	%trace [io(!IO)] (io.write(Action^name, !IO), io.nl(!IO)),
	(if 
	    list.delete_first(!.Node ^ agenda, {Q, Need}, Xso)
	then
	    Xso=Xs
	else
	    error("this shouldn't happen")
	),
	%	!.Node ^ agenda = [{Q, Need}|Xs], 
%	get_suitable_action(Q, (!.Node ^ plan ^ a), AOut, Operators, Objects, Action, IsFresh), %cf
	(if
	    AOut = yes(NewA)
	then
	    replace_A(NewA, !Node)
	else
	    true
	),
	NewLink = causal_link(Action^name, Need, Q),
	verify_link_threat(NewLink, !Node), %cf
	update_L(NewLink, !Node),
	update_O(Action^name, Need, !Node),
	
	(if
	    IsFresh = yes
	then
	    update_O(Initial, Action^name, !Node),
	    update_O(Action^name, Final, !Node),
	    verify_action_threat(Action, !Node), %cf
	    update_A(Action, !Node),
	    add_precond_to_agenda(Action^name,
		Action^preconds,
		Xs, NewAgenda),
	    update_Agenda(NewAgenda, !Node)
	else
	    poset.orderable(Action^name, Need, !.Node ^ plan ^ o), %cf
	    update_Agenda(Xs, !Node)
	),
	    %remove this trace once you think you can get a result
	    trace [io(!IO)] (
		poset.to_total(!.Node ^ plan ^ o, Total),
		io.write(Total, !IO), io.nl(!IO))
    ).


/*
main(!IO):-
    
	action(
	    "initial-state",
	    [],
	    [on(a, table), on(b, table), on(c, a), clear(b), clear(c)],
	    []),
	action(
	    "goal-state",
	    [on(a, b), on(b, c)],
	    [],
	    [])
	]),
    poset.add("initial-state", "goal-state", poset.init, NullOrder),
    NullPlan = plan(NullAction, NullOrder, set.init),
    Closure = {"initial-state", "goal-state"},
    Agenda = [{on(b, c), "goal-state"}, {on(a, b), "goal-state"} ],
    (if
	pop(Agenda, Closure, NullPlan, plan(_, OutOrder, _))
    then
	poset.to_total(OutOrder, OutPlan),
	print(OutPlan, !IO),
	nl(!IO),
	nl(!IO),
	print(OutOrder, !IO)
    else
	write("No solution found.", !IO),
	nl(!IO)
    ).
*/	
