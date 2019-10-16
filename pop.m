:- module pop.
:- interface.
:- import_module logic.
:- import_module list.
:- import_module set.
:- import_module poset.

:- type action_name == logic.name.

:- type ground_literal == logic.disjunct.

:- type action ---> action(
    name :: action_name,
    preconds :: list(disjunct),
    effects_add :: list(disjunct),
    effects_remove :: list(disjunct)
).
:- type operator ---> operator(
    free_action :: action,
    noncodesignants :: list({object, object}) %it means variables that shouldn't be the same thing
).

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



:- type node ---> node(plan :: plan, agenda :: agenda).

%These node update predicates help make code more readable.
%No more 'O_5', 'L_3', etc. State variables all the way.
%I wish there was a more natural way to do this though.


:- pred update_A(pop.action, pop.node, pop.node).
:- mode update_A(in, in, out) is det.
update_A(Value, OldNode, NewNode):-
    OldNode = node(plan(A, O, L), Agenda),
    NewNode = node(plan(set.insert(A, Value), O, L), Agenda).

:- pred update_O(action_name, action_name, pop.node, pop.node).
:- mode update_O(in, in, in, out) is det.
update_O(Before, After, OldNode, NewNode):-
    OldNode = node(plan(A, O, L), Agenda),
    NewNode = node(plan(A, poset.add(Before, After, O), L), Agenda).

:- pred update_L(pop.causal_link, pop.node, pop.node).
:- mode update_L(in, in, out) is det.
update_L(NewLink, OldNode, NewNode):-
    OldNode = node(plan(A, O, L), Agenda),
    NewNode = node(plan(A, O, set.insert(L, NewLink)), Agenda).

%This one just takes a new agenda altogether.
:- pred update_Agenda(agenda, pop.node, pop.node).
:- mode update_Agenda(in, in, out) is det.
update_Agenda(NewAgenda, OldNode, NewNode):-
    OldNode = node(Plan, _),
    NewNode = node(Plan, NewAgenda).


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
	    Operator^free_action^name = name(Name, Vars),
	    list.foldl(Lambda, Vars, MGU_init, MGU),
	    Action = action(
		name(Name, apply_sub_to_list(Vars, MGU)),
		apply_sub_to_list(Operator^free_action^preconds, MGU),
		apply_sub_to_list(Operator^free_action^effects_add, MGU),
		apply_sub_to_list(Operator^free_action^effects_remove, MGU)
	    ).
%question: 
:- pred get_suitable_action(pop.ground_literal, set(pop.action), list(operator), list(object), action, bool).
:- mode get_suitable_action(in, in, in, in, out, out) is nondet.
get_suitable_action(Q, A, Domain, Objects, Result, IsFresh):-
    (if
	member(Action, A), 
	member(Q, Action^effects_add)
    then
	Result = Action,
	IsFresh = no
    else
	%All the stuff related to grounding the operator will go here
	member(Operator, Domain),
	member(Term, Operator^free_action^effects_add),
	unify(Term, Q, Operator^noncodesignants, sub_init, MGU),
	bind_operator(Operator, Objects, Result, MGU),
	IsFresh = yes
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

:- pred link_threathens(pop.causal_link, poset(action_name), set(pop.action), pop.action).
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

:- pred verify_link_threat(pop.causal_link, pop.node, pop.node).
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

:- pred verify_action_threat(pop.action, pop.node, pop.node).
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

pop(Agenda, {Initial, Final}, Operators, Objects, !Plan):-
    bfs(node(!.Plan, Agenda), node(!:Plan, _), Successor, Goal),
    Goal = (pred(Node::in) is semidet :- Node = node(_, [])),
    
    Successor = (pred(!.Node::in, !:Node::out) is nondet :-
	!.Node ^ agenda = [{Q, Need}|Xs],
	get_suitable_action(Q, (!.Node ^ plan ^ a), Operators, Objects, Action, IsFresh), %cf
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
	)
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
