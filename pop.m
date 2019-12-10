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


%aside from verify link etc, I feel like I have inlined almost everything I could have here.
%should I inline the bfs portion here as well? lets think about pros and cons.
%pros:  dont need to switch between 2 files to understand execution flow of my program.
%cons: bfs is actually a very nice abstraction, and one that is unlikely to ever leak

%ok I wont for now unles I will have a very good reason to later on


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


%I feel like this is discrete enough, it can stay as a separate function.
%What does it do? It binds an operator. I get it. No ambiguity here, really.


%fix unifing noncodesignant inefficiency
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

%hint: a good way to solve it would have been to use the solutons predicate to find all link threats, and then simple solve them. The upside of that would have been that this would allow me to inline this function into the main pop predicate later (this would have been difficult otherwise).



:- pred verify_link_threat(causal_link, node, node).
:- mode verify_link_threat(in,  in, out) is nondet.
verify_link_threat(causal_link(Add, Need, Q), !Node ):-
    (if
	member(A_t, !.Node ^ plan ^ a),
	Add \= A_t^name,
	Need \= A_t^name,
	member(Q, A_t^effects_remove), 
	poset.orderable(Add, A_t^name, !.Node^plan^o),
	poset.orderable(A_t^name, Need, !.Node^plan^o)
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
	member(Q, Action^effects_remove),
	A_p \= Action^name,
	A_c \= Action^name,
	member(causal_link(A_p, A_c, Q), !.Node^plan^l), 
	poset.orderable(A_p, Action^name, !.Node^plan^o),
	poset.orderable(Action^name, A_c, !.Node^plan^o)
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



        % trace [io(!IO)] (
		%     io.write_string("Ordering ", !IO), 
		%     io.write(Act^name, !IO),
		%     io.nl(!IO),
		%     io.write_string(" <  ", !IO),
		%     io.nl(!IO),
		%     io.write(Ne, !IO),
		%     io.nl(!IO),
		%     io.write_string(" cannot be inserted into poset: ", !IO),
		%     poset.to_total(!.Node ^ plan ^ o, Total),
		%     io.nl(!IO),
		%     io.write(Total, !IO),
		%     io.nl(!IO)
		% ),


	  
%Okay, since I'm on a newer version of mercury now, with all these cool brand new compiler grades, maybe trailing works now. My unfortunate current predicament would be a nice test of this, actually! Lets inset printouts from time to time, and get it sorted out.

%So, its not working for the gripper problem for some reason.
%Turns out, it finds all these possible actions for depth 0 just fine. But when it comes to finding any further, it just doesn't, it finds 0.

%Hmm, I need to think about this. Still, its pretty good I now have this diagnostic system!


pop(Agenda, {Initial, Final}, Operators, Objects, !Plan):-
    Goal = (pred(Node::in) is semidet :- Node = node(_, [])),
    
    Successor = (pred(!.Node::in, !:Node::out) is nondet :-

	Fold = (pred({Q_n, Ne}::in, {Num_old, Set_old}::in, New::out) is semidet:-
	    
	    Lambda = (pred(Out::out) is nondet:-
    Out = {Q_n, Res, IsF, Ne},
    (if
	member(Act, (!.Node ^ plan ^ a)),
	member(Q_n, Act^effects_add),
	poset.orderable(Act^name, Ne, !.Node ^ plan ^ o) %cf
    then
        Res = Act,
	IsF = no
    else
	%All the stuff related to grounding the operator will go here
	member(Operator, Operators),
	member(Term, Operator^free_action^effects_add),
	unify(Term, Q_n, Operator^noncodesignants, sub_init, MGU),
	bind_operator(Operator, Objects, Res, MGU),
	IsF = yes
    )
),
	    solutions_set(Lambda, Set),
		    Count = set.count(Set),
		    (if 
			Count = 0
		    then
			trace [io(!IO)] (
			    io.write_string("Abandoning plan: no possible refinement found for agenda goal ", !IO), 
			    io.write(Q_n, !IO),
			    io.nl(!IO)
			),
			fail %if there is a flaw that cannot be refined, there is no hope
		    else
			true
		    ),
			
	     (if
		 Count < Num_old
	     then
		 New = {Count, Set}
	     else
		 New = {Num_old, Set_old}
	     )
	 ),

	
	list.foldl(Fold, !.Node ^ agenda, {int.max_int, set.init}, {_, SelectedFlaw}),
%	trace [io(!IO)] (io.write(Countie, !IO), io.nl(!IO)),
	member({Q, Action, IsFresh, Need}, SelectedFlaw),	    
	
	%trace [io(!IO)] (io.write(Action^name, !IO), io.nl(!IO)),
	(if 
	    list.delete_first(!.Node ^ agenda, {Q, Need}, Xso)
	then
	    Xso=Xs
	else
	    error("this shouldn't happen")
	),

	    NewLink = causal_link(Action^name, Need, Q),
	    (if
		verify_link_threat(NewLink, !Node) %cf
	    then
		true
	    else
		trace [io(!IO)] (io.write_string("Link threat unresolvable!", !IO), io.nl(!IO)),
		fail),
	    update_L(NewLink, !Node),
	    poset.orderable(Action^name, Need, !.Node ^ plan ^ o), %cf
	update_O(Action^name, Need, !Node),
	
	(if
	    IsFresh = yes
	then
	    poset.orderable(Initial, Action^name, !.Node ^ plan ^ o), %cf
	    poset.orderable(Action^name, Final, !.Node ^ plan ^ o), %cf
	    update_O(Initial, Action^name, !Node),
	    update_O(Action^name, Final, !Node),
	    (if
		verify_action_threat(Action, !Node) %cf
	    then
		true
	    else
		trace [io(!IO)] (io.write_string("Action threat unresolvable!", !IO), io.nl(!IO)),
		fail),
	    update_A(Action, !Node),
	    add_precond_to_agenda(Action^name,
		Action^preconds,
		Xs, NewAgenda),
	    update_Agenda(NewAgenda, !Node)
	      %trace [io(!IO)] ( io.write(NewAgenda, !IO), io.nl(!IO))
	  else
	      
	    update_Agenda(Xs, !Node)
	),
	    %remove this trace once you think you can get a result
	    trace [io(!IO)] (
	 	poset.to_total(!.Node ^ plan ^ o, Total),
	 	io.write(Total, !IO), io.nl(!IO))
     ),

     bfs(node(!.Plan, Agenda), node(!:Plan, _), Successor, Goal).

