:- module pop.
:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is cc_multi.

:- implementation.
:- import_module list.
:- import_module int.
:- import_module set.
:- import_module solutions.
:- import_module maybe.
:- include_module pop.poset.
:- import_module pop.poset.
:- import_module require.

%Note: its stuck in (what feels like) an infinite loop now.

:- type object
         ---> a
         ;      b
	 ;      c    
	 ;      table.    
	     
:- type ground_literal
         ---> on(object, object)
         ;      clear(object).

%once string comparison becomes too unbearable, change to discriminated union of all the names
:- type action_name == string.

:- type action 
         ---> action(
	     name :: action_name,
	     preconditions :: list(ground_literal),
	     add :: list(ground_literal),
	     remove :: list(ground_literal)
	 ).

:- type causal_link
         ---> causal_link(
	     producer :: action_name,
	     consumer :: action_name,
	     proposition :: ground_literal
	 ).

	     
	     
:- type plan == {set(action), poset(action_name), set(causal_link)}.
:- type agenda == list({ground_literal, action_name}).



:- func actions = list.list(action).
actions = [
    action(%
	"move-B-from-T-to-C",
	[clear(c), on(b, table), clear(b)],
	[on(b, c)],
	[on(b, table), clear(c)]),
     action(%
	"move-A-from-T-to-B",
	[on(a, table), clear(a), clear(b)],
	[on(a, b)],
	[on(a, table), clear(b)]),
    action(
    	"move-A-from-B-to-C",
    	[on(a, b), clear(a), clear(c)],
    	[on(a, c), clear(b)],
    	[on(a, b), clear(c)]),
    action(
    	"move-A-from-C-to-B",
    	[on(a, c), clear(a), clear(b)],
    	[on(a, b), clear(c)],
    	[on(a, c), clear(b)]),
    action(
    	"move-A-from-C-to-T",
    	[on(a, c), clear(a)],
    	[on(a, table), clear(c)],
    	[on(a, c)]),
    action(
    	"move-A-from-B-to-T",
    	[on(a, b), clear(a)],
    	[on(a, table), clear(b)],
    	[on(a, b)]),
    action(
    	"move-B-from-A-to-C",
    	[on(b, a), clear(b), clear(c)],
    	[on(b, c), clear(a)],
    	[on(b, a), clear(c)]),
    action(
    	"move-B-from-C-to-A",
    	[on(b, c), clear(b), clear(a)],
    	[on(b, a), clear(c)],
    	[on(b, c), clear(a)]),
    action(
    	"move-B-from-A-to-T",
    	[on(b, a), clear(b)],
    	[on(b, table), clear(a)],
    	[on(b, a)]), %uncomment me for the slowdown
    action(
    	"move-B-from-C-to-T",
    	[on(b, c), clear(b)],
    	[on(b, table), clear(c)],
    	[on(b, c)]),
    action(
    	"move-C-from-A-to-B",
    	[on(c, a), clear(c), clear(b)],
    	[on(c, b), clear(a)],
    	[on(c, a), clear(b)]),
    action(
    	"move-C-from-B-to-A",
    	[on(c, b), clear(c), clear(a)],
    	[on(c, a), clear(b)],
    	[on(c, b), clear(a)]),
    action(
    	"move-C-from-B-to-T",
    	[on(c, b), clear(c)],
    	[on(c, table), clear(b)],
    	[on(c, b)]),

    action(%
	"move-C-from-A-to-T",
	[on(c, a), clear(c)],
	[on(c, table), clear(a)],
	[on(c, a)]),
    
    
    action(
    	"move-A-from-T-to-C",
    	[on(a, table), clear(a), clear(c)],
    	[on(a, c)],
    	[on(a, table), clear(c)]),
    action(
    	"move-B-from-T-to-A",
    	[on(b, table), clear(b), clear(a)],
    	[on(b, a)],
    	[on(b, table), clear(a)]),
    action(
    	"move-C-from-T-to-A",
    	[on(c, table), clear(c), clear(a)],
    	[on(c, a)],
    	[on(c, table), clear(a)]),
    action(
    	"move-C-from-T-to-B",
    	[on(c, table), clear(c), clear(b)],
    	[on(c, b)],
    	[on(c, table), clear(b)])
    ].
 

:- pred providers(pop.ground_literal, set(pop.action), list.list(pop.action), action_name).
:- mode providers(in, in, in, out) is nondet.
providers(Q, A, Domain, Result):-
    (if
	member(Action, A),
	member(Q, add(Action))
    then
	Result = name(Action)
    else
	member(Action, Domain),
	member(Q, add(Action)),
	Result = name(Action)
    ).

:- pred establish_action_order(action_name, action_name, {action_name, action_name}, pop.poset.poset(action_name), pop.poset.poset(action_name)).
:- mode establish_action_order(in, in, in, in, out) is det.
establish_action_order(Add, Need, {FirstA, LastA}, !Order):-
    poset.add(Add, Need, !Order),
    poset.add(FirstA, Add, !Order),
    poset.add(Add, LastA, !Order).
	
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
    member(Q, remove(A_t)), 
    poset.orderable(A_p, name(A_t), Order),
    poset.orderable(name(A_t), A_c, Order).

:- pred action_threathens(action, poset(action_name), set(causal_link), action_name, action_name).
:- mode action_threathens(in, in, in, out, out) is nondet.
action_threathens(A_t, Order, Links, A_p, A_c):-
    member(Q, remove(A_t)),
    A_p \= A_t^name,
    A_c \= A_t^name,
    member(causal_link(A_p, A_c, Q), Links), 
    poset.orderable(A_p, name(A_t), Order),
    poset.orderable(name(A_t), A_c, Order).

:- pred fix_constraint(action_name, action_name, action_name, pop.poset.poset(action_name), pop.poset.poset(action_name)).
:- mode fix_constraint(in, in, in, in, out) is nondet.
fix_constraint(A_p, A_t, A_c, !Order):-
    poset.orderable(A_t, A_p, !.Order),
    poset.add(A_t, A_p, !Order)
    ;
    poset.orderable(A_c, A_t, !.Order),
    poset.add(A_c, A_t, !Order).

:- pred verify_link_threat(pop.causal_link, set.set(pop.action), pop.poset.poset(string), pop.poset.poset(string)).
:- mode verify_link_threat(in, in, in, out) is nondet.
verify_link_threat(causal_link(Add, Need, Q), Actions, !Order ):-
    (if
	link_threathens(causal_link(Add, Need, Q), !.Order, Actions, A_t)
	then
	    fix_constraint(Add, name(A_t), Need, !Order)
	else
	    !.Order = !:Order
	).

:- pred add_new_action(string, {string, string}, list.list({pop.ground_literal, string}), list.list({pop.ground_literal, string}), {set.set(pop.action), pop.poset.poset(string), set.set(pop.causal_link)}, {set.set(pop.action), pop.poset.poset(string), set.set(pop.causal_link)}).
:- mode add_new_action(in, in, in, out, in, out) is nondet.

add_new_action(Need, Closure, !Agenda, !Plan):-
    !.Plan = {A_old, O_old, L},
    !:Plan = {A_new, O_new, L},
    member(Full_Add, actions), 
    name(Full_Add) = Add, 
    set.insert(Full_Add, A_old, A_new), 
    %new action instance added to A
    establish_action_order(Add, Need, Closure, O_old, O_mid),
    add_precond_to_agenda(Add, preconditions(Full_Add), !.Agenda, !:Agenda),
    (if
	action_threathens(Full_Add, O_mid, L, A_p, A_c)
    then
	fix_constraint(A_p, Add, A_c, O_mid, O_new) 
    else
	O_new = O_mid
    ).



:- pred pop(int, agenda, set({agenda, plan}), {action_name, action_name}, plan, plan).


%:- pragma minimal_model(pop/4).


%There is an infinite loop in here, somewhere.
%I have no clue as to what is causing it. I should get a break from this for a while.
%After a break, I still don't know. But worry not, I shall find out.
:- mode pop(in, in, in, in, in, out) is nondet.
pop(Depth, Agenda, PastPlans, Closure, !Plan):-
    (if
	Depth > 0
    then
	!.Plan = {Actions, Order, Links},
	(if
	    Agenda = [{Q, Need}|Xs]
	then
	    providers(Q, Actions, actions, Add),
	    NewLink = causal_link(Add, Need, Q),
	    set.insert(NewLink, Links, L_1), %L_New = L_1
	    poset.orderable(Add, Need, Order),  
	    poset.add(Add, Need, Order, O_1),
	    verify_link_threat(NewLink, Actions, O_1, O_2),
	    (if
		%if A is a new action
		not (member(Full_Add, Actions), name(Full_Add) = Add)
	    then
		add_new_action(Need, Closure, Xs, Ag_New, {Actions, O_2, L_1}, NewPlan)
	    else
		%just plumbing
		Xs = Ag_New,
		NewPlan = {Actions, O_2, L_1}
            ),
	    
		\+ member({Ag_New, NewPlan}, PastPlans),
		set.insert({Ag_New, NewPlan}, PastPlans, NewRecord),
		pop(Depth-1, Ag_New, NewRecord, Closure, NewPlan,!:Plan) 		
	    else %this is an optional assert and could be removed completely
		(if % *all conjuncts of every action's precondition need to be supported by causal links*
		    (member(A, Actions), member(Q, preconditions(A))) => member(causal_link(_, _, Q), Links) 
		then
		    !.Plan = !:Plan
		else
		    error("Something is up with the algorithm")
		)
	    )
	else
	    fail).

:- pred pop_wrap(list.list({pop.ground_literal, string}), {string, string}, {set.set(pop.action), pop.poset.poset(string), set.set(pop.causal_link)}, {set.set(pop.action), pop.poset.poset(string), set.set(pop.causal_link)}).
:- mode pop_wrap(in, in, in, out) is nondet.
pop_wrap(Agenda, Closure, !Plan):-
    nondet_int_in_range(6, 12, Depth),
    pop(Depth, Agenda, set.init, Closure, !Plan).

main(!IO):-
    NullAction = set.from_list([
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
    NullPlan = {NullAction, NullOrder, set.init},
    Closure = {"initial-state", "goal-state"},
    Agenda = [{on(b, c), "goal-state"}, {on(a, b), "goal-state"} ],
    (if
	pop_wrap(Agenda, Closure, NullPlan, {_, OutOrder, _})
	%poset.orderable("move-B-from-T-to-C", "move-A-from-T-to-C", OutOrder)
	%only generates the correct answer once the constraint above constraints are added - suggests there is something wrong with my poset implementation
	
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
	
