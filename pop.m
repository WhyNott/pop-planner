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



:- func actions = list.list(action).
actions = [
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
    
    action(%
	"move-A-from-T-to-B",
	[on(a, table), clear(a), clear(b)],
	[on(a, b)],
	[on(a, table), clear(b)]),
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
    action(%
	"move-B-from-T-to-C",
	[on(b, table), clear(b), clear(c)],
	[on(b, c)],
	[on(b, table), clear(c)]),
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
    member(Q, remove(A_t)),
    poset.orderable(A_p, name(A_t), Order),
    poset.orderable(name(A_t), A_c, Order).

:- pred action_threathens(action, poset(action_name), set(causal_link), action_name, action_name).
:- mode action_threathens(in, in, in, out, out) is nondet.
action_threathens(A_t, Order, Links, A_p, A_c):-
    member(Q, remove(A_t)),
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
	
:- pred pop(list.list({pop.ground_literal, action_name}), {action_name, action_name}, {set(pop.action), pop.poset.poset(action_name), set(pop.causal_link)}, {set(pop.action), pop.poset.poset(action_name), set(pop.causal_link)}).
:- mode pop(in, in, in, out) is cc_nondet.
pop(Agenda, Closure, !Plan):-
    (if
	Agenda = [{Q, Need}|Xs]
    then
	!.Plan = {Actions, Order, Links},
	providers(Q, Actions, actions, Add),
	set.insert(causal_link(Add, Need, Q), Links, L_New),
	(if
	    link_threathens(causal_link(Add, Need, Q), Order, Actions, A_t)
	then
	    fix_constraint(Add, name(A_t), Need, Order, O_mid)
	else
	    Order = O_mid
	),
	(if
	    member(Full_Add, Actions),
	    name(Full_Add) = Add
	then
	    A_New = Actions,
	    Ag_New = Xs,
	    poset.add(Add, Need, O_mid, O_New)
	else
	    member(Full_Add, actions),
	    name(Full_Add) = Add,
	    set.insert(Full_Add, Actions, A_New),
	    (if
		action_threathens(Full_Add, O_mid, L_New, A_p, A_c)
	    then
		fix_constraint(A_p, Add, A_c, O_mid, O_mid2)
	    else
		O_mid2 = O_mid
	    ),
		
	    %new action instance added to A
	    establish_action_order(Add, Need, Closure, O_mid2, O_New),
	    add_precond_to_agenda(Add, preconditions(Full_Add), Agenda, Ag_New)
		
	    ),
            pop(Ag_New, Closure, {A_New, O_New, L_New}, !:Plan) 		
	    else
		!.Plan = !:Plan
	    ).
		




% :- pred regws_wrap(set(ground_literal), set(ground_literal), set(set(ground_literal)), list(regws.action), maybe(list(regws.action)), maybe(list(regws.action))).
% :- mode regws_wrap(in, in, in, in, in, out) is nondet.
% :- mode regws_wrap(in, in, in, in, in, out) is cc_nondet.

% regws_wrap(InitState, CurGoals, PastGoals, Actions, !Path):-
%     nondet_int_in_range(1, 12, Depth),
%     regws(Depth, InitState, CurGoals, PastGoals, Actions, !Path).

% :- pred regws(int, set(ground_literal), set(ground_literal), set(set(ground_literal)), list(regws.action), maybe(list(regws.action)), maybe(list(regws.action))).
% :- mode regws(in, in, in, in, in, in, out) is nondet.
% :- mode regws(in, in, in, in, in, in, out) is cc_nondet.

% regws(Depth, InitState, CurGoals, PastGoals, Actions, !Path):-
%     (if
% 	Depth > 0
%     then	
% 	(if
% 	    set.subset(CurGoals, InitState)
% 	then
% 	    !.Path = !:Path
% 	else
% 	    (if
% 		member(Act, Actions),
% 		some [X] (member(X, add(Act)), member(X, CurGoals)),
% 		\+ (some [Y] (member(Y, remove(Act)), member(Y, CurGoals))),
% 		!.Path = yes(PathSoFar)
% 	then
% 	    delete_list(add(Act), CurGoals, Mid),
% 	    insert_list(preconditions(Act), Mid, G),
% 	    \+ member(G, PastGoals),
	    
% 	    regws(Depth-1, InitState, G, set.insert(PastGoals, G), Actions, yes([Act|PathSoFar]), !:Path)
% 	else
% 	    !:Path = no))
% 	else
% 	    fail).





:- pred printPath(list.list(action), io.state, io.state).
:- mode printPath(in, di, uo) is det. 
printPath(Path, !IO):-
    (if
	Path = [Head|Tail]
    then
	print(name(Head), !IO),
	nl(!IO),
	printPath(Tail, !IO)
    else
	print("End", !IO)).




main(!IO).% :-
    % (if
    % 	regws_wrap(set.from_list([on(a, table), on(b, table), on(c, a), clear(b), clear(c)]), set.from_list([on(a, b), on(b, c)]), set.init, actions, yes([]), Path),
    % 	Path = yes(ActualPath)
    % then
    % 	printPath(ActualPath, !IO)
    % else
    % 	write("No path found.", !IO),
    % 	nl(!IO)
    % ).
