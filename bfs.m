:- module bfs.
:- interface.
:- import_module list.

:- mode successor == in(pred((ground >> ground), (free >> ground)) is nondet).
:- mode goal == in((pred((ground >> ground)) is semidet)).    


:- pred bfs_path(Node, list.list(Node), pred(Node, Node), (pred Node)).
:- mode bfs_path(in, out, successor, goal) is nondet.

:- pred bfs(Node, Node, pred(Node, Node), (pred Node)).
:- mode bfs(in, out, successor, goal) is nondet.


%Breath First Search implementation
%Loosely adapted from https://www.csee.umbc.edu/courses/771/current/presentations/prolog%20search.pdf

:- implementation.

:- import_module list.
:- import_module queue.
:- import_module solutions.
:- import_module io.
:- import_module int.
:- import_module bool.

bfs_path(S, Path, Successor, GoalEv):-
    queue.init(Q1),
    queue.put_on_front([S], Q1, Q2),
    bfs_path1(Q2, Path, Successor, GoalEv).


:- pred bfs_path1(queue.queue(list.list(Node)), list.list(Node), pred(Node, Node), (pred Node)).
:- mode bfs_path1(in, out, successor, goal). 

bfs_path1(Q1, Solution, Arc, GoalEv):-
    (if
	queue.first(Q1, [S|Tail]),
	Arc(S, G),
	GoalEv(G)
    then
	Solution = [G, S|Tail]
    else
	queue.get([S|Tail], Q1, Q2),
	Lambda = (pred(X::out) is nondet :-
	    Arc(S,Succ), \+member(Succ,Tail),
	    X = [Succ,S|Tail]
	),
	solutions(Lambda, NewPaths), 
	queue.put_list(NewPaths, Q2, Q3),
	bfs_path1(Q3, Solution, Arc, GoalEv)
    ).


bfs(S, Goal, Successor, GoalEv):-
    (if
	GoalEv(S)
    then
	Goal = S
    else
	queue.init(Q1),
	queue.put_on_front([S], Q1, Q2),
	bfs1(Q2, Goal, Successor, GoalEv)
    ).

:- mutable(depth, int, 0, ground, [untrailed]).


%TODO: change bfs1 so that it generates the solutons first, and then uses them both to verify if a goal is reacheable and to add them to the queue for later.

:- pred bfs1(queue.queue(list.list(Node)), Node, pred(Node, Node), (pred Node)).
:- mode bfs1(in, out, successor, goal) is nondet. 
bfs1(Q1, Goal, Arc, GoalEv):-
    (if
	queue.first(Q1, [S|_]),
	Arc(S, G),
	GoalEv(G)
    then

	%###
	trace [io(!IO)] (
		io.write_string("Goal located!", !IO), io.nl(!IO)

	),
	%###

	Goal = G
    else
	queue.get([S|Tail], Q1, Q2), %this part can fail if queue is empty
	Lambda = (pred(X::out) is nondet :-
	    Arc(S, Succ), \+ member(Succ, Tail),
	    X = [Succ, S|Tail]
	),
	solutions(Lambda, NewPaths),

	queue.put_list(NewPaths, Q2, Q3),

	%###    
	trace [io(!IO), state(depth, !Depth)] (
	    NewNodes = list.length(NewPaths):int,
	    io.write(NewNodes, !IO),
	    io.write_string(" new refinements found", !IO),
	    io.nl(!IO),
	    io.write_string("Total: ", !IO),
	    io.write(queue.length(Q3):int, !IO),
	    io.write_string(" plans on level ", !IO),
	    io.write(!.Depth, !IO),
	    io.nl(!IO),

	    (if
		NewNodes = 0
	    then
		!:Depth = !.Depth
	    else
		!:Depth = !.Depth + 1
	    )
	),
	%###
	    
	    

	bfs1(Q3, Goal, Arc, GoalEv)
    ).


