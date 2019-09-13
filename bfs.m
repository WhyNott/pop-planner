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
    queue.init(Q1),
    queue.put_on_front([S], Q1, Q2),
    bfs1(Q2, Goal, Successor, GoalEv).


:- pred bfs1(queue.queue(list.list(Node)), Node, pred(Node, Node), (pred Node)).
:- mode bfs1(in, out, successor, goal). 
bfs1(Q1, Goal, Arc, GoalEv):-
    (if
	queue.first(Q1, [S|_]),
	Arc(S, G),
	GoalEv(G)
    then
	Goal = G
    else
	queue.get([S|Tail], Q1, Q2),
	Lambda = (pred(X::out) is nondet :-
	    Arc(S, Succ), \+ member(Succ, Tail),
	    X = [Succ, S|Tail]
	),
	solutions(Lambda, NewPaths),    
	queue.put_list(NewPaths, Q2, Q3),
	bfs1(Q3, Goal, Arc, GoalEv)
    ).

