:- module poset.
%An implementation of a partially ordered set data structure.
%Prioritizes odereability checks over anything else.

:- interface.


:- import_module list.

:- type poset(V).

% Initialize an empty poset.
:- pred poset.init(poset(V)::out) is det.
:- func poset.init = (poset(V)::out) is det.

% Add new constraint to a poset
:- pred poset.add(V::in, V::in, poset(V)::in, poset(V)::out) is det.
:- func poset.add(V, V, poset(V)) = poset(V) is det.



% Determine is the poset is consistent
:- pred poset.consistent(poset(V)::in) is semidet.


% Determine is X can be consistently ordered before Y
:- pred poset.orderable(V::in, V::in, poset(V)::in) is semidet.


% Return the list of elements that are definitely ordered before X
:- pred poset.before(V::in, poset(V)::in, list(V)::out) is det.
:- func poset.before(V, poset(V)) = list(V) is det.

%Returns a totally ordered set (list) consistent with the poset

:- pred poset.to_total(poset(V), list(V)).
:- mode poset.to_total(in, out) is det.
%:- mode poset.to_total(in, out) is cc_multi.






:- implementation.
:- import_module list.

%%This is super ugly. There is no need to use a V -> unit map, I can just use a set and it will have the same exact result. Why didn't I think of it??TODO


% For every vertex (in this case, action) we store a map where the keys are
%all the elements that are preceeded by it (the value can be unit for example).
%When we check if two elements can be ordered one before another, we check if
% an opposite ordering exists and allow it if it doesnt.

% Okay, now what to do when a new ordering X < Y is added? Well, we add X
%to Y node's adjecency map, and then go thorugh all the verticies and if Y is
%in their maps add X there as well (since if verticle Z > Y, then Z is 
%also > X).

% I can implement sorting to total order quite similarly to how I am doing it
%now. Lets assume that '<' in the sorting function means 'not provably >'.

% Actually, I can have it choose nondeterministically to either accept it or
%not. But I'm not sure if I actually need that.

%I'm gonna use an ordinary map for now. I dont feel like messing around 
%with setting up the hashing predicate, and it would ruin my beutiful type
%abstraction. Honestly, mercury needs to have something in way of built-in
%typeclass predicates for basic classes - something like getHash, toString in
%OOP languages.

:- import_module unit.
:- import_module map.
:- import_module set.

:- import_module require.
% I need to change it, so that it also stores a set of all elements in the poset.
:- type poset(V) ---> poset(elems::set(V), order::map(V, map(V, unit))).

%ugh this will require tons of fixing
%and some boilerplate functions

:- pred map_insert(V, map(V, unit.unit), poset.poset(V), poset.poset(V)).
:- mode map_insert(in, in, in, out) is det.
poset.map_insert(Key, Value, poset(E, O), poset(E, ONew)) :-
	map.set(Key, Value, O, ONew).

:- pred set_insert(T, poset.poset(T), poset.poset(T)).
:- mode set_insert(in, in, out) is det.
poset.set_insert(Element, poset(E, O), poset(ENew, O)):-
    set.insert(Element, E, ENew).

:- pred map_values(pred(K, map(K, unit.unit), map(K, unit.unit)), poset.poset(K), poset.poset(K)).
:- mode map_values(di(/* unique */(pred((ground >> ground), (ground >> ground), (free >> ground)) is det)), in, out) is det.
poset.map_values(Pred, poset(E, O), poset(E, ONew)) :-
    map.map_values(Pred, O, ONew).

poset.init(poset(set.init, map.init)).
poset.init = poset(set.init, map.init).

poset.add(A, B, !Poset):-
    (if
	map.search(!.Poset^order, B, Adj_t)
    then
	map.set(A, unit, Adj_t, Adj_new),
	map_insert(B, Adj_new, !Poset)
    else
	map_insert(B, map.singleton(A, unit), !Poset),
	set_insert(B, !Poset)
    ),
    set_insert(A, !Poset),
	%That part here seems like there is some potential for optimisation
	%Or maybe I'm wrong?
    Transform = (pred(_::in, V::in, W::out) is det :-
	(if
	    map.contains(V, B)
	then
	    map.set(A, unit, V, W)
	else
	    V = W
	)
    ),
	    map_values(Transform, !Poset).

poset.add(A, B, In) = Out :- poset.add(A, B, In, Out).


%To check if the poset is consistent, you iterate through the vertices, and for
%each one you verify that none of the elements that is supposed to be ordered
%before it is also ordered after it for some reason. This is a slow method, but
%I only ever use it in the testing suite anyway. 

poset.consistent(Poset):-
    CheckVertices = (pred(B::in, Adj::in, _::in, unit::out) is semidet :-
	CheckAdjecency = (pred(A::in, _::in, _::in, unit::out) is semidet :-
	    \+ poset.contains(B, A, Poset)),
	map.foldl(CheckAdjecency, Adj, unit, _)),
    map.foldl(CheckVertices, Poset^order, unit, _).

%same as poset.consistent but errors out instead of failing
:- import_module string.

:- pred consistent_det(poset.poset(V)).
:- mode consistent_det(in) is det.
poset.consistent_det(Poset):-
    CheckVertices = (pred(B::in, Adj::in, _::in, unit::out) is det :-
	CheckAdjecency = (pred(A::in, _::in, _::in, unit::out) is det :-
	    (if
		poset.contains(B, A, Poset)
	    then
		ErrStr = format("Ordering %s < %s is inconsistent!", [s(string(A)), s(string(B))]),
		error(ErrStr)
	    else
		true
	    )),
	map.foldl(CheckAdjecency, Adj, unit, _)),
    map.foldl(CheckVertices, Poset^order, unit, _).


:- pred contains(V, V, poset(V)).
:- mode contains(in, in, in) is semidet.
poset.contains(A, B, Poset):-
    map.search(Poset^order, B, Adj),
    map.contains(Adj, A).


poset.orderable(A, B, Poset):-
    A \= B,
    \+ contains(B, A, Poset).
    
poset.before(A, Poset, List):-
    (if
	map.search(Poset^order, A, Adj)
    then
	map.keys(Adj, List)
    else
	List = []
    ).

poset.before(A, Poset) = List :- poset.before(A, Poset, List).



poset.to_total(Poset, OutList):-
    i_sort(Poset, set.to_sorted_list(Poset^elems), [], OutList).




%Code stolen from http://kti.mff.cuni.cz/~bartak/prolog/sorting.html
%It's just insertion sort

:- pred i_sort(poset(V), list.list(V), list.list(V), list.list(V)).
:- mode i_sort(in, in, in, out) is det.

i_sort(Poset, List,Acc,Sorted):-
    (if
	List = [H|T]
    then
	insert(Poset, H,Acc,NAcc), i_sort(Poset, T,NAcc,Sorted)
    else
	Acc = Sorted
    ).




:- pred insert(poset(V), V, list.list(V), list.list(V)).
:- mode insert(in, in, in, out) is det.
insert(Poset, X,Acc, Out):-
    (if
	Acc = [Y|T]
    then
	(if
	    poset.orderable(Y, X, Poset)
	then
	    insert(Poset,X,T,NT),
	    Out = [Y|NT]
	else
	    Out = [X,Y|T]
	)
    else
	Out = [X]
    ).

