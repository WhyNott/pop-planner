:- module poset.
%A naive implementation of a partially ordered set data structure.

:- interface.

:- import_module set.
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


% % A debug variant which outputs the cycle which lead to the poset being considered inconsistent

:- import_module maybe.

:- pred poset.consistent_debug(poset(V)::in, maybe(list(list(V)))::out) is det.


% Determine is X can be consistently ordered before Y
:- pred poset.orderable(V::in, V::in, poset(V)::in) is semidet.




% Return the set of elements that can be ordered before X
:- pred poset.before(V::in, poset(V)::in, set(V)::out) is det.
:- func poset.before(V, poset(V)) = set(V) is det.

%Returns a totally ordered set (list) consistent with the poset

:- pred poset.to_total(poset(V), list(V)).
:- mode poset.to_total(in, out) is det.
%:- mode poset.to_total(in, out) is cc_multi.

%debug only
:- pred poset.debug_to_list(poset(V), list({V, V})).
:- mode poset.debug_to_list(in, out) is det.



:- implementation.
:- import_module list.
:- import_module solutions.
:- import_module maybe.
:- import_module cycle_detector.

:- type poset(V) == set({V, V}).


debug_to_list(Poset, List):-
    set.to_sorted_list(Poset, List).




init(set.init).



init = set.init.


add(A, B, Poset, set.insert(Poset, {A, B})).

add(A, B, Poset) = set.insert(Poset, {A, B}).


:- pred extract_verts(list({V, V}), set(V), set(V)).
:- mode extract_verts(in, in, out) is det.

extract_verts(Data, !Sets):-
    (if
	Data = [{A, B}|Xs]
    then
	set.insert(A, !Sets),
	set.insert(B, !Sets),
	extract_verts(Xs, !Sets)
    else
	!.Sets = !:Sets
    ).



consistent(Poset):-
    extract_verts(set.to_sorted_list(Poset), set.init, Verts),
    cycle_detector.tarjan(set.to_sorted_list(Verts), set.to_sorted_list(Poset), no).

consistent_debug(Poset, Output):-
    extract_verts(set.to_sorted_list(Poset), set.init, Verts),
    cycle_detector.tarjan(set.to_sorted_list(Verts), set.to_sorted_list(Poset), Output).


:- pred known_after(list({V, V}), V, V).
:- mode known_after(in, in, in) is semidet.
:- mode known_after(in, in, out) is nondet.

known_after(Data, X1, X2):-
    (list.member({X1, X2}, Data)
;
    list.member({X1, Mid1}, Data),
    list.member({Mid2, X2}, Data),
    (Mid1 = Mid2; known_after(Data, Mid1, Mid2))).

:- pred poset.orderable_before(V, V, poset(V)).
:- mode poset.orderable_before(out, in, in) is nondet.

orderable_before(A, B, Poset):-
    extract_verts(set.to_sorted_list(Poset), set.init, Verts),
    member(A, Verts),
    \+ known_after(set.to_sorted_list(Poset), B, A).

orderable(A, B, Poset):-
    add(A, B, Poset, PosetOut),
    consistent(PosetOut).
    %\+ known_after(set.to_sorted_list(Poset), B, A).




before(X, Poset, Set):-
    Lambda = (pred(A::out) is nondet:-
	orderable_before(A, X, Poset), A \= X),
    solutions_set(Lambda, Set).

before(X, Poset) = Set :- before(X, Poset, Set).


to_total(Poset, OutList):-
    extract_verts(set.to_sorted_list(Poset), set.init, Verts),
    List = set.to_sorted_list(Verts),
    i_sort(Poset, List,[], OutList).




    %code stolen from http://kti.mff.cuni.cz/~bartak/prolog/sorting.html
    
:- pred i_sort(poset(V), list.list(V), list.list(V), list.list(V)).
:- mode i_sort(in, in, in, out) is det.

i_sort(Poset, List,Acc,Sorted):-
    (if
	List = [H|T]
    then
	insert(Poset, H,Acc,NAcc),i_sort(Poset, T,NAcc,Sorted)
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

