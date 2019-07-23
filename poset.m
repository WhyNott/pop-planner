:- module poset.
%A naive implementation of a partially ordered set data structure.

:- interface.

:- include_module poset.cycle_detector.


:- import_module io.
:- import_module set.

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
% :- import_module list.
% :- import_module maybe.

% :- pred poset.consistent_debug(poset(V)::in, maybe(list(list(V)))::out) is det.


% Determine is X can be consistently ordered before Y
:- pred poset.orderable(V::in, V::in, poset(V)::in) is semidet.




% Return the set of elements that can be ordered before X
:- pred poset.before(V::in, poset(V)::in, set(V)::out) is det.
:- func poset.before(V, poset(V)) = set(V) is det.









:- implementation.
:- import_module list.
:- import_module solutions.
:- import_module maybe.
:- import_module pop.poset.cycle_detector.


:- type poset(V) == list({V, V}).






init([]).



init = [].


add(A, B, Poset, [{A, B}|Poset]).

add(A, B, Poset) = [{A, B}|Poset].


:- pred extract_verts(poset(V), set(V), set(V)).
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
    extract_verts(Poset, set.init, Verts),
    cycle_detector.tarjan(set.to_sorted_list(Verts), Poset, no).

% consistent_debug(Poset, Output):-
%     extract_verts(Poset, set.init, Verts),
%     cycle_detector.tarjan(set.to_sorted_list(Verts), Poset, Output).


:- pred known_after(poset(V), V, V).
:- mode known_after(in, in, in) is semidet.
:- mode known_after(in, in, out) is nondet.

known_after(Data, X1, X2):-
    list.member({X1, X2}, Data)
;
    list.member({X1, Mid1}, Data),
    list.member({Mid2, X2}, Data),
    (Mid1 = Mid2; known_after(Data, Mid1, Mid2)).

:- mode poset.orderable(out, in, in) is nondet.

orderable(A, B, Poset):-
    extract_verts(Poset, set.init, Verts),
    member(A, Verts),
    \+ known_after(Poset, B, A).




before(X, Poset, Set):-
    Lambda = (pred(A::out) is nondet:-
	orderable(A, X, Poset), A \= X),
    solutions_set(Lambda, Set).

before(X, Poset) = Set :- before(X, Poset, Set).
