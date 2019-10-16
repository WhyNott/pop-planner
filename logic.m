:- module logic.
%A module for data structures used in representing planning.
:- interface.

:- import_module list.
%Haha, this is so simple! 


% OOP best practice, or an overengineered mess? Ill let you decide.
% This was supposed to be just a simple wrapper for the messy 'term' library.. I am not sure if I actually succeeded in reducing complexity...

:- typeclass unifiable(D).

:- pred unify(D, D, list({O, O}), logic.substitution, logic.substitution) <= (unifiable(D), unifiable(O)).
:- mode unify(in, in, in, in, out) is semidet.


:- type disjunct ---> disjunct(string, list(object)).
:- instance unifiable(disjunct).


:- type name ---> name(string, list(object)).
:- instance unifiable(name).

:- type var.

:- type object ---> object(string);
             variable(var).
:- instance unifiable(object).

%disjunct, name, object

:- type substitution.
:- func sub_init = logic.substitution.
:- func apply_sub_to_list(list(D), logic.substitution) = list(D) <= unifiable(D).
:- mode apply_sub_to_list(in, in) = out is det.

:- pred bindings_allowed(list({O, O}), logic.substitution) <= unifiable(O).
:- mode bindings_allowed(in, in) is semidet.

:- type var_supply.
:- func init_var_supply = logic.var_supply.

:- pred create_wrap_var(object, logic.var_supply, logic.var_supply).
:- mode create_wrap_var(out, in, out) is det.


%Printing utilities

%write_term

:- import_module io.
:- pred write(D, io, io) <= unifiable(D) .
:- mode write(in, di, uo) is det.

:- implementation.

:- import_module term.
:- import_module require.
:- import_module map.
:- import_module string.

:- typeclass unifiable(D) where [
func to_term(D) = term.term,
func from_term(term.term) = D
].




:- instance unifiable(disjunct) where [
func(to_term/1) is dis_to_term,
func(from_term/1) is dis_from_term
].
:- func dis_to_term(disjunct) = term.
:- mode dis_to_term(in) = out is det.
dis_to_term(disjunct(String, List)) = functor(atom(String), list.map(object_to_term,List), ct_disjunct).

:- func dis_from_term(term) = disjunct.
:- mode dis_from_term(in) = out is det.
dis_from_term(Term) = disjunct(String, list.map(object_from_term, List)) :-
    (if
	Term = functor(atom(S), L, ct_disjunct)
    then
	String = S,
	List = L
    else
	error("could not get a disjunct from a given term")
    ).



:- instance unifiable(name) where [
func(to_term/1) is name_to_term,
func(from_term/1) is name_from_term
].
:- func name_to_term(name) = term.
:- mode name_to_term(in) = out is det.
name_to_term(name(String, List)) = functor(atom(String), list.map(object_to_term,List), ct_name).

:- func name_from_term(term) = name.
:- mode name_from_term(in) = out is det.
name_from_term(Term) = name(String, list.map(object_from_term, List)) :-
    (if
	Term = functor(atom(S), L, ct_name)
    then
	String = S,
	List = L
    else
	error("could not get a name from a given term")
    ).

:- type logic.var == term.var.

:- instance unifiable(object) where [
func(to_term/1) is object_to_term,
func(from_term/1) is object_from_term
].
:- func object_to_term(object) = term.
:- mode object_to_term(in) = out is det.
object_to_term(Input) = Output :-
	Input = object(String),
	Output = functor(atom(String), [], ct_object)
    ;
	Input = variable(Var),
	Output = variable(Var, ct_variable).

:- func object_from_term(term) = object.
:- mode object_from_term(in) = out is det.
object_from_term(Term) = Output :-
    (if
	Term = functor(atom(S), [], ct_object)
    then
	Output = object(S)
    else
	(if
	    Term = variable(Var, ct_variable)
	then
	    Output = variable(Var)
	else
	    error(string.format("could not get an object from term %s", [s(string(Term))]))
	)
    ).


:- type logic.substitution == term.substitution.
:- type logic.var_supply == term.var_supply(term.generic). 



:- func ct_disjunct = term.context.
ct_disjunct = term.context("disjunct", 1).

:- func ct_name = term.context.
ct_name = term.context("name", 2).

:- func ct_object = term.context.
ct_object = term.context("object", 3).

:- func ct_variable = term.context.
ct_variable = term.context("variable", 4).



sub_init = map.init.

unify(X, Y, NC, !MGU):-
    unify_term(to_term(X), to_term(Y), !MGU),
    bindings_allowed(NC, !.MGU).

%Noncodesignants mean that one cannot be assigned to other.
%Steps:
% substitute all values in noncodesignants with MGU
% verify that for that substituted list, there are no equal values 

bindings_allowed(Noncodesignants, MGU):-
    Substituted = list.map((func({X, Y}) = {apply_substitution(to_term(X), MGU),
	apply_substitution(to_term(Y), MGU)}), Noncodesignants) : list({term, term}), 
    \+ (member({A,B}, Substituted), A = B).

apply_sub_to_list(Vars, MGU) = list.map(
    (func(X) = from_term(Y) :- apply_substitution(to_term(X), MGU, Y)), Vars). 
    



create_wrap_var(object_from_term(variable(Var, ct_variable)), !Supply):-
    create_var(Var, !Supply).


init_var_supply = term.init_var_supply : term.var_supply(term.generic).

:- import_module varset.
:- import_module term_io.

write(Item, !IO):-
    V = varset.init,
    term_io.write_term(V, to_term(Item), !IO).
