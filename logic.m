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


:- type disjunct.
:- instance unifiable(disjunct).
:- func disjunct(string, list(object)) = disjunct.
:- mode disjunct(in, in) = out is det.
:- mode disjunct(out, out) = in is det.

:- type name.
:- instance unifiable(name).
:- func name(string, list(object)) = name.
:- mode name(in, in) = out is det.
:- mode name(out, out) = in is det.

:- type object.
:- instance unifiable(object).
:- func object(string) = object.
:- mode object(in) = out is det.
:- mode object(out) = in is det.



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

:- typeclass unifiable(D) where [
func to_term(D) = term.term,
func from_term(term.term) = D
].

:- type disjunct ---> d(dt :: term).
:- instance unifiable(disjunct) where [
func(to_term/1) is dis_to_term,
func(from_term/1) is dis_from_term
].
:- func dis_to_term(disjunct) = term.
:- mode dis_to_term(in) = out is det.
dis_to_term(Dis) = Dis^dt.

:- func dis_from_term(term) = disjunct.
:- mode dis_from_term(in) = out is det.
dis_from_term(Term) = d(Term).


:- type name ---> n(nt :: term).
:- instance unifiable(name) where [
func(to_term/1) is name_to_term,
func(from_term/1) is name_from_term
].
:- func name_to_term(name) = term.
:- mode name_to_term(in) = out is det.
name_to_term(Name) = Name^nt.

:- func name_from_term(term) = name.
:- mode name_from_term(in) = out is det.
name_from_term(Term) = n(Term).


:- type object ---> o(ot :: term).
:- instance unifiable(object) where [
func(to_term/1) is object_to_term,
func(from_term/1) is object_from_term
].
:- func object_to_term(object) = term.
:- mode object_to_term(in) = out is det.
object_to_term(Object) = Object^ot.

:- func object_from_term(term) = object.
:- mode object_from_term(in) = out is det.
object_from_term(Term) = o(Term).


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
    

%object_to_term_list(



%I call this design pattern "pseudoconstructor".
%Is it a pattern, or an anti-pattern?

name(Name, Vars) = X :- name(Name, Vars,  X).

:- pred name(string, list(object), name).
:- mode name(in, in, out) is det.
:- mode name(out, out, in) is det.
:- pragma promise_equivalent_clauses(name/3).

name(Name::in, Vars::in, X::out) :-
    X = n(functor(atom(Name), list.map(object_to_term,Vars), ct_name)).

name(Name::out, Vars::out, X::in) :-
    (if
	X = n(functor(atom(N), V, ct_name))
    then
	N = Name,
	Vars = list.map(object_from_term, V)
    else
	error("attempted to unify name with a term that is not a name.")
    ).


object(Object) = X :- object(Object, X).

:- pred object(string, object).
:- mode object(in,  out) is det.
:- mode object(out,  in) is det.
:- pragma promise_equivalent_clauses(object/2).

object(Object::in, X::out) :-
    X = o(functor(atom(Object), [], ct_object)).

object(Object::out,  X::in) :-
    (if
	X = o(functor(atom(N), [], ct_object))
    then
	N = Object
    else
	error("attempted to unify object with a term that is not an object.")
    ).


disjunct(Disjunct, Objs) = X :- disjunct(Disjunct, Objs,  X).

:- pred disjunct(string, list(object), disjunct).
:- mode disjunct(in, in, out) is det.
:- mode disjunct(out, out, in) is det.
:- pragma promise_equivalent_clauses(disjunct/3).

disjunct(Disjunct::in, Objs::in, X::out) :-
    X = d(functor(atom(Disjunct), list.map(object_to_term,Objs), ct_disjunct)).

disjunct(Disjunct::out, Objs::out, X::in) :-
    (if
	X = d(functor(atom(N), V, ct_disjunct))
    then
	N = Disjunct,
	Objs = list.map(object_from_term, V)
    else
	error("attempted to unify disjunct with a term that is not a disjunct.")
    ).



create_wrap_var(object_from_term(variable(Var, ct_variable)), !Supply):-
    create_var(Var, !Supply).


init_var_supply = term.init_var_supply : term.var_supply(term.generic).

:- import_module varset.
:- import_module term_io.

write(Item, !IO):-
    V = varset.init,
    term_io.write_term(V, to_term(Item), !IO).
