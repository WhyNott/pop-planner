:- module planner_data_structures.
:- interface.
:- import_module logic.
:- import_module list.
:- type action_name == logic.name.

:- type ground_literal == logic.disjunct.

:- type action ---> action(
    name :: action_name,
    preconds :: list(disjunct),
    effects_add :: list(disjunct),
    effects_remove :: list(disjunct)
).

:- type operator ---> operator(
    free_action :: action,
    noncodesignants :: list({object, object}) %it means variables that shouldn't be the same thing
).

:- type domain ---> domain(
    operators :: list(operator),
    objects :: list(logic.object),
    initial :: list(logic.disjunct),
    goal :: list(logic.disjunct)
).
