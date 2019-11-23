:- module cycle_detector.
:- interface.

%:- import_module io.
:- import_module list.
:- import_module maybe.

%:- pred main(io::di, io::uo) is det.

:- pred tarjan(list(V), list({V, V}), maybe(list(list(V)))).
:- mode tarjan(in, in, out) is det.


:- implementation.


:- import_module stack.
:- import_module map.
:- import_module require.
:- import_module int.
:- import_module string. %for the error messages

:- type state(V) == {int, stack(V), map(V, {maybe(int), maybe(int), maybe(int)}), maybe(list(list(V)))}.


/*

%Left in for the sake of testing:

main(!IO):-
    tarjan(["0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "10", "11", "12"],
	[{"0", "5"},
	{"2", "0"},
	{"0", "1"},
	{"2", "3"},
	{"3", "2"},
	{"3", "5"},
	{"4", "2"},
	{"5", "4"},
	{"6", "0"},
	{"6", "9"},
	{"7", "6"},
	{"7", "8"},
	{"8", "7"},
	{"8", "9"},
	{"9", "10"},
	{"9", "11"},
	{"10", "12"},
	{"11", "4"},
	{"11", "12"},
	{"12", "9"}],
	Components),
%Proper clusters should be: [1], [2, 3, 4, 5, 0], [6], [7, 8], [9, 10, 11, 12] 
    
        (if
	Components = yes(Solutions)
    then
	Lambda = (pred(List::in, !.IO::di, !:IO::uo) is det :-	
	    (if
		List = []
	    then
		io.write("Empty solution", !IO),
		io.nl(!IO)
	    else
		io.write_strings(List, !IO),
		io.nl(!IO)
	    )),
		foreach(Solutions, Lambda, !IO)
	    
    else
	io.write("No solution found!", !IO)
    ).

*/

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%    

    %Acessor predicates for manipulating the passed state
    
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    %Index
    
%%%%%%%%%%%%%%%%%%%%    

:-pred update_index(int, state(V), state(V)).
:-mode update_index(in, in, out) is det.

update_index(NewIndex, !State):-
    {_, Stack, Map, Output} = !.State,
    {NewIndex, Stack, Map, Output} = !:State.

:- pred get_index(int, state(V)).
:-mode get_index(out, in) is det. 
get_index(Output, {Output, _, _, _}).

%%%%%%%%%%%%%%%%%%%%

    %Map (per-vertex variables)

%%%%%%%%%%%%%%%%%%%%

:-pred update_vertex_index(int, V, state(V), state(V)).
:-mode update_vertex_index(in, in, in, out) is det.

update_vertex_index(NewIndex, Vertice, !State):-
    Lambda = (pred(NI::in, {_, Lowlink, OnStack}::in, {maybe.yes(NI), Lowlink, OnStack}::out) is det),
    update_vertex(NewIndex, Vertice, Lambda, !State).


:- pred update_vertex_lowlink(int, V, state(V), state(V)).
:-mode update_vertex_lowlink(in, in, in, out) is det.

update_vertex_lowlink(Lowlink, Vertice, !State):-
    Lambda = (pred(NewLowlink::in, {Index, _, OnStack}::in, {Index, maybe.yes(NewLowlink), OnStack}::out) is det),
    update_vertex(Lowlink, Vertice, Lambda, !State).


:- pred update_vertex_onstack(int, V, state(V), state(V)).
:-mode update_vertex_onstack(in, in, in, out) is det.

update_vertex_onstack(OnStack, Vertice,!State):-
    Lambda = (pred(NewOnStack::in, {Index, LowLink, _}::in, {Index, LowLink, maybe.yes(NewOnStack)}::out) is det),
    update_vertex(OnStack, Vertice, Lambda, !State).


:-pred clear_vertex_onstack(V, state(V), state(V)).
:-mode clear_vertex_onstack(in, in, out) is det.

clear_vertex_onstack(Vertice,!State):-
    Lambda = (pred(_::in, {Index, LowLink, _}::in, {Index, LowLink, maybe.no}::out) is det),
    update_vertex(0, Vertice, Lambda, !State).


:- pred update_vertex(int, V, pred(int, {maybe(int), maybe(int), maybe(int)},  {maybe(int), maybe(int), maybe(int)}), state(V), state(V)).
:- mode update_vertex(in, in, di(/* unique */(pred((ground >> ground), (ground >> ground), (free >> ground)) is det)), in, out) is det.

update_vertex(NewValue, Vertice, Lambda, !State):-
    {Index, Stack, OldMap, Output} = !.State,
    {Index, Stack, NewMap, Output} = !:State,
    (if
	map.search(OldMap, Vertice, OldTuple)
    then
	Lambda(NewValue, OldTuple, NewTuple),
	map.det_update(Vertice, NewTuple, OldMap, NewMap)
    else
	Lambda(NewValue, {no, no, no}, NewTuple),
	map.det_insert(Vertice, NewTuple, OldMap, NewMap)
    ).


:- pred get_vertex_index(int, V, state(V)).
:- mode get_vertex_index(out, in, in) is semidet.

get_vertex_index(Index, Vertice, {_, _, Map, _}):-
    map.search(Map, Vertice, {yes(Index), _, _}).


:- pred get_vertex_lowlink(int, V, state(V)).
:- mode get_vertex_lowlink(out, in, in) is semidet.

get_vertex_lowlink(Lowlink, Vertice, {_, _, Map, _}):-
    map.search(Map, Vertice, {_, yes(Lowlink), _}).


:- pred get_vertex_onstack(int, V, state(V)).
:- mode get_vertex_onstack(out, in, in) is semidet.

get_vertex_onstack(OnStack, Vertice, {_, _, Map, _}):-
    map.search(Map, Vertice, {_, _, yes(OnStack)}).


:- pred get_det(int, pred(int, V, state(V)), V, state(V)). 
:- mode get_det(out, di(/* unique */(pred((free >> ground), (ground >> ground), (ground >> ground)) is semidet)), in, in) is det.

get_det(Thing, Lambda, Vertice, State):-
    (if
	Lambda(Actual_Thing, Vertice, State)
    then
	Thing = Actual_Thing
    else
	error_show_map("getting thing failed", State, Vertice)
    ).


%%%%%%%%%%%%%%%%%%%%

    %Stack

%%%%%%%%%%%%%%%%%%%%

:- pred stack_push(V, state(V), state(V)).
:- mode stack_push(in, in, out) is det.

stack_push(New, !State):-
    {Index, OldStack, Map, Output} = !.State,
    stack.push(New, OldStack, NewStack),
    {Index, NewStack, Map, Output} = !:State.


:- pred stack_pop(V, state(V), state(V)).
:- mode stack_pop(out, in, out) is det.

stack_pop(Out, !State):-
    {Index, OldStack, Map, Output} = !.State,
    (if
	stack.pop(Out1, OldStack, NewStack1)
    then
	Out1 = Out,
	NewStack1 = NewStack
    else
	error("Stack is empty and asked to pop")
),
    {Index, NewStack, Map, Output}= !:State.

%%%%%%%%%%%%%%%%%%%%

    %Components

%%%%%%%%%%%%%%%%%%%%

:- pred add_to_output(list(V), state(V), state(V)). 
:- mode add_to_output(in, in, out) is det.

add_to_output(Component, !State):-
    !.State = {Index, Stack, Map, OldOutput},
    !:State = {Index, Stack, Map, yes(NewOutput)},
    (if
	OldOutput = yes(List)
    then
	NewOutput = [Component|List]
    else
	NewOutput = [Component]
    ). 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    %Error handling

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:-pred error_show_map(string::in, state(V)::in, V::in) is erroneous.
error_show_map(String, State, Vertice):-
    State = {_, _, Map, _},
    (if
	map.search(Map, Vertice, {X, Y, Z})
    then
	(if
	    X=yes(XN)
	then
	    X_str = int_to_string(XN)
	else
	    X_str = "no"),
	(if
	    Y=yes(YN)
	then
	    Y_str = int_to_string(YN)
	else
	    Y_str = "no"),
	(if
	    Z=yes(ZN)
	then
	    Z_str = int_to_string(ZN)
	else
	    Z_str = "no")
	
    else
	error(String ++ " {map not initalised for vertice}")
    ),
    ErrorMessage = String ++ " {" ++ X_str ++ " " ++ Y_str ++ " " ++ Z_str ++ "}",
    error(ErrorMessage).
	
    


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    %Loops

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%Turns out I did not need that one
/*
:- pred do_while(pred(V_2, V_1), pred(V_1, V_2), V_1, V_2).
:- mode do_while(in, in, in, out) is det.

do_while(Condition, DoThis, !State):-
    DoThis(!State),
    (if
	Condition(!State)
    then
	do_while(Condition, DoThis, !State)
    else
	true
    ).

*/

:- pred foreach(list.list(V_1), pred(V_1, V_2, V_2), V_2, V_2).
:- mode foreach(in, di( (pred((ground >> ground), (ground >> ground), (free >> ground)) is det)), in, out) is det.
:- mode foreach(in, di( (pred((ground >> ground), (unique >> clobbered), (free >> unique)) is det)), di, uo) is det. %mode for IO

foreach(List, DoThis, !State):-
    (if
	List = [X|Xs]
    then
	DoThis(X, !State),
	foreach(Xs, DoThis, !State)
    else
	true
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

    %Algorithm body

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- pred strongconnect_body1(V, list({V, V}), {V, V}, state(V), state(V)).
:- mode strongconnect_body1(in, in, in, in, out) is det.

strongconnect_body1(Vertex, Edges, {V, W}, !State):-
    (if
	V=Vertex
    then
	(if
	    get_vertex_index(_, W, !.State)
	then
	    (if
		get_vertex_onstack(_, W, !.State)
	    then
		get_det(VLL, get_vertex_lowlink, V, !.State), 
		
		get_det(WI, get_vertex_index, W, !.State),
		min(VLL, WI, Smallest),
		update_vertex_lowlink(Smallest, V, !State)
	    else
		!.State = !:State
	    )
	else
	    strongconnect(Edges, W, !State),
	    get_det(VLL,get_vertex_lowlink, V, !.State),
	    get_det(WI, get_vertex_lowlink, W, !.State),
	    min(VLL, WI, Smallest),
	    update_vertex_lowlink(Smallest, V, !State)
	)
    else
	!.State = !:State
    ).

:- pred strongconnect_body2(list(V), V, state(V), state(V)).
:- mode strongconnect_body2(in, in, in, out) is det.

strongconnect_body2(List, V, !State):-
    stack_pop(W, !State),
    clear_vertex_onstack(W, !State),
    NewList=[W|List],
    (if
	W = V
    then
	(if
	    List \= [] %this clause blocks all single-vertex "cycles"
	then
	    add_to_output(NewList, !State)
	else
	    !.State = !:State
	)
    else
	strongconnect_body2(NewList, V, !State)
    ).


:- pred strongconnect(list({V, V}), V, state(V), state(V)).
:- mode strongconnect(in, in, in, out) is det.

strongconnect(Edges, Vertex, !State):-
    get_index(Index, !.State),
    update_vertex_index(Index, Vertex, !State),
    update_vertex_lowlink(Index, Vertex, !State),
    IndexPlusOne = Index + 1, 
    update_index(IndexPlusOne, !State),
    stack_push(Vertex, !State),
    update_vertex_onstack(1, Vertex, !State),
    Body = strongconnect_body1(Vertex, Edges),
    foreach(Edges, Body, !State),
    (if
	get_vertex_lowlink(VLowlink, Vertex, !.State),
	get_vertex_index(VIndex, Vertex, !.State),
	VLowlink = VIndex
    then
	strongconnect_body2([], Vertex, !State)
    else
	!.State = !:State
    ).
    



:- pred tarjan_body(list({V, V}), V, state(V), state(V)).
:- mode tarjan_body(in, in, in, out) is det.

tarjan_body(Edges, Vertex, !State) :-
	(if
	    get_vertex_index(_, Vertex, !.State)
	then
	    !:State = !.State
	else
	    strongconnect(Edges, Vertex, !State)
	).


tarjan(V, E, Output):-
    %an integer, a stack and a map walk into a bar
    {0, stack.init, map.init, no} = State_init,
    DoThis = tarjan_body(E), 
    foreach(V, DoThis, State_init, State_out),
    {_, _, _, Output} = State_out.


    




