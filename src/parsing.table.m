%-----------------------------------------------------------------------%
% vim: ts=4 sw=4 et
%-----------------------------------------------------------------------%
:- module parsing.table.
%
% Table for LL parser.
%
% Copyright (C) 2015 Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
%-----------------------------------------------------------------------%
:- interface.

:- type table(T, NT, TE).

:- func init = table(T, NT, TE).

:- pred table_insert(NT::in, T::in, maybe(T)::in, TE::in,
    table(T, NT, TE)::in, table(T, NT, TE)::out) is det.

:- pred table_search(table(T, NT, TE)::in, NT::in, T::in, T::in, TE::out)
    is semidet.

    % Get the set of terminals that are valid for this non-terminal.  This
    % allows the parser to inform the user which terminals it may have
    % expected when it recieved a non-matching terminal and NT was on the
    % top of the stack.
    %
:- pred table_valid_terminals(table(T, NT, TE)::in, NT::in,
    list(T)::out) is det.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

:- import_module map.

:- type table(T, NT, TE)
    --->    table(
                t_map       :: map({NT, T}, table_node(T, TE)),
                t_nt_map    :: map(NT, list(T))
            ).

:- type table_node(T, TE)
    --->    leaf(TE)
    ;       branch(map(T, TE)).

init = table(map.init, map.init).

table_insert(NT, T1, MaybeT2, Entry, Table@table(Map0, NTMap0),
        table(Map, NTMap)) :-
    ( MaybeT2 = yes(T2),
        ( if search(Map0, {NT, T1}, Branch0) then
            ( Branch0 = leaf(_),
                unexpected($file, $pred, "Overlapping table entries")
            ; Branch0 = branch(IMap0)
            ),
            det_insert(T2, Entry, IMap0, IMap),
            Branch = branch(IMap),
            det_update({NT, T1}, Branch, Map0, Map)
        else
            det_insert(T2, Entry, map.init, IMap),
            det_insert({NT, T1}, branch(IMap), Map0, Map)
        )
    ; MaybeT2 = no,
        det_insert({NT, T1}, leaf(Entry), Map0, Map)
    ),
    % TODO: make this a set.
    table_valid_terminals(Table, NT, Ts0),
    Ts = [T1 | Ts0],
    set(NT, Ts, NTMap0, NTMap).

table_search(Table, NT, T1, T2, Entry) :-
    search(Table ^ t_map, {NT, T1}, Branch),
    ( Branch = leaf(Entry)
    ; Branch = branch(Map2),
        search(Map2, T2, Entry)
    ).

table_valid_terminals(Table, NT, Ts) :-
    ( if search(Table ^ t_nt_map, NT, TsPrime) then
        Ts = TsPrime
    else
        Ts = []
    ).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
