%-----------------------------------------------------------------------%
% vim: ts=4 sw=4 et
%-----------------------------------------------------------------------%
:- module parsing.gen.
%
% Generate an LL(1) parser.
%
% Copyright (C) 2015 Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
%-----------------------------------------------------------------------%
:- interface.

:- import_module parsing.bnf.

:- func make_parser(bnf(T, NT, R)) = parser(T, NT, R).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

:- import_module require.

%-----------------------------------------------------------------------%

    % This uses the algorithm from
    % https://en.wikipedia.org/wiki/LL_parser#Constructing_an_LL.281.29_parsing_table
    %
    % Some points of clarification.
    %   + the first and follow sets have been typed as set(terminal(T)),
    %     they're stored in maps indexed by non-terminals.
    %   + When building first sets Fi(A) \ {ε} ∪ Fi(w') is assumed to be
    %     (Fi(A) \ {ε}) ∪ Fi(w')
    %   + To support lookahead we also build second sets.
    %
make_parser(bnf(Start, EOFTerminal, Rules)) =
        parser(Start, EOFTerminal, Table) :-
    make_first_sets(Rules, map.init, FirstSets),
    trace [compile_time(flag("debug-parser-table")), io(!IO)] (
        io.write_string("First sets:\n", !IO),
        foldl(print_set, FirstSets, !IO),
        io.nl(!IO)
    ),

    make_leading_sets(FirstSets, Rules, map.init, LeadingSets),
    trace [compile_time(flag("debug-parser-table")), io(!IO)] (
        io.write_string("Leading sets:\n", !IO),
        foldl(print_set, LeadingSets, !IO),
        io.nl(!IO)
    ),

    det_insert(Start, make_singleton_set(eof),
        map.init, FollowSets0),
    make_follow_sets(FirstSets, LeadingSets, Rules, FollowSets0, FollowSets),
    trace [compile_time(flag("debug-parser-table")), io(!IO)] (
        io.write_string("Follow sets:\n", !IO),
        foldl(print_set, FollowSets, !IO),
        io.nl(!IO)
    ),

    Table = make_table(Rules, EOFTerminal, FirstSets, LeadingSets, FollowSets).

%-----------------------------------------------------------------------%

:- type first_set(T) == set(first_set_entry(T)).

:- type first_set_entry(T)
    --->    empty
    ;       one(T).

:- type leading_set(T) == set(leading_set_entry(T)).

:- type leading_set_entry(T)
    --->    empty
    ;       one(T)
    ;       two(T, T).

:- type follows_set(T) == set(follows_set_entry(T)).

:- type follows_set_entry(T)
    --->    eof
    ;       one(T)
    ;       one_and_eof(T) % XXX Unused.
    ;       two(T, T).

%-----------------------------------------------------------------------%

:- pred make_first_sets(list(bnf_rule(T, NT, R))::in,
    map(NT, first_set(T))::in, map(NT, first_set(T))::out) is det.

make_first_sets(Rules, !FirstSets) :-
    map_foldl(make_first_sets_rule, Rules, Changed, !FirstSets),
    ( if member(yes, Changed) then
        make_first_sets(Rules, !FirstSets)
    else
        true
    ).

:- pred make_first_sets_rule(bnf_rule(T, NT, R)::in, bool::out,
    map(NT, first_set(T))::in, map(NT, first_set(T))::out) is det.

make_first_sets_rule(Rule, Changed, FirstSets0, FirstSets) :-
    First = union_list(map((func(RHS) = first(FirstSets0, RHS ^ bnf_rhs)
        ), Rule ^ bnf_rhss)),
    LHS = Rule ^ bnf_lhs,
    ( if search(FirstSets0, LHS, OldFirstSet) then
        ( if superset(OldFirstSet, First) then
            Changed = no,
            FirstSets = FirstSets0
        else
            Changed = yes,
            det_update(LHS, union(OldFirstSet, First), FirstSets0, FirstSets)
        )
    else
        Changed = yes,
        det_insert(LHS, First, FirstSets0, FirstSets)
    ).

:- func first(map(NT, first_set(T)), list(bnf_atom(T, NT))) =
    first_set(T).

first(_, []) = make_singleton_set(empty).
first(FirstSets, [Atom | Atoms]) = First :-
    ( Atom = t(T),
        First = make_singleton_set(one(T))
    ; Atom = nt(NT),
        ( if search(FirstSets, NT, NTFirstSet) then
            ( if member(empty, NTFirstSet) then
                First = union(delete(NTFirstSet, empty),
                    first(FirstSets, Atoms))
            else
                First = NTFirstSet
            )
        else
            % No information on this other set yet.
            First = set.init
        )
    ).

%-----------------------------------------------------------------------%

:- pred make_leading_sets(map(NT, first_set(T))::in,
    list(bnf_rule(T, NT, R))::in,
    map(NT, leading_set(T))::in, map(NT, leading_set(T))::out) is det.

make_leading_sets(FirstSets, Rules, !LeadingSets) :-
    map_foldl(make_leading_sets_rule(FirstSets), Rules, Changed, !LeadingSets),
    ( if member(yes, Changed) then
        make_leading_sets(FirstSets, Rules, !LeadingSets)
    else
        true
    ).

:- pred make_leading_sets_rule(map(NT, first_set(T))::in,
    bnf_rule(T, NT, R)::in, bool::out,
    map(NT, leading_set(T))::in, map(NT, leading_set(T))::out) is det.

make_leading_sets_rule(FirstSets, Rule, Changed, LeadingSets0, LeadingSets) :-
    Leading = union_list(map(
        (func(RHS) = leading(FirstSets, LeadingSets0, RHS ^ bnf_rhs)),
        Rule ^ bnf_rhss)),
    LHS = Rule ^ bnf_lhs,
    ( if search(LeadingSets0, LHS, OldLeadingSet) then
        ( if superset(OldLeadingSet, Leading) then
            Changed = no,
            LeadingSets = LeadingSets0
        else
            Changed = yes,
            det_update(LHS, union(OldLeadingSet, Leading),
                LeadingSets0, LeadingSets)
        )
    else
        Changed = yes,
        det_insert(LHS, Leading, LeadingSets0, LeadingSets)
    ).

:- func leading(map(NT, first_set(T)), map(NT, leading_set(T)),
    list(bnf_atom(T, NT))) = leading_set(T).

leading(_, _, []) = make_singleton_set(empty).
leading(FirstSets, LeadingSets, [Atom | Atoms]) = Set :-
    ( Atom = t(T),
        Seconds = first(FirstSets, Atoms),
        Set = map((func(S0) = R :-
                ( S0 = empty,
                    R = one(T)
                ; S0 = one(S),
                    R = two(T, S)
                )
            ), Seconds)
    ; Atom = nt(NT),
        ( if search(LeadingSets, NT, NTLeadingSet) then
            ( if member(empty, NTLeadingSet) then
                Set = delete(NTLeadingSet, empty) `union`
                    leading(FirstSets, LeadingSets, Atoms)
            else
                Set = NTLeadingSet
            )
        else
            % No information on this set yet.
            Set = set.init
        )
    ).

%-----------------------------------------------------------------------%

:- pred make_follow_sets(map(NT, first_set(T))::in, map(NT,
    leading_set(T))::in, list(bnf_rule(T, NT, R))::in,
    map(NT, follows_set(T))::in, map(NT, follows_set(T))::out) is det.

make_follow_sets(FirstSets, LeadingSets, Rules, !FollowSets) :-
    map_foldl(make_follow_sets_2(FirstSets, LeadingSets), Rules, Changed,
        !FollowSets),
    ( if member(yes, Changed) then
        make_follow_sets(FirstSets, LeadingSets, Rules, !FollowSets)
    else
        true
    ).

:- pred make_follow_sets_2(map(NT, first_set(T))::in,
    map(NT, leading_set(T))::in, bnf_rule(T, NT, R)::in,
    bool::out, map(NT, follows_set(T))::in, map(NT, follows_set(T))::out)
    is det.

make_follow_sets_2(FirstSets, LeadingSets, Rule, Changed, !FollowSets) :-
    foldl2(make_follow_sets_3(Rule ^ bnf_lhs, FirstSets, LeadingSets),
        Rule ^ bnf_rhss, no, Changed, !FollowSets).

:- pred make_follow_sets_3(NT::in, map(NT, first_set(T))::in,
    map(NT, leading_set(T))::in, bnf_rhs(T, NT, R)::in, bool::in, bool::out,
    map(NT, follows_set(T))::in, map(NT, follows_set(T))::out) is det.

make_follow_sets_3(LHS, FirstSets, LeadingSets, RHS, !Changed, !FollowSets) :-
    bnf_rhs(Atoms, _) = RHS,
    make_follow_sets_4(Atoms, LHS, FirstSets, LeadingSets, _, !Changed,
        !FollowSets).

:- pred make_follow_sets_4(list(bnf_atom(T, NT))::in, NT::in,
    map(NT, first_set(T))::in, map(NT, leading_set(T))::in,
    follows_set(T)::out, bool::in, bool::out,
    map(NT, follows_set(T))::in, map(NT, follows_set(T))::out) is det.

make_follow_sets_4([], LHS, _, _,
        get_set_from_map_or_empty(FollowSets, LHS), !Changed, FollowSets,
        FollowSets).
make_follow_sets_4([t(T) | Atoms], LHS, FirstSets, LeadingSets,
        set([one(T)]), !Changed, !FollowSets) :-
    make_follow_sets_4(Atoms, LHS, FirstSets, LeadingSets, _, !Changed,
        !FollowSets).
make_follow_sets_4([nt(NT) | Atoms], LHS, FirstSets, LeadingSets,
        UpdatedFollows, !Changed, !FollowSets) :-
    make_follow_sets_4(Atoms, LHS, FirstSets, LeadingSets, NextFollows,
        !Changed, !FollowSets),

    ( Atoms = [],
        % Copy the follows set for LHS to the follows set for NT.
        Follows = NextFollows
    ; Atoms = [_ | _],
        % Add all the nonterminals from from the leading sets of Atoms to the
        % follows set of NT.
        LeadingInAtoms = leading(FirstSets, LeadingSets, Atoms),
        Follows = union_list(map(
            leading_to_follows(NextFollows),
            to_sorted_list(LeadingInAtoms)))
    ),

    ( if search(!.FollowSets, NT, OldFollows) then
        UpdatedFollows = union(OldFollows, Follows),
        ( if equal(UpdatedFollows, OldFollows) then
            true
        else
            !:Changed = yes,
            det_update(NT, UpdatedFollows, !FollowSets)
        )
    else
        UpdatedFollows = Follows,
        det_insert(NT, UpdatedFollows, !FollowSets)
    ).

:- func leading_to_follows(follows_set(T), leading_set_entry(T)) =
    follows_set(T).

leading_to_follows(FollowsSet, empty) = FollowsSet.
leading_to_follows(FollowsSet, one(T)) =
    next_follows_to_follows(T, FollowsSet).
leading_to_follows(_, two(FT, ST)) = set([two(FT, ST)]).

:- func next_follows_to_follows(T, follows_set(T)) = follows_set(T).

next_follows_to_follows(T, FollowsSet) =
    map((func(FollowsEntry) = Entry :-
        ( FollowsEntry = eof,
            Entry = one_and_eof(T)
        ;
            ( FollowsEntry = one(ST)
            ; FollowsEntry = one_and_eof(ST)
            ; FollowsEntry = two(ST, _)
            ),
            Entry = two(T, ST)
        )), FollowsSet).

:- func get_set_from_map_or_empty(map(K, set(V)), K) = set(V).

get_set_from_map_or_empty(Map, K) = Set :-
    ( if search(Map, K, SetPrime) then
        Set = SetPrime
    else
        Set = init
    ).

%-----------------------------------------------------------------------%

:- func make_table(list(bnf_rule(T, NT, R)), T, map(NT, first_set(T)),
    map(NT, leading_set(T)), map(NT, follows_set(T))) =
    table(T, NT, table_entry(T, NT, R)).

make_table(Rules, EOFTerminal, FirstSets, LeadingSets, FollowSets) =
        Table :-
    Rows0 = sort_and_remove_dups(condense(map(
        make_table_rows(EOFTerminal, FirstSets, LeadingSets, FollowSets),
        Rules))),
    condense_rows(Rows0, [], Rows),
    trace [compile_time(flag("debug-parser-table")), io(!IO)] (
        io.write_string("Table rows:\n", !IO),
        foldl(print_table_row, Rows, !IO),
        io.nl(!IO)
    ),
    foldl(build_table, Rows, table.init, Table).

:- type table_row(T, NT, R)
    --->    table_row(
                tr_nt           :: NT,
                tr_first_t      :: T,
                tr_second_t     :: maybe(T),
                tr_rule_name    :: string,
                tr_rule_rhs     :: bnf_rhs(T, NT, R)
            ).

:- func make_table_rows(T, map(NT, first_set(T)), map(NT, leading_set(T)),
    map(NT, follows_set(T)), bnf_rule(T, NT, R)) = list(table_row(T, NT, R)).

make_table_rows(EOFTerminal, FirstSets, LeadingSets, FollowSets, Rule) = Rows :-
    Name = Rule ^ bnf_name,
    LHS = Rule ^ bnf_lhs,
    Rows = condense(list.map(
        make_table_rows_rhs(EOFTerminal, FirstSets, LeadingSets, FollowSets,
            Name, LHS),
        Rule ^ bnf_rhss)).

:- func make_table_rows_rhs(T, map(NT, first_set(T)), map(NT, leading_set(T)),
    map(NT, follows_set(T)), string, NT, bnf_rhs(T, NT, R)) =
    list(table_row(T, NT, R)).

make_table_rows_rhs(EOFTerminal, FirstSets, LeadingSets, FollowSets, Name,
        LHS, RHS) = Rows :-
    LeadingSet = leading(FirstSets, LeadingSets, RHS ^ bnf_rhs),
    Rows = condense(map(
        make_table_rows_ls(EOFTerminal, FollowSets, Name, LHS, RHS),
        to_sorted_list(LeadingSet))).

:- func make_table_rows_ls(T, map(NT, follows_set(T)),
    string, NT, bnf_rhs(T, NT, R), leading_set_entry(T)) =
    list(table_row(T, NT, R)).

make_table_rows_ls(EOFTerminal, FollowSets, Name, LHS, RHS, LeadingEntry) =
        Rows :-
    ( LeadingEntry = empty,
        lookup(FollowSets, LHS, FollowSet),
        Rows = map(follows_entry_to_tr(EOFTerminal, LHS, Name, RHS),
            to_sorted_list(FollowSet))
    ; LeadingEntry = one(FT),
        Rows = [table_row(LHS, FT, no, Name, RHS)]
    ; LeadingEntry = two(FT, ST),
        Rows = [table_row(LHS, FT, yes(ST), Name, RHS)]
    ).

:- func follows_entry_to_tr(T, NT, string, bnf_rhs(T, NT, R),
    follows_set_entry(T)) = table_row(T, NT, R).

follows_entry_to_tr(EOFTerminal, LHS, Name, RHS, Entry) = Row :-
    ( Entry = eof,
        Row = table_row(LHS, EOFTerminal, no, Name, RHS)
    ; Entry = one(T),
        Row = table_row(LHS, T, no, Name, RHS)
    ; Entry = one_and_eof(T),
        Row = table_row(LHS, T, yes(EOFTerminal), Name, RHS)
    ; Entry = two(FT, ST),
        Row = table_row(LHS, FT, yes(ST), Name, RHS)
    ).

% The condese rows predicates form a state machine and will colapse
% sequences of rows whose second T's don't matter.

:- pred condense_rows(list(table_row(T, NT, R))::in,
    list(table_row(T, NT, R))::in, list(table_row(T, NT, R))::out) is det.

condense_rows([], !Rows).
condense_rows([Row | Rows], !Rows) :-
    condense_rows_same(Rows, Row, [], !Rows).

:- pred condense_rows_same(list(table_row(T, NT, R))::in,
    table_row(T, NT, R)::in, list(table_row(T, NT, R))::in,
    list(table_row(T, NT, R))::in, list(table_row(T, NT, R))::out) is det.

condense_rows_same([], Row0, _, !Rows) :-
    % All the rows we've seen can be colapsed into one.
    Row = Row0 ^ tr_second_t := no,
    !:Rows = [Row | !.Rows].
condense_rows_same([Row | Rows], SeenRow, SeenRows0, !Rows) :-
    Result = compare_rows(Row, SeenRow),
    ( Result = rows_equivilant,
        % We may be able to colapse this row too. depending on the rest.
        SeenRows = [SeenRow | SeenRows0],
        condense_rows_same(Rows, Row, SeenRows, !Rows)
    ; Result = rows_same_nt_first,
        % We cannot collapse these rows.
        !:Rows = [SeenRow | SeenRows0 ++ !.Rows],
        condense_rows_different(Rows, Row, !Rows)
    ; Result = rows_different,
        % This row forms a different part of the table, finish the current
        % part by collapsing this group and return to the first state.
        !:Rows = [SeenRow ^ tr_second_t := no | !.Rows],
        condense_rows([Row | Rows], !Rows)
    ).

:- pred condense_rows_different(list(table_row(T, NT, R))::in,
    table_row(T, NT, R)::in,
    list(table_row(T, NT, R))::in, list(table_row(T, NT, R))::out) is det.

condense_rows_different([], PrevRow, !Rows) :-
    !:Rows = [PrevRow | !.Rows].
condense_rows_different([Row | Rows], PrevRow, !Rows) :-
    !:Rows = [PrevRow | !.Rows],
    Result = compare_rows(Row, PrevRow),
    (
        % Part of the same group, which cannot be collapsed.
        ( Result = rows_equivilant
        ; Result = rows_same_nt_first
        ),
        condense_rows_different(Rows, Row, !Rows)
    ;
        % The start of a new group.
        Result = rows_different,
        condense_rows([Row | Rows], !Rows)
    ).

:- type compare_rows_result
    --->    rows_equivilant
    ;       rows_same_nt_first
    ;       rows_different.

:- func compare_rows(table_row(T, NT, R), table_row(T, NT, R))
    = compare_rows_result.

compare_rows(table_row(NTA, FTA, _, NameA, bnf_rhs(AtomsA, _)),
        table_row(NTB, FTB, _, NameB, bnf_rhs(AtomsB, _))) =
    ( if
        NTA = NTB,
        FTA = FTB
    then
        ( if
            NameA = NameB,
            AtomsA = AtomsB
        then
            rows_equivilant
        else
            rows_same_nt_first
        )
    else
        rows_different
    ).

:- pred build_table(table_row(T, NT, R)::in,
    table(T, NT, table_entry(T, NT, R))::in,
    table(T, NT, table_entry(T, NT, R))::out) is det.

build_table(Row, !Table) :-
    table_row(NT, FirstT, MaybeSecondT, Name, RHS) = Row,
    bnf_rhs(Atoms, Func) = RHS,
    StackItems = map(atom_to_stack_item, Atoms) ++
        [stack_reduce(Name, length(Atoms), Func)],
    Entry = table_entry(StackItems),
    table_insert(NT, FirstT, MaybeSecondT, Entry, !Table).

:- func atom_to_stack_item(bnf_atom(T, NT)) = stack_item(T, NT, R).

atom_to_stack_item(t(T)) = stack_t(T).
atom_to_stack_item(nt(NT)) = stack_nt(NT).

%-----------------------------------------------------------------------%

:- pred print_set(NT::in, set(T)::in, io::di, io::uo) is det.

print_set(NT, Set, !IO) :-
    SetString = join_list(", ", map(string, to_sorted_list(Set))),
    format("%s: %s\n", [s(string(NT)), s(SetString)], !IO).

:- pred print_table_row(table_row(T, NT, R)::in, io::di, io::uo) is det.

print_table_row(table_row(NT, FT, MaybeST, Name, _), !IO) :-
    io.format("%s: %s, %s, %s\n",
        [s(Name), s(string(NT)), s(string(FT)), s(STStr)], !IO),
    ( MaybeST = no,
        STStr = "-"
    ; MaybeST = yes(ST),
        STStr = string(ST)
    ).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
