%-----------------------------------------------------------------------%
% vim: ts=4 sw=4 et
%-----------------------------------------------------------------------%
:- module parsing.
%
% Parsing utils.
%
% Copyright (C) 2015 Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
%-----------------------------------------------------------------------%

:- interface.

:- import_module list.
:- import_module maybe.

:- include_module parsing.bnf.
:- include_module parsing.gen.

:- import_module context.
:- import_module parsing.bnf.
:- import_module result.

%-----------------------------------------------------------------------%

:- type parser(T, NT, R).

:- typeclass token_to_result(T, R) where [
        func token_to_result(T, maybe(string), context) = R
    ].

:- type token(T)
    --->    token(
                t_terminal      :: T,
                t_data          :: maybe(string),
                t_context       :: context
            ).

:- type parse_error(T)
    --->    pe_unexpected_token(
                peut_expected           :: list(T),
                peut_got                :: T
            )
    ;       pe_unexpected_eof(
                peue_expected           :: list(T)
            )
    ;       pe_junk_at_end(
                pejae_got               :: T
            ).

:- pred parse(parser(T, NT, R), list(token(T)), result(R, parse_error(T)))
    <= token_to_result(T, R).
:- mode parse(in, in, out) is det.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

:- import_module bool.
:- import_module io.
:- import_module int.
:- import_module map.
:- import_module require.
:- import_module set.
:- import_module string.

:- include_module parsing.table.

:- import_module parsing.table.

%-----------------------------------------------------------------------%

:- type table_entry(T, NT, R)
    --->    table_entry(
                te_new_stack_items  :: list(stack_item(T, NT, R))
            ).

:- type parser(T, NT, R)
    --->    parser(
                p_start         :: NT,
                p_eof_terminal  :: T,
                p_table         :: table(T, NT, table_entry(T, NT, R))
            ).

%-----------------------------------------------------------------------%

:- type stack_item(T, NT, R)
    --->    stack_nt(NT)
    ;       stack_t(T)
    ;       stack_reduce(string, int, func(list(R)) = maybe(R)).

parse(Parser, Input, Result) :-
    Stack = [stack_nt(Parser ^ p_start)],
    parse(Parser, Input, Stack, [], Result).

:- pred parse(parser(T, NT, R), list(token(T)), list(stack_item(T, NT, R)),
        list(R), result(R, parse_error(T)))
    <= token_to_result(T, R).
:- mode parse(in, in, in, in, out) is det.

parse(Parser, Input0, Stack0, ResultStack0, Result) :-
    ( Stack0 = [Tos | Stack1],
        ( Tos = stack_t(TS),
            ( Input0 = [token(TI, MaybeString, Context) | Input],
                ( if TI = TS then
                    % Input and TOS match, discard both and proceed.
                    TokenResult = token_to_result(TI, MaybeString, Context),
                    ResultStack = [TokenResult | ResultStack0],
                    parse(Parser, Input, Stack1, ResultStack, Result)
                else
                    % Not matched, parsing error.
                    Error = pe_unexpected_token([TS], TI),
                    Result = return_error(Context, Error)
                )
            ; Input0 = [],
                Error = pe_unexpected_eof([TS]),
                Result = return_error(nil_context, Error)
            )
        ; Tos = stack_nt(NTS),
            % Check table
            ( Input0 = [token(TI1, _, _), token(TI2, _, _) | _]
            ; Input0 = [token(TI1, _, _)],
                TI2 = Parser ^ p_eof_terminal
            ; Input0 = [],
                TI1 = Parser ^ p_eof_terminal,
                TI2 = Parser ^ p_eof_terminal
            ),
            ( if table_search(Parser ^ p_table, NTS, TI1, TI2, Entry) then
                Stack = Entry ^ te_new_stack_items ++ Stack1,
                parse(Parser, Input0, Stack, ResultStack0, Result)
            else
                table_valid_terminals(Parser ^ p_table, NTS, ValidTerminals),
                ( Input0 = [token(TIPrime, _, Context) | _],
                    Error = pe_unexpected_token(ValidTerminals, TIPrime)
                ; Input0 = [],
                    Error = pe_unexpected_eof(ValidTerminals),
                    Context = nil_context
                ),
                Result = return_error(Context, Error)
            )
        ; Tos = stack_reduce(Name, Num, Func),
            det_split_list(Num, ResultStack0, Nodes0, ResultStack1),
            reverse(Nodes0, Nodes),
            MaybeNode = Func(Nodes),
            ( MaybeNode = yes(Node)
            ; MaybeNode = no,
                error(format(
                    "Error creating parse tree node for '%s' with input: %s",
                    [s(Name), s(string(Nodes))]))
            ),
            ResultStack = [Node | ResultStack1],
            parse(Parser, Input0, Stack1, ResultStack, Result)
        )
    ; Stack0 = [],
        ( Input0 = [],
            ( if ResultStack0 = [R] then
                Result = ok(R)
            else
                unexpected($file, $pred, "Couldn't build result")
            )
        ; Input0 = [token(TI, _, Context) | _],
            Error = pe_junk_at_end(TI),
            Result = return_error(Context, Error)
        )
    ).

:- pred det_pop_items(int::in, list(T)::in, list(T)::out, list(T)::out)
    is det.

det_pop_items(N, List, Prefix, Suffix) :-
    det_pop_items(N, List, [], Prefix, Suffix).

:- pred det_pop_items(int::in, list(T)::in,
    list(T)::in, list(T)::out, list(T)::out) is det.

det_pop_items(N, List0, !Prefix, Suffix) :-
    ( if N < 0 then
        unexpected($file, $pred, "N < 0")
    else if N = 0 then
        Suffix = List0
    else
        ( List0 = [],
            unexpected($file, $pred, "list too short")
        ; List0 = [X | List],
            det_pop_items(N - 1, List, [X | !.Prefix], !:Prefix, Suffix)
        )
    ).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
