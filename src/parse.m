%-----------------------------------------------------------------------%
% vim: ts=4 sw=4 et
%-----------------------------------------------------------------------%
:- module parse.
%
% Copyright (C) Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
% Plasma parser
%
%-----------------------------------------------------------------------%

:- interface.

:- import_module io.

:- import_module ast.
:- import_module parse_util.
:- import_module util.
:- import_module util.result.

%-----------------------------------------------------------------------%

:- pred parse(string::in, result(ast, read_src_error)::out,
    io::di, io::uo) is det.

:- pred parse_interface(string::in, result(ast_interface, read_src_error)::out,
    io::di, io::uo) is det.

:- pred parse_typeres(string::in, result(ast_typeres, read_src_error)::out,
    io::di, io::uo) is det.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

:- import_module char.
:- import_module int.
:- import_module list.
:- import_module maybe.
:- import_module require.
:- import_module std_util.
:- import_module solutions.
:- import_module string.
:- import_module unit.

:- import_module common_types.
:- import_module context.
:- import_module lex.
:- import_module parsing.
:- import_module q_name.
:- import_module util.my_exception.
:- import_module util.my_string.
:- import_module varmap.

%-----------------------------------------------------------------------%

parse(Filename, Result, !IO) :-
    parse_file(Filename, lexemes, ignore_tokens, check_token, parse_plasma,
        Result, !IO).

parse_interface(Filename, Result, !IO) :-
    parse_file(Filename, lexemes, ignore_tokens, check_token,
        parse_plasma_interface(parse_interface_entry), Result, !IO).

parse_typeres(Filename, Result, !IO) :-
    parse_file(Filename, lexemes, ignore_tokens, check_token,
        parse_plasma_interface(parse_typeres_entry), Result, !IO).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- type token_type
    --->    module_
    ;       export
    ;       entrypoint
    ;       import
    ;       type_
    ;       func_
    ;       resource
    ;       from
    ;       uses
    ;       observes
    ;       opaque
    ;       as
    ;       foreign
    ;       var
    ;       return
    ;       match
    ;       if_
    ;       then_
    ;       else_
    ;       and_
    ;       or_
    ;       not_
    ;       pragma_
    ;       ident
    ;       number
    ;       string
    ;       l_curly
    ;       r_curly
    ;       l_paren
    ;       r_paren
    ;       l_square
    ;       r_square
    ;       l_angle
    ;       r_angle
    ;       l_square_colon
    ;       r_square_colon
    ;       apostrophe
    ;       colon
    ;       comma
    ;       period
    ;       plus
    ;       minus
    ;       star
    ;       slash
    ;       percent
    ;       bar
    ;       bang
    ;       double_plus
    ;       l_angle_equal
    ;       r_angle_equal
    ;       double_equal
    ;       bang_equal
    ;       equals
    ;       l_arrow
    ;       r_arrow
    ;       underscore
    ;       newline
    ;       comment
    ;       whitespace
    ;       eof.

:- instance ident_parsing(token_type) where [
    ident_ = ident,
    period_ = period
].

:- func lexemes = list(lexeme(lex_token(token_type))).

lexemes = [
        ("module"           -> return(module_)),
        ("export"           -> return(export)),
        ("entrypoint"       -> return(entrypoint)),
        ("import"           -> return(import)),
        ("type"             -> return(type_)),
        ("func"             -> return(func_)),
        ("resource"         -> return(resource)),
        ("from"             -> return(from)),
        ("uses"             -> return(uses)),
        ("observes"         -> return(observes)),
        ("opaque"           -> return(opaque)),
        ("as"               -> return(as)),
        ("foreign"          -> return(foreign)),
        ("var"              -> return(var)),
        ("return"           -> return(return)),
        ("match"            -> return(match)),
        ("if"               -> return(if_)),
        ("then"             -> return(then_)),
        ("else"             -> return(else_)),
        ("not"              -> return(not_)),
        ("and"              -> return(and_)),
        ("or"               -> return(or_)),
        ("pragma"           -> return(pragma_)),
        ("{"                -> return(l_curly)),
        ("}"                -> return(r_curly)),
        ("("                -> return(l_paren)),
        (")"                -> return(r_paren)),
        ("["                -> return(l_square)),
        ("]"                -> return(r_square)),
        ("<"                -> return(l_angle)),
        (">"                -> return(r_angle)),
        ("[:"               -> return(l_square_colon)),
        (":]"               -> return(r_square_colon)),
        ("'"                -> return(apostrophe)),
        (":"                -> return(colon)),
        (","                -> return(comma)),
        ("."                -> return(period)),
        ("+"                -> return(plus)),
        ("-"                -> return(minus)),
        ("*"                -> return(star)),
        ("/"                -> return(slash)),
        ("%"                -> return(percent)),
        ("|"                -> return(bar)),
        ("!"                -> return(bang)),
        ("<"                -> return(l_angle)),
        (">"                -> return(r_angle)),
        ("++"               -> return(double_plus)),
        ("<="               -> return(l_angle_equal)),
        (">="               -> return(r_angle_equal)),
        ("=="               -> return(double_equal)),
        ("!="               -> return(bang_equal)),
        ("="                -> return(equals)),
        ("<-"               -> return(l_arrow)),
        ("->"               -> return(r_arrow)),
        ("_"                -> return(underscore)),
        (nat                -> return(number)),
        (parse.identifier   -> return(ident)),
        % TODO: don't terminate the string on a \" escape sequence.
        ("\"" ++ *(anybut("\"")) ++ "\""
                            -> return(string)),

        (("//" ++ *(anybut("\n")))
                            -> return(comment)),
        (c_style_comment    -> return(comment)),
        ("\n"               -> return(newline)),
        (any(" \t\v\f")     -> return(whitespace))
    ].

:- func identifier = regexp.

identifier = alpha ++ *(lex.ident).

    % Due to a limitiation in the regex library this wont match /* **/ and
    % other strings where there is a * next to the final */
    %
:- func c_style_comment = regexp.

c_style_comment = "/*" ++ Middle ++ "*/" :-
    Middle = *(anybut("*") or ("*" ++ anybut("/"))).

:- pred ignore_tokens(token_type::in) is semidet.

ignore_tokens(whitespace).
ignore_tokens(newline).
ignore_tokens(comment).

:- pred check_token(token(token_type)::in, maybe(read_src_error)::out) is det.

check_token(token(Token, Data, _), Result) :-
    ( if
        % Comments
        Token = comment,
        % that begin with /* (not //)
        append("/*", _, Data),
        Length = length(Data)
    then
        ( if
            % and contain */ are probably a mistake due to the greedy match
            % for the middle part of those comments.
            sub_string_search(Data, "*/", Index),
            % Except when it's the last part of the comment.
            Index \= Length - 2
        then
            Result = yes(rse_tokeniser_greedy_comment)
        else if
            % Have a general warning to help people avoid the odd
            % condition above.
            index(Data, Length - 3, '*'),
            Length > 4
        then
            Result = yes(rse_tokeniser_starstarslash_comment)
        else
            Result = no
        )
    else
        Result = no
    ).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- type tokens == list(token(token_type)).

% Some grammar rules are conditionally enabled depending on what we're
% parsing.
:- type parse_type
    --->    parse_source
    ;       parse_interface.

:- pred parse_plasma(tokens::in, result(ast, read_src_error)::out)
    is det.

    % I will show the EBNF in comments.  NonTerminals appear in
    % CamelCase and terminals appear in lower_underscore_case.
    %
    % Plasma := ModuleDecl ToplevelItem*
    %
    % ModuleDecl := module ident
    %
parse_plasma(!.Tokens, Result) :-
    get_context(!.Tokens, Context),
    match_token(module_, ModuleMatch, !Tokens),
    parse_q_name(NameResult, !Tokens),
    zero_or_more_last_error(parse_entry, ok(Items), LastError, !Tokens),
    ( if
        ModuleMatch = ok(_),
        NameResult = ok(Name)
    then
        ( !.Tokens = [],
            Result = ok(ast(Name, Context, Items))
        ; !.Tokens = [token(Tok, _, TokCtxt) | _],
            LastError = error(LECtxt, Got, Expect),
            ( if compare((<), LECtxt, TokCtxt) then
                Result = return_error(TokCtxt,
                    rse_parse_junk_at_end(string(Tok)))
            else
                Result = return_error(LECtxt, rse_parse_error(Got, Expect))
            )
        )
    else
        Result0 = combine_errors_2(ModuleMatch, NameResult) `with_type`
            parse_res(unit),
        ( Result0 = error(C, G, E),
            Result = return_error(C, rse_parse_error(G, E))
        ; Result0 = ok(_),
            unexpected($file, $pred, "ok/1, expecting error/1")
        )
    ).

    % ToplevelItem := ImportDirective
    %               | TypeDefinition
    %               | ResourceDefinition
    %               | Definition
    %               | Pragma
    %
:- pred parse_entry(parse_res(ast_entry)::out, tokens::in, tokens::out) is det.

    % Defintiions exist at the top level and also within code blocks.  For
    % now that's just function definitions but it'll include other things in
    % the future.
    %
    % Definition := FuncDefinition
    %
parse_entry(Result, !Tokens) :-
    or([    parse_import,
            parse_map(func({N, X}) = ast_type(N, X),
                parse_type(parse_nq_name)),
            parse_map(func({N, X}) = ast_resource(N, X),
                parse_resource(parse_nq_name)),
            parse_map(func({N, X}) = ast_function(N, X),
                parse_func(parse_nq_name, parse_source)),
            parse_pragma],
        Result, !Tokens).

    % ImportDirective := import QualifiedIdent
    %                  | import QualifiedIdent as ident
    %
:- pred parse_import(parse_res(ast_entry)::out, tokens::in, tokens::out)
    is det.

parse_import(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(import, ImportMatch, !Tokens),
    parse_q_name(NameResult, !Tokens),
    ( if
        ImportMatch = ok(_),
        NameResult = ok(Name)
    then
        TokensAs = !.Tokens,
        match_token(as, AsMatch, !Tokens),
        match_token(ident, AsIdentResult, !Tokens),
        ( AsMatch = ok(_),
            ( AsIdentResult = ok(AsIdent),
                Result = ok(ast_import(ast_import(Name, yes(AsIdent),
                    Context)))
            ; AsIdentResult = error(C, G, E),
                Result = error(C, G, E)
            )
        ; AsMatch = error(_, _, _),
            Result = ok(ast_import(ast_import(Name, no, Context))),
            !:Tokens = TokensAs
        )
    else
        Result = combine_errors_2(ImportMatch, NameResult)
    ).

:- pred parse_type(parsing.parser(N, token_type), parse_res({N, ast_type(N)}),
    tokens, tokens).
:- mode parse_type(in(parsing.parser), out, in, out) is det.

parse_type(ParseName, Result, !Tokens) :-
    parse_export_opaque(Sharing, !Tokens),
    get_context(!.Tokens, Context),
    match_token(type_, MatchType, !Tokens),
    ParseName(NameResult, !Tokens),
    ( if
        MatchType = ok(_),
        NameResult = ok(Name)
    then
        match_token(slash, MatchSlash, !Tokens),
        ( MatchSlash = ok(_),
            % Abstract type
            parse_number(NumberRes, !Tokens),
            ( NumberRes = ok(Arity),
                Result = ok({Name, ast_type_abstract(arity(Arity), Context)})
            ; NumberRes = error(C, G, E),
                Result = error(C, G, E)
            )
        ; MatchSlash = error(_, _, _),
            % Concrete type
            optional(within(l_paren, one_or_more_delimited(comma,
                parse_type_var), r_paren), ok(MaybeParams), !Tokens),
            match_token(equals, MatchEquals, !Tokens),
            one_or_more_delimited(bar, parse_type_constructor(ParseName),
                CtrsResult, !Tokens),
            ( if
                MatchEquals = ok(_),
                CtrsResult = ok(Constructors)
            then
                Params = map(
                    func(T) = ( if N = T ^ atv_name
                                 then N
                                 else unexpected($file, $pred,
                                    "not a type variable")),
                    maybe_default([], MaybeParams)),
                Result = ok({Name,
                    ast_type(Params, Constructors, Sharing, Context)})
            else
                Result = combine_errors_2(MatchEquals, CtrsResult)
            )
        )
    else
        Result = combine_errors_2(MatchType, NameResult)
    ).

:- pred parse_type_constructor(parsing.parser(N, token_type),
    parse_res(at_constructor(N)), tokens, tokens).
:- mode parse_type_constructor(in(parsing.parser), out, in, out) is det.

parse_type_constructor(ParseName, Result, !Tokens) :-
    get_context(!.Tokens, Context),
    ParseName(CNameResult, !Tokens),
    optional(within(l_paren,
        one_or_more_delimited(comma, parse_type_ctr_field), r_paren),
        ok(MaybeFields), !Tokens),
    ( CNameResult = ok(CName),
        Result = ok(at_constructor(CName, maybe_default([], MaybeFields),
            Context))
    ; CNameResult = error(C, G, E),
        Result = error(C, G, E)
    ).

:- pred parse_type_ctr_field(parse_res(at_field)::out, tokens::in,
    tokens::out) is det.

parse_type_ctr_field(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(ident, NameResult, !Tokens),
    match_token(colon, MatchColon, !Tokens),
    parse_type_expr(TypeResult, !Tokens),
    ( if
        NameResult = ok(Name),
        MatchColon = ok(_),
        TypeResult = ok(Type)
    then
        Result = ok(at_field(Name, Type, Context))
    else
        Result = combine_errors_3(NameResult, MatchColon, TypeResult)
    ).

    % TypeExpr := TypeVar
    %           | TypeCtor ( '(' TypeExpr ( ',' TypeExpr )* ')' )?
    %           | 'func' '(' ( TypeExpr ( ',' TypeExpr )* )? ')' RetTypes?
    %
    % RetTypes := '->' TypeExpr
    %           | '->' '(' TypeExpr ( ',' TypeExpr )* ')'
    %
    % Type := QualifiedIdent
    %
    % TODO: Update to respect case of type names/vars
    %
:- pred parse_type_expr(parse_res(ast_type_expr)::out,
    tokens::in, tokens::out) is det.

parse_type_expr(Result, !Tokens) :-
    or([parse_type_var, parse_type_construction, parse_func_type], Result,
        !Tokens).

:- pred parse_type_var(parse_res(ast_type_expr)::out,
    tokens::in, tokens::out) is det.

parse_type_var(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(apostrophe, MatchSigil, !Tokens),
    match_token(ident, Result0, !Tokens),
    ( if
        MatchSigil = ok(_),
        Result0 = ok(S)
    then
        Result = ok(ast_type_var(S, Context))
    else
        Result = combine_errors_2(MatchSigil, Result0)
    ).

:- pred parse_type_construction(parse_res(ast_type_expr)::out,
    tokens::in, tokens::out) is det.

parse_type_construction(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    parse_q_name(ConstructorResult, !Tokens),
    % TODO: We could generate more helpful parse errors here, for example by
    % returning the error from within the optional thing if the l_paren is
    % seen.
    optional(within(l_paren, one_or_more_delimited(comma, parse_type_expr),
        r_paren), ok(MaybeArgs), !Tokens),
    ( ConstructorResult = ok(Name),
        ( MaybeArgs = no,
            Args = []
        ; MaybeArgs = yes(Args)
        ),
        Result = ok(ast_type(Name, Args, Context))
    ; ConstructorResult = error(C, G, E),
        Result = error(C, G, E)
    ).

    % Note that the return type cannot contain a comma, or that would be the
    % end of the type as a whole. So we use parens (that should be optional
    % when there's only a single result) to group multiple returns.
    %
    % TODO: This is an exception to the established pattern and so we should
    % update the rest of the grammar to match it (allowing optional parens).
    %
:- pred parse_func_type(parse_res(ast_type_expr)::out,
    tokens::in, tokens::out) is det.

parse_func_type(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(func_, MatchFunc, !Tokens),
    ( MatchFunc = ok(_),
        within(l_paren, zero_or_more_delimited(comma, parse_type_expr),
            r_paren, ParamsResult, !Tokens),

        zero_or_more(parse_uses, ok(Usess), !Tokens),
        Uses = condense(Usess),

        optional(parse_returns, ok(MaybeReturns), !Tokens),
        Returns = maybe_default([], MaybeReturns),

        ( ParamsResult = ok(Params),
            Result = ok(ast_type_func(Params, Returns, Uses, Context))
        ; ParamsResult = error(C, G, E),
            Result = error(C, G, E)
        )
    ; MatchFunc = error(C, G, E),
        Result = error(C, G, E)
    ).

    % ResourceDefinition := 'resource' QualifiedIdent 'from' QualifiedIdent
    %
:- pred parse_resource(parsing.parser(N, token_type),
    parse_res({N, ast_resource}), tokens, tokens).
:- mode parse_resource(in(parsing.parser), out, in, out) is det.

parse_resource(ParseName, Result, !Tokens) :-
    parse_export_opaque(Sharing, !Tokens),
    get_context(!.Tokens, Context),
    match_token(resource, ResourceMatch, !Tokens),
    % Not really an any ident, but this should make errors easier to
    % understand.  A user will get a "resource uknown" if they use the wrong
    % case rather than a syntax error.
    ParseName(NameResult, !Tokens),
    parse_resource_from(FromResult, !Tokens),
    ( if
        ResourceMatch = ok(_),
        NameResult = ok(Name),
        FromResult = ok(FromIdent)
    then
        Result = ok({Name, ast_resource(FromIdent, Sharing, Context)})
    else
        Result = combine_errors_3(ResourceMatch, NameResult, FromResult)
    ).

    % Parse a resource from an interface file.
    %
    % ResourceInterface := 'resource' QualifiedIdent ('from' QualifiedIdent)?
    %
:- pred parse_resource_interface(parse_res({q_name, maybe(ast_resource)})::out,
    tokens::in, tokens::out) is det.

parse_resource_interface(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(resource, ResourceMatch, !Tokens),
    parse_q_name(NameResult, !Tokens),
    ( if
        ResourceMatch = ok(_),
        NameResult = ok(Name)
    then
        optional(parse_resource_from, ok(FromResult), !Tokens),
        ( FromResult = yes(FromName),
            Result = ok({Name, yes(ast_resource(FromName, so_private, Context))})
        ; FromResult = no,
            Result = ok({Name, no})
        )
    else
        Result = combine_errors_2(ResourceMatch, NameResult)
    ).

    % Parse the body of a resource definition.
    %
:- pred parse_resource_from(parse_res(q_name)::out, tokens::in, tokens::out)
    is det.

parse_resource_from(Result, !Tokens) :-
    match_token(from, FromMatch, !Tokens),
    parse_q_name(IdentResult, !Tokens),
    ( if
        FromMatch = ok(_),
        IdentResult = ok(Name)
    then
        Result = ok(Name)
    else
        Result = combine_errors_2(FromMatch, IdentResult)
    ).

    % FuncDefinition := 'func' Name '(' ( Param ( ',' Param )* )? ')'
    %                       Uses* ReturnTypes? FuncBody
    %
    % Depending on the ParseName value that's passed in.
    % Name := ident
    %       | QualifiedIdent
    %
    % Param := ident : TypeExpr
    %        | TypeExpr          (Only in interfaces)
    %
    % Uses := uses QualifiedIdent
    %       | uses '(' QualifiedIdentList ')'
    %       | observes QualifiedIdent
    %       | observes '(' QualifiedIdentList ')'
    %
    % ReturnTypes := '->' TypeExpr
    %              | '->' '(' TypeExpr ( ',' TypeExpr )* ')'
    %
    % FuncBody := Block
    %           | Foreign
    %
:- pred parse_func(parsing.parser(Name, token_type),
    parse_type, parse_res({Name, ast_function}), tokens, tokens).
:- mode parse_func(in(parsing.parser),
    in, out, in, out) is det.

parse_func(ParseName, ParseType, Result, !Tokens) :-
    maybe_parse_func_export(Sharing, Entrypoint, !Tokens),
    parse_func_decl(ParseName, ParseType, DeclResult, !Tokens),
    ( DeclResult = ok({Name, Decl}),
        or([parse_map(func(Bs) = ast_body_block(Bs), parse_block),
            parse_foreign],
           BodyResult, !Tokens),
        ( BodyResult = ok(Body),
            Result = ok({Name, ast_function(Decl, Body, Sharing, Entrypoint)})
        ; BodyResult = error(C, G, E),
            Result = error(C, G, E)
        )
    ; DeclResult = error(C, G, E),
        Result = error(C, G, E)
    ).

    % NestedFuncDefinition := 'func' Ident '(' ( Param ( ',' Param )* )? ')'
    %                             Uses* ReturnTypes? Block
    %
    % Param := ident : TypeExpr
    %
    % Uses := uses QualifiedIdent
    %       | uses '(' QualifiedIdentList ')'
    %       | observes QualifiedIdent
    %       | observes '(' QualifiedIdentList ')'
    %
    % ReturnTypes := '->' TypeExpr
    %              | '->' '(' TypeExpr ( ',' TypeExpr )* ')'
    %
:- pred parse_nested_func(parse_res(ast_block_thing), tokens, tokens).
:- mode parse_nested_func(out, in, out) is det.

parse_nested_func(Result, !Tokens) :-
    parse_func_decl(parse_nq_name, parse_source, DeclResult, !Tokens),
    ( DeclResult = ok({Name, Decl}),
        parse_block(BodyResult, !Tokens),
        ( BodyResult = ok(Body),
            Result = ok(astbt_function(Name,
                ast_nested_function(Decl, Body)))
        ; BodyResult = error(C, G, E),
            Result = error(C, G, E)
        )
    ; DeclResult = error(C, G, E),
        Result = error(C, G, E)
    ).

:- pred parse_func_decl(pred(parse_res(Name), tokens, tokens),
    parse_type, parse_res({Name, ast_function_decl}), tokens, tokens).
:- mode parse_func_decl(pred(out, in, out) is det,
    in, out, in, out) is det.

parse_func_decl(ParseName, ParseType, Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(func_, MatchFunc, !Tokens),
    ( MatchFunc = ok(_),
        ParseName(NameResult, !Tokens),
        parse_param_list(ParseType, ParamsResult, !Tokens),
        zero_or_more(parse_uses, ok(Uses), !Tokens),
        optional(parse_returns, ok(MaybeReturns), !Tokens),
        ( if
            NameResult = ok(Name),
            ParamsResult = ok(Params)
        then
            Result = ok({Name,
                ast_function_decl(Params, maybe_default([], MaybeReturns),
                    condense(Uses), Context)})
        else
            Result = combine_errors_2(NameResult, ParamsResult)
        )
    ; MatchFunc = error(C, G, E),
        Result = error(C, G, E)
    ).

:- pred parse_param_list(parse_type::in, parse_res(list(ast_param))::out,
    tokens::in, tokens::out) is det.

parse_param_list(ParseType, Result, !Tokens) :-
    within(l_paren, zero_or_more_delimited(comma, parse_param(ParseType)),
        r_paren, Result, !Tokens).

:- pred parse_param(parse_type::in, parse_res(ast_param)::out,
    tokens::in, tokens::out) is det.

parse_param(parse_source, Result, !Tokens) :-
    parse_named_param(Result, !Tokens).
parse_param(parse_interface, Result, !Tokens) :-
    or([parse_named_param, parse_unnamed_param], Result, !Tokens).

:- pred parse_named_param(parse_res(ast_param)::out,
    tokens::in, tokens::out) is det.

parse_named_param(Result, !Tokens) :-
    parse_ident_or_wildcard(NameOrWildResult, !Tokens),
    match_token(colon, ColonMatch, !Tokens),
    parse_type_expr(TypeResult, !Tokens),
    ( if
        NameOrWildResult = ok(NameOrWild),
        ColonMatch = ok(_),
        TypeResult = ok(Type)
    then
        Result = ok(ast_param(NameOrWild, Type))
    else
        Result = combine_errors_3(NameOrWildResult, ColonMatch, TypeResult)
    ).

:- pred parse_unnamed_param(parse_res(ast_param)::out,
    tokens::in, tokens::out) is det.

parse_unnamed_param(Result, !Tokens) :-
    parse_map(func(Type) = ast_param(wildcard, Type),
        parse_type_expr, Result, !Tokens).

:- pred parse_returns(parse_res(list(ast_type_expr))::out,
    tokens::in, tokens::out) is det.

parse_returns(Result, !Tokens) :-
    match_token(r_arrow, MatchRArrow, !Tokens),
    decl_list(parse_type_expr, ReturnTypesResult, !Tokens),
    ( if
        MatchRArrow = ok(_),
        ReturnTypesResult = ok(ReturnTypes)
    then
        Result = ok(ReturnTypes)
    else
        Result = combine_errors_2(MatchRArrow, ReturnTypesResult)
    ).

:- pred parse_uses(parse_res(list(ast_uses))::out,
    tokens::in, tokens::out) is det.

parse_uses(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    next_token("Uses or observes clause", UsesObservesResult, !Tokens),
    ( UsesObservesResult = ok(token_and_string(UsesObserves, TokenString)),
        ( if
            ( UsesObserves = uses,
                UsesType = ut_uses
            ; UsesObserves = observes,
                UsesType = ut_observes
            )
        then
            decl_list(parse_q_name, ResourcesResult, !Tokens),
            Result = map((func(Rs) =
                    map((func(R) = ast_uses(UsesType, R)), Rs)
                ), ResourcesResult)
        else
            Result = error(Context, TokenString, "Uses or observes clause")
        )
    ; UsesObservesResult = error(C, G, E),
        Result = error(C, G, E)
    ).

    % Foreign := 'foreign' '(' Ident ')'
    %
    % A foreign code declration. Plasma will attempt to link the foreign
    % symbol named with the Ident.
    %
:- pred parse_foreign(parse_res(ast_body)::out,
    tokens::in, tokens::out) is det.

parse_foreign(Result, !Tokens) :-
    match_token(foreign, ForeignMatch, !Tokens),
    within(l_paren, match_token(ident), r_paren, MaybeName, !Tokens),
    ( if
        ForeignMatch = ok(_),
        MaybeName = ok(Name)
    then
        Result = ok(ast_body_foreign(Name))
    else
        Result = combine_errors_2(ForeignMatch, MaybeName)
    ).

    % Block := '{' ( Statment | Definition )* ReturnExpr? '}'
    % ReturnExpr := 'return' TupleExpr
    %
    % ReturnExpr is parsed here to avoid an ambiguity that could arise if
    % the expression it is returning is a match or if expression, since it
    % could also be the beginning of the following statement.  By requiring
    % that the return statement is the last statement (which makes sense)
    % there can be no next statement and match/if is the expression being
    % returned.  TODO: This could be a problem if we add yield statements,
    % which probably can be followed by other statements.
    %
:- pred parse_block(parse_res(list(ast_block_thing))::out,
    tokens::in, tokens::out) is det.

parse_block(Result, !Tokens) :-
    match_token(l_curly, MatchLCurly, !Tokens),
    zero_or_more_last_error(parse_block_thing, Stmts0Result, LastError,
        !Tokens),
    ( if
        MatchLCurly = ok(_),
        Stmts0Result = ok(Stmts0)
    then
        optional(parse_stmt_return, ok(MaybeReturn), !Tokens),
        match_token(r_curly, MatchRCurly, !Tokens),
        ( MatchRCurly = ok(_),
            ( MaybeReturn = yes(Return),
                Stmts = Stmts0 ++ [astbt_statement(Return)]
            ; MaybeReturn = no,
                Stmts = Stmts0
            ),
            Result = ok(Stmts)
        ; MatchRCurly = error(C, G, E),
            ( MaybeReturn = yes(_),
                Result = error(C, G, E)
            ; MaybeReturn = no,
                LastError = error(LastC, LastG, LastE),
                ( if LastC ^ c_line > C ^ c_line then
                    % We partially parsed a statement above
                    Result = error(LastC, LastG, LastE)
                else
                    % We stopped parsing the zero_or_more_last_error above for
                    % the same reason there's no return statement and no closing
                    % brace.
                    Result = error(C, G, "statement or closing brace")
                )
            )
        )
    else
        Result = combine_errors_2(MatchLCurly, Stmts0Result)
    ).

:- pred parse_block_thing(parse_res(ast_block_thing)::out,
    tokens::in, tokens::out) is det.

parse_block_thing(Result, !Tokens) :-
    or([  parse_map(func(S) = astbt_statement(S),
            parse_statement),
          parse_nested_func],
        Result, !Tokens).

    % Statement := 'var' Ident ( ',' Ident )+
    %            | `match` Expr '{' Case+ '}'
    %            | ITE
    %            | CallInStmt
    %            | IdentList '=' Expr
    %            | Ident ArraySubscript '<=' Expr
    %            | Definition
    %
    % CallInStmt := ExprPart '!'? '(' Expr ( , Expr )* ')'
    %
    % The '!' is an optional part of the grammer even though no sensible
    % program would omit it in this context (either it would be an error
    % because the callee uses a resource or the compiler would optimise the
    % call away).
    %
    % Case := Pattern '->' Block
    %
    % ITE := 'if' Expr Block else ElsePart
    % ElsePart := ITE | Block
    %
:- pred parse_statement(parse_res(ast_statement)::out,
    tokens::in, tokens::out) is det.

parse_statement(Result, !Tokens) :-
    or([    parse_stmt_match,
            parse_stmt_ite,
            parse_stmt_assign,
            parse_stmt_call,
            parse_stmt_var,
            parse_stmt_array_set],
        Result, !Tokens).

:- pred parse_stmt_return(parse_res(ast_statement)::out,
    tokens::in, tokens::out) is det.

parse_stmt_return(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(return, ReturnMatch, !Tokens),
    zero_or_more_delimited(comma, parse_expr, ok(Vals), !Tokens),
    Result = map((func(_) =
            ast_statement(s_return_statement(Vals), Context)),
        ReturnMatch).

:- pred parse_stmt_match(parse_res(ast_statement)::out,
    tokens::in, tokens::out) is det.

parse_stmt_match(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(match, MatchMatch, !Tokens),
    parse_expr(MExprResult, !Tokens),
    within_use_last_error(l_curly, one_or_more_last_error(parse_match_case),
        r_curly, CasesResult, !Tokens),
    ( if
        MatchMatch = ok(_),
        MExprResult = ok(MExpr),
        CasesResult = ok(Cases)
    then
        Result = ok(ast_statement(s_match_statement(MExpr, Cases), Context))
    else
        Result = combine_errors_3(MatchMatch, MExprResult, CasesResult)
    ).

:- pred parse_match_case(parse_res(ast_match_case)::out,
    tokens::in, tokens::out) is det.

parse_match_case(Result, !Tokens) :-
    parse_pattern(PatternResult, !Tokens),
    match_token(r_arrow, MatchArrow, !Tokens),
    parse_block(StmtsResult, !Tokens),
    ( if
        PatternResult = ok(Pattern),
        MatchArrow = ok(_),
        StmtsResult = ok(Stmts)
    then
        Result = ok(ast_match_case(Pattern, Stmts))
    else
        Result = combine_errors_3(PatternResult, MatchArrow, StmtsResult)
    ).

:- pred parse_stmt_call(parse_res(ast_statement)::out,
    tokens::in, tokens::out) is det.

parse_stmt_call(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    parse_call_in_stmt(CallResult, !Tokens),
    ( CallResult = ok(Call),
        Result = ok(ast_statement(s_call(Call), Context))
    ; CallResult = error(C, G, E),
        Result = error(C, G, E)
    ).

    % Parse a call as it occurs within a statement.
    %
:- pred parse_call_in_stmt(parse_res(ast_call_like)::out,
    tokens::in, tokens::out) is det.

parse_call_in_stmt(Result, !Tokens) :-
    parse_expr_2(CalleeResult, !Tokens),
    optional(match_token(bang), ok(MaybeBang), !Tokens),
    % TODO: Use last error.
    within(l_paren, zero_or_more_delimited(comma, parse_expr), r_paren,
        ArgsResult, !Tokens),
    ( if
        CalleeResult = ok(Callee),
        ArgsResult = ok(Args)
    then
        ( MaybeBang = no,
            Result = ok(ast_call_like(Callee, Args))
        ; MaybeBang = yes(_),
            Result = ok(ast_bang_call(Callee, Args))
        )
    else
        Result = combine_errors_2(CalleeResult, ArgsResult)
    ).

:- pred parse_stmt_var(parse_res(ast_statement)::out,
    tokens::in, tokens::out) is det.

parse_stmt_var(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(var, VarMatch, !Tokens),
    match_token(ident, IdentResult, !Tokens),
    ( if
        VarMatch = ok(_),
        IdentResult = ok(Var)
    then
        Result = ok(ast_statement(s_var_statement(Var), Context))
    else
        Result = combine_errors_2(VarMatch, IdentResult)
    ).

:- pred parse_stmt_assign(parse_res(ast_statement)::out,
    tokens::in, tokens::out) is det.

parse_stmt_assign(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    one_or_more_delimited(comma, parse_pattern, LHSResult, !Tokens),
    parse_assigner(ValResult, !Tokens),
    ( if
        LHSResult = ok(LHSs),
        ValResult = ok(Val)
    then
        Result = ok(ast_statement(s_assign_statement(LHSs, Val), Context))
    else
        Result = combine_errors_2(LHSResult, ValResult)
    ).

:- pred parse_assigner(parse_res(list(ast_expression))::out,
    tokens::in, tokens::out) is det.

parse_assigner(Result, !Tokens) :-
    match_token(equals, EqualsMatch, !Tokens),
    one_or_more_delimited(comma, parse_expr, ValsResult, !Tokens),
    ( if
        EqualsMatch = ok(_)
    then
        Result = ValsResult
    else
        Result = combine_errors_2(EqualsMatch, ValsResult)
    ).

:- pred parse_ident_or_wildcard(parse_res(var_or_wildcard(string))::out,
    tokens::in, tokens::out) is det.

parse_ident_or_wildcard(Result, !Tokens) :-
    match_token(ident, ResultIdent, !.Tokens, TokensIdent),
    ( ResultIdent = ok(Ident),
        !:Tokens = TokensIdent,
        Result = ok(var(Ident))
    ; ResultIdent = error(C, G, E),
        match_token(underscore, ResultWildcard, !Tokens),
        ( ResultWildcard = ok(_),
            Result = ok(wildcard)
        ; ResultWildcard = error(_, _, _),
            Result = error(C, G, E)
        )
    ).

:- pred parse_stmt_array_set(parse_res(ast_statement)::out,
    tokens::in, tokens::out) is det.

parse_stmt_array_set(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(ident, NameResult, !Tokens),
    within(l_square, parse_expr, r_square, IndexResult, !Tokens),
    % TODO: Use := for array assignment.
    match_token(l_angle_equal, ArrowMatch, !Tokens),
    parse_expr(ValueResult, !Tokens),
    ( if
        NameResult = ok(Name),
        IndexResult = ok(Index),
        ArrowMatch = ok(_),
        ValueResult = ok(Value)
    then
        Result = ok(ast_statement(
            s_array_set_statement(Name, Index, Value), Context))
    else
        Result = combine_errors_4(NameResult, IndexResult, ArrowMatch,
            ValueResult)
    ).

:- pred parse_stmt_ite(parse_res(ast_statement)::out,
    tokens::in, tokens::out) is det.

parse_stmt_ite(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(if_, MatchIf, !Tokens),
    ( MatchIf = ok(_),
        parse_expr(CondResult, !Tokens),
        parse_block(ThenResult, !Tokens),
        match_token(else_, MatchElse, !Tokens),
        or([parse_stmt_ite_as_block, parse_block], ElseResult, !Tokens),
        ( if
            CondResult = ok(Cond),
            ThenResult = ok(Then),
            MatchElse = ok(_),
            ElseResult = ok(Else)
        then
            Result = ok(ast_statement(s_ite(Cond, Then, Else), Context))
        else
            Result = combine_errors_4(CondResult, ThenResult,
                MatchElse, ElseResult)
        )
    ; MatchIf = error(C, G, E),
        Result = error(C, G, E)
    ).

:- pred parse_stmt_ite_as_block(parse_res(list(ast_block_thing))::out,
    tokens::in, tokens::out) is det.

parse_stmt_ite_as_block(Result, !Tokens) :-
    parse_stmt_ite(Result0, !Tokens),
    Result = map((func(X) = [astbt_statement(X)]), Result0).

    % Expressions may be:
    %
    % A branch expression
    %   Expr := 'match' Expr '{' Case+ '}'
    %         | 'if' Expr 'then' Expr 'else' Expr
    % A binary and unary expressions
    %         | Expr BinOp Expr
    %         | UOp Expr
    % A call or construction
    %         | ExprPart '!'? '(' Expr ( , Expr )* ')'
    % An array subscript
    %         | ExprPart '[' Expr ']'
    % A higher precedence expression.
    %         | ExprPart
    %
    % Which may be:
    %   ExprPart := '(' Expr ')'
    % A list or array
    %             | '[' ListExpr ']'
    %             | '[:' TupleExpr? ':]'
    % A value:
    %             | QualifiedIdent
    % A constant:
    %             | const_str
    %             | const_int
    %
    % ListExpr := e
    %           | Expr ( ',' Expr )* ( ':' Expr )?
    %
    % Case := Pattern '->' TupleExpr
    %
    % The relative precedences of unary and binary operators is covered in
    % the reference manual
    % https://plasmalang.org/docs/plasma_ref.html#_expressions
    %
:- pred parse_expr(parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_expr(Result, !Tokens) :-
    or([parse_expr_match, parse_expr_if, parse_binary_expr(max_binop_level)],
        Result, !Tokens).

:- pred parse_expr_match(parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_expr_match(Result, !Tokens) :-
    match_token(match, MatchMatch, !Tokens),
    ( MatchMatch = ok(_),
        parse_expr(MatchExprResult, !Tokens),
        match_token(l_curly, MatchLCurly, !Tokens),
        one_or_more(parse_expr_match_case, CasesResult, !Tokens),
        match_token(r_curly, MatchRCurly, !Tokens),
        ( if
            MatchExprResult = ok(MatchExpr),
            MatchLCurly = ok(_),
            CasesResult = ok(Cases),
            MatchRCurly = ok(_)
        then
            Result = ok(e_match(MatchExpr, Cases))
        else
            Result = combine_errors_4(MatchExprResult, MatchLCurly,
                CasesResult, MatchRCurly)
        )
    ; MatchMatch = error(C, G, E),
        Result = error(C, G, E)
    ).

:- pred parse_expr_match_case(parse_res(ast_expr_match_case)::out,
    tokens::in, tokens::out) is det.

parse_expr_match_case(Result, !Tokens) :-
    parse_pattern(PatternResult, !Tokens),
    match_token(r_arrow, MatchArrow, !Tokens),
    one_or_more_delimited(comma, parse_expr, ExprsResult, !Tokens),
    ( if
        PatternResult = ok(Pattern),
        MatchArrow = ok(_),
        ExprsResult = ok(Exprs)
    then
        Result = ok(ast_emc(Pattern, Exprs))
    else
        Result = combine_errors_3(PatternResult, MatchArrow, ExprsResult)
    ).

:- pred parse_expr_if(parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_expr_if(Result, !Tokens) :-
    match_token(if_, MatchIf, !Tokens),
    ( MatchIf = ok(_),
        parse_expr(CondResult, !Tokens),
        match_token(then_, MatchThen, !Tokens),
        one_or_more_delimited(comma, parse_expr, ThenResult, !Tokens),
        match_token(else_, MatchElse, !Tokens),
        one_or_more_delimited(comma, parse_expr, ElseResult, !Tokens),
        ( if
            CondResult = ok(Cond),
            MatchThen = ok(_),
            ThenResult = ok(Then),
            MatchElse = ok(_),
            ElseResult = ok(Else)
        then
            Result = ok(e_if(Cond, Then, Else))
        else
            Result = combine_errors_5(CondResult, MatchThen, ThenResult,
                MatchElse, ElseResult)
        )
    ; MatchIf = error(C, G, E),
        Result = error(C, G, E)
    ).

:- pred operator_table(int, token_type, ast_bop).
:- mode operator_table(in, in, out) is semidet.
:- mode operator_table(out, out, out) is multi.

operator_table(1,   star,               b_mul).
operator_table(1,   slash,              b_div).
operator_table(1,   percent,            b_mod).
operator_table(2,   plus,               b_add).
operator_table(2,   minus,              b_sub).
operator_table(3,   l_angle,            b_lt).
operator_table(3,   r_angle,            b_gt).
operator_table(3,   l_angle_equal,      b_lteq).
operator_table(3,   r_angle_equal,      b_gteq).
operator_table(3,   double_equal,       b_eq).
operator_table(3,   bang_equal,         b_neq).
operator_table(4,   and_,               b_logical_and).
operator_table(5,   or_,                b_logical_or).
operator_table(6,   double_plus,        b_concat).

:- func max_binop_level = int.

max_binop_level = Max :-
    solutions((pred(Level::out) is multi :- operator_table(Level, _, _)),
        Levels),
    Max = foldl((func(X, M) = (if X > M then X else M)), Levels, 1).

:- pred parse_binary_expr(int::in, parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_binary_expr(Level, Result, !Tokens) :-
    parse_binary_expr_2(Level, ExprLResult, !Tokens),
    ( ExprLResult = ok(ExprL),
        parse_binary_expr_lassoc(Level, ExprL, Result, !Tokens)
    ; ExprLResult = error(_, _, _),
        Result = ExprLResult
    ).

:- pred parse_binary_expr_lassoc(int::in, ast_expression::in,
    parse_res(ast_expression)::out, tokens::in, tokens::out) is det.

parse_binary_expr_lassoc(Level, ExprL0, Result, !Tokens) :-
    BeforeOpTokens = !.Tokens,
    next_token("operator", OpResult, !Tokens),
    ( if
        OpResult = ok(token_and_string(Op, _)),
        operator_table(Level, Op, EOp)
    then
        parse_binary_expr_2(Level, ExprNResult, !Tokens),
        ( ExprNResult = ok(ExprN),
            ExprL = e_b_op(ExprL0, EOp, ExprN),
            parse_binary_expr_lassoc(Level, ExprL, Result, !Tokens)
        ; ExprNResult = error(_, _, _),
            Result = ExprNResult
        )
    else
        !:Tokens = BeforeOpTokens,
        Result = ok(ExprL0)
    ).

:- pred parse_binary_expr_2(int::in, parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_binary_expr_2(Level, Result, !Tokens) :-
    ( if Level > 0 then
        parse_binary_expr(Level - 1, ExprLResult, !Tokens),
        ( ExprLResult = ok(ExprL),
            BeforeOpTokens = !.Tokens,
            next_token("operator", OpResult, !Tokens),
            ( if
                OpResult = ok(token_and_string(Op, _)),
                operator_table(Level, Op, EOp)
            then
                parse_binary_expr(Level - 1, ExprRResult, !Tokens),
                ( ExprRResult = ok(ExprR),
                    Result = ok(e_b_op(ExprL, EOp, ExprR))
                ; ExprRResult = error(C, G, E),
                    Result = error(C, G, E)
                )
            else
                Result = ok(ExprL),
                !:Tokens = BeforeOpTokens
            )
        ; ExprLResult = error(C, G, E),
            Result = error(C, G, E)
        )
    else
        parse_unary_expr(Result, !Tokens)
    ).

:- pred parse_unary_expr(parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_unary_expr(Result, !Tokens) :-
    StartTokens = !.Tokens,
    next_token("expression", TokenResult, !Tokens),
    ( TokenResult = ok(token_and_string(Token, _)),
        ( if
            ( Token = minus,
                UOp = u_minus
            ; Token = not_,
                UOp = u_not
            )
        then
            parse_unary_expr(ExprResult, !Tokens),
            Result = map((func(E) = e_u_op(UOp, E)), ExprResult)
        else
            !:Tokens = StartTokens,
            parse_expr_1(Result, !Tokens)
        )
    ; TokenResult = error(C, G, E),
        Result = error(C, G, E)
    ).

    % This precidence level covers calls and array subscriptions.
    %
:- pred parse_expr_1(parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_expr_1(Result, !Tokens) :-
    parse_expr_2(Part1Result0, !Tokens),
    ( Part1Result0 = ok(Part1),
        parse_expr_part_2(Part1, Result, !Tokens)
    ; Part1Result0 = error(C, G, E),
        Result = error(C, G, E)
    ).

:- pred parse_expr_part_2(ast_expression::in, parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_expr_part_2(Part1, Result, !Tokens) :-
    Part1Tokens = !.Tokens,
    next_token("Call arguments or array subscript", NextResult,
        !Tokens),
    ( NextResult = ok(token_and_string(Next, _)),
        ( if
            (
                Next = l_paren,
                require_det (
                    parse_call_part2(Part1, Result1, !Tokens)
                )
            ;
                Next = bang,
                require_det (
                    match_token(l_paren, ParenResult, !Tokens),
                    ( ParenResult = ok(_),
                        parse_call_part2(Part1, Result0, !Tokens),
                        Result1 = map(make_bang_call, Result0)
                    ; ParenResult = error(C, G, E),
                        Result1 = error(C, G, E)
                    )
                )
            ;
                Next = l_square,
                require_det (
                    parse_array_subscript_part2(Part1, Result1, !Tokens)
                )
            )
        then
            ( Result1 = ok(Expr),
                parse_expr_part_2(Expr, Result, !Tokens)
            ; Result1 = error(_, _, _),
                !:Tokens = Part1Tokens,
                Result = ok(Part1)
            )
        else
            !:Tokens = Part1Tokens,
            Result = ok(Part1)
        )
    ; NextResult = error(_, _, _),
        !:Tokens = Part1Tokens,
        Result = ok(Part1)
    ).

:- pred parse_expr_2(parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_expr_2(Result, !Tokens) :-
    or([    parse_const_expr,
            within(l_paren, parse_expr, r_paren),
            within(l_square, parse_list_expr, r_square),
            parse_array_expr,
            parse_expr_symbol
        ], Result, !Tokens).

:- pred parse_const_expr(parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_const_expr(Result, !Tokens) :-
    ( if parse_string(ok(String), !Tokens) then
        Result = ok(e_const(c_string(String)))
    else if parse_number(ok(Num), !Tokens) then
        Result = ok(e_const(c_number(Num)))
    else
        get_context(!.Tokens, Context),
        Result = error(Context, "", "expression")
    ).

:- pred parse_array_expr(parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_array_expr(Result, !Tokens) :-
    within(l_square_colon, zero_or_more_delimited(comma, parse_expr),
        r_square_colon, Result0, !Tokens),
    Result = map((func(Exprs) = e_array(Exprs)), Result0).

:- pred parse_string(parse_res(string)::out, tokens::in, tokens::out)
    is det.

parse_string(Result, !Tokens) :-
    match_token(string, Result0, !Tokens),
    Result = map(unescape_string, Result0).

:- pred parse_number(parse_res(int)::out, tokens::in, tokens::out) is det.

parse_number(Result, !Tokens) :-
    optional(match_token(minus), ok(MaybeMinus), !Tokens),
    match_token(number, Result0, !Tokens),
    ( MaybeMinus = yes(_),
        Convert = (func(N) = string.det_to_int(N) * -1)
    ; MaybeMinus = no,
        Convert = string.det_to_int
    ),
    Result = map(Convert, Result0).

:- pred parse_list_expr(parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_list_expr(Result, !Tokens) :-
    StartTokens = !.Tokens,
    one_or_more_delimited(comma, parse_expr, HeadsResult, !Tokens),
    ( HeadsResult = ok(Heads),
        BeforeBarTokens = !.Tokens,
        match_token(bar, MatchBar, !Tokens),
        ( MatchBar = ok(_),
            parse_expr(TailResult, !Tokens),
            ( TailResult = ok(Tail),
                Result = ok(make_cons_list(Heads, Tail))
            ; TailResult = error(C, G, E),
                Result = error(C, G, E)
            )
        ; MatchBar = error(_, _, _),
            !:Tokens = BeforeBarTokens,
            Result = ok(make_cons_list(Heads, e_const(c_list_nil)))
        )
    ; HeadsResult = error(_, _, _),
        !:Tokens = StartTokens,
        Result = ok(e_const(c_list_nil))
    ).

:- pred parse_expr_symbol(parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_expr_symbol(Result, !Tokens) :-
    parse_q_name(QNameResult, !Tokens),
    Result = map((func(Name) = e_symbol(Name)), QNameResult).

:- pred parse_call_part2(ast_expression::in, parse_res(ast_expression)::out,
    tokens::in, tokens::out) is det.

parse_call_part2(Callee, Result, !Tokens) :-
    zero_or_more_delimited(comma, parse_expr, ok(Args), !Tokens),
    match_token(r_paren, MatchParen, !Tokens),
    ( MatchParen = ok(_),
        Result = ok(e_call_like(ast_call_like(Callee, Args)))
    ; MatchParen = error(C, G, E),
        Result = error(C, G, E)
    ).

:- pred parse_array_subscript_part2(ast_expression::in,
    parse_res(ast_expression)::out, tokens::in, tokens::out) is det.

parse_array_subscript_part2(Expr, Result, !Tokens) :-
    parse_expr(SubscriptResult, !Tokens),
    match_token(r_square, MatchClose, !Tokens),
    ( if
        SubscriptResult = ok(Subscript),
        MatchClose = ok(_)
    then
        Result = ok(e_b_op(Expr, b_array_subscript, Subscript))
    else
        Result = combine_errors_2(SubscriptResult, MatchClose)
    ).

    % Pattern := Number
    %          | QualifiedIdent ( '(' Pattern ',' ( Pattern ',' )+ ')' )?
    %
:- pred parse_pattern(parse_res(ast_pattern)::out,
    tokens::in, tokens::out) is det.

parse_pattern(Result, !Tokens) :-
    or([    parse_constr_pattern,
            parse_list_pattern,
            parse_number_pattern,
            parse_wildcard_pattern,
            parse_var_pattern
        ], Result, !Tokens).

:- pred parse_constr_pattern(parse_res(ast_pattern)::out,
    tokens::in, tokens::out) is det.

parse_constr_pattern(Result, !Tokens) :-
    parse_q_name(Result0, !Tokens),
    ( Result0 = ok(Symbol),
        optional(within(l_paren, one_or_more_delimited(comma, parse_pattern),
                r_paren),
            ok(MaybeArgs), !Tokens),
        ( MaybeArgs = yes(Args),
            Result = ok(p_constr(Symbol, Args))
        ; MaybeArgs = no,
            Result = ok(p_symbol(Symbol))
        )
    ; Result0 = error(C, G, E),
        Result = error(C, G, E)
    ).

:- pred parse_list_pattern(parse_res(ast_pattern)::out,
    tokens::in, tokens::out) is det.

parse_list_pattern(Result, !Tokens) :-
    within(l_square, parse_list_pattern_2, r_square, Result0, !Tokens),
    Result = map(id, Result0).

:- pred parse_list_pattern_2(parse_res(ast_pattern)::out,
    tokens::in, tokens::out) is det.

parse_list_pattern_2(Result, !Tokens) :-
    ( if peek_token(!.Tokens, yes(r_square)) then
        Result = ok(p_list_nil)
    else
        one_or_more_delimited(comma, parse_pattern, HeadsResult, !Tokens),
        ( HeadsResult = ok(Heads),
            BeforeBarTokens = !.Tokens,
            match_token(bar, MatchBar, !Tokens),
            ( MatchBar = ok(_),
                parse_pattern(TailResult, !Tokens),
                ( TailResult = ok(Tail),
                    Result = ok(make_p_list_cons(Heads, Tail))
                ; TailResult = error(C, G, E),
                    Result = error(C, G, E)
                )
            ; MatchBar = error(_, _, _),
                !:Tokens = BeforeBarTokens,
                Result = ok(make_p_list_cons(Heads, p_list_nil))
            )
        ; HeadsResult = error(C, G, E),
            Result = error(C, G, E)
        )
    ).

:- func make_p_list_cons(list(ast_pattern), ast_pattern) = ast_pattern.

make_p_list_cons([], Tail) = Tail.
make_p_list_cons([Head | Heads], Tail) =
    p_list_cons(Head, make_p_list_cons(Heads, Tail)).

:- pred parse_number_pattern(parse_res(ast_pattern)::out,
    tokens::in, tokens::out) is det.

parse_number_pattern(Result, !Tokens) :-
    parse_number(Result0, !Tokens),
    Result = map((func(N) = p_number(N)), Result0).

:- pred parse_wildcard_pattern(parse_res(ast_pattern)::out,
    tokens::in, tokens::out) is det.

parse_wildcard_pattern(Result, !Tokens) :-
    match_token(underscore, Result0, !Tokens),
    Result = map((func(_) = p_wildcard), Result0).

:- pred parse_var_pattern(parse_res(ast_pattern)::out,
    tokens::in, tokens::out) is det.

parse_var_pattern(Result, !Tokens) :-
    match_token(var, MatchVar, !Tokens),
    match_token(ident, Result0, !Tokens),
    ( if
        MatchVar = ok(_),
        Result0 = ok(S)
    then
        Result = ok(p_var(S))
    else
        Result = combine_errors_2(MatchVar, Result0)
    ).

%-----------------------------------------------------------------------%

:- pred maybe_parse_func_export(sharing::out, is_entrypoint::out,
    tokens::in, tokens::out) is det.

maybe_parse_func_export(Sharing, IsEntrypoint, !Tokens) :-
    parse_export(Sharing0, !Tokens),
    optional(match_token(entrypoint), ok(MaybeEntrypoint), !Tokens),
    ( MaybeEntrypoint = yes(_),
        ( Sharing0 = s_private,
            % the export keyword might have come after entrypoint, so check
            % again.
            parse_export(Sharing, !Tokens)
        ; Sharing0 = s_public,
            Sharing = s_public
        ),
        IsEntrypoint = is_entrypoint
    ; MaybeEntrypoint = no,
        IsEntrypoint = not_entrypoint,
        Sharing = Sharing0
    ).

:- pred parse_export_opaque(sharing_opaque::out,
    tokens::in, tokens::out) is det.

parse_export_opaque(Result, !Tokens) :-
    optional(match_token(export), ok(Export), !Tokens),
    ( Export = yes(_),
        optional(match_token(opaque), ok(Opaque), !Tokens),
        ( Opaque = yes(_),
            Result = so_public_opaque
        ; Opaque = no,
            Result = so_public
        )
    ; Export = no,
        Result = so_private
    ).

:- pred parse_export(sharing::out, tokens::in, tokens::out) is det.

parse_export(Sharing, !Tokens) :-
    optional(match_token(export), ok(MaybeExport), !Tokens),
    ( MaybeExport = yes(_),
        Sharing = s_public
    ; MaybeExport = no,
        Sharing = s_private
    ).

%-----------------------------------------------------------------------%

    % Pragma := 'pragma' Ident ('(' ( PragmaArg PragmaArgs )?  ')')
    %
    % PragmaArgs := ',' PragmaArg PragmaArgs
    %             | empty
    %
    % PragmaArg := String
    %
:- pred parse_pragma(parse_res(ast_entry)::out, tokens::in, tokens::out)
    is det.

parse_pragma(Result, !Tokens) :-
    get_context(!.Tokens, Context),
    match_token(pragma_, MatchPragma, !Tokens),
    match_token(ident, MatchIdent, !Tokens),
    within(l_paren, zero_or_more_delimited(comma, parse_pragma_arg),
        r_paren, MatchArgs, !Tokens),
    ( if
        MatchPragma = ok(_),
        MatchIdent = ok(Ident),
        MatchArgs = ok(Args)
    then
        Result = ok(ast_pragma(ast_pragma(Ident, Args, Context)))
    else
        Result = combine_errors_3(MatchPragma, MatchIdent, MatchArgs)
    ).

:- pred parse_pragma_arg(parse_res(ast_pragma_arg)::out,
    tokens::in, tokens::out) is det.

parse_pragma_arg(Result, !Tokens) :-
    parse_string(StringRes, !Tokens),
    ( StringRes = ok(String),
        Result = ok(ast_pragma_arg(String))
    ; StringRes = error(C, G, E),
        Result = error(C, G, E)
    ).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- pred parse_plasma_interface(
    pred(parse_res(E), tokens, tokens),
    tokens, result(ast(E), read_src_error)).
:- mode parse_plasma_interface(
    pred(out, in, out) is det,
    in, out) is det.

parse_plasma_interface(ParseEntry, !.Tokens, Result) :-
    get_context(!.Tokens, Context),
    match_token(module_, ModuleMatch, !Tokens),
    parse_q_name(NameResult, !Tokens),
    zero_or_more_last_error(ParseEntry, ok(Items), LastError,
        !Tokens),
    ( if
        ModuleMatch = ok(_),
        NameResult = ok(Name)
    then
        ( !.Tokens = [],
            Result = ok(ast(Name, Context, Items))
        ; !.Tokens = [token(Tok, _, TokCtxt) | _],
            LastError = error(LECtxt, Got, Expect),
            ( if compare((<), LECtxt, TokCtxt) then
                Result = return_error(TokCtxt,
                    rse_parse_junk_at_end(string(Tok)))
            else
                Result = return_error(LECtxt, rse_parse_error(Got, Expect))
            )
        )
    else
        Result0 = combine_errors_2(ModuleMatch, NameResult) `with_type`
            parse_res(unit),
        ( Result0 = error(C, G, E),
            Result = return_error(C, rse_parse_error(G, E))
        ; Result0 = ok(_),
            unexpected($file, $pred, "ok/1, expecting error/1")
        )
    ).

:- pred parse_interface_entry(parse_res(ast_interface_entry)::out,
    tokens::in, tokens::out) is det.

parse_interface_entry(Result, !Tokens) :-
    or([parse_map(func({N, T}) = asti_resource(N, T),
            parse_resource_interface),
        parse_map(func({N, T}) = asti_type(N, T),
            parse_type(parse_q_name)),
        parse_map(func({N, D}) = asti_function(N, D),
            parse_func_decl(parse_q_name, parse_interface))
    ], Result, !Tokens).

:- pred parse_typeres_entry(parse_res(ast_typeres_entry)::out,
    tokens::in, tokens::out) is det.

parse_typeres_entry(Result, !Tokens) :-
    or([parse_map(func(N) = asti_resource_abs(N), parse_abs_thing(resource)),
        parse_map(func({N, T}) = asti_type_abs(N, type_arity(T)),
            parse_type(parse_q_name))
    ], Result, !Tokens).

:- pred parse_abs_thing(token_type::in, parse_res(q_name)::out,
    tokens::in, tokens::out) is det.

parse_abs_thing(Token, Result, !Tokens) :-
    match_token(Token, ResourceMatch, !Tokens),
    ( ResourceMatch = ok(_),
        parse_q_name(Result, !Tokens)
    ; ResourceMatch = error(C, G, E),
        Result = error(C, G, E)
    ).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

    % A comma-seperated list with parens or a singleton item.
    %
    % This is used for lists where a comma in the list could either be the
    % end of the whole list and the legal beginning of something else, or
    % parens can be used to allow a list here.  This can be used for things
    % like the return types of function types when the function type is in
    % list of its own.
    %
:- pred decl_list(parsing.parser(R, token_type)::in(parsing.parser),
    parse_res(list(R))::out, tokens::in, tokens::out) is det.

decl_list(Parser, Result, !Tokens) :-
    ( if peek_token(!.Tokens, yes(l_paren)) then
        within(l_paren, one_or_more_delimited(comma, Parser), r_paren,
            Result, !Tokens)
    else
        Parser(Result0, !Tokens),
        Result = map((func(R) = [R]), Result0)
    ).

%-----------------------------------------------------------------------%

:- func make_cons_list(list(ast_expression), ast_expression) =
    ast_expression.

make_cons_list([], Tail) = Tail.
make_cons_list([X | Xs], Tail) = List :-
    List0 = make_cons_list(Xs, Tail),
    List = e_b_op(X, b_list_cons, List0).

:- func make_bang_call(ast_expression) = ast_expression.

make_bang_call(Expr0) = Expr :-
    ( if Expr0 = e_call_like(ast_call_like(Callee, Args)) then
        Expr = e_call_like(ast_bang_call(Callee, Args))
    else
        unexpected($file, $pred, "Not a call")
    ).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
