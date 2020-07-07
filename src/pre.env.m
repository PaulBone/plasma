%-----------------------------------------------------------------------%
% Plasma AST Environment manipulation routines
% vim: ts=4 sw=4 et
%
% Copyright (C) 2015-2020 Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
% This module contains code to track the environment of a statement in the
% Plasma AST.
%
%-----------------------------------------------------------------------%
:- module pre.env.
%-----------------------------------------------------------------------%

:- interface.

:- import_module set.
:- import_module string.

:- import_module ast.
:- import_module context.
:- import_module common_types.
:- import_module q_name.
:- import_module varmap.

%-----------------------------------------------------------------------%

:- type env.

    % init(BoolTrue, BoolFalse, ListNil, ListCons) = Env.
    %
:- func init(ctor_id, ctor_id, ctor_id, ctor_id) = env.

%-----------------------------------------------------------------------%
%
% Code to add variables and maniuplate their visibility in the environment.
%

    % Add but leave a variable uninitialised.
    %
    % The variable must not already exist.
    %
:- pred env_add_uninitialised_var(string::in, var::out, env::in, env::out,
    varmap::in, varmap::out) is semidet.

    % Add and initialise a variable.
    %
    % The variable must not already exist.
    %
:- pred env_add_and_initlalise_var(string::in, var::out, env::in, env::out,
    varmap::in, varmap::out) is semidet.

:- type initialise_result(T)
    --->    ok(T)
    ;       does_not_exist
    ;       already_initialised
    ;       inaccessible.

    % Initialise an existing variable.
    %
    % The variable must already exist.
    %
:- pred env_initialise_var(string::in, initialise_result(var)::out,
    env::in, env::out, varmap::in, varmap::out) is det.

    % All the vars that are defined but not initialised.
    %
:- func env_uninitialised_vars(env) = set(var).

    % Mark all these uninitialised vars as initialised.
    %
:- pred env_mark_initialised(set(var)::in, env::in, env::out) is det.

    % Within a closure scope the currently-uninitialised variables cannot be
    % accessed from the closure.
    %
    % We leave closures (like any scope) by discarding the environment and
    % using a "higher" one.
    %
:- pred env_enter_closure(env::in, env::out) is det.

    % Add a letrec variable.
    %
    % These are added to help resolve names within nested functions.
    % They're cleared when the real variable bindings become available.
    % Discarding is performed by discarding the environment.
    %
:- pred env_add_for_letrec(string::in, var::out, env::in, env::out,
    varmap::in, varmap::out) is semidet.

    % Within a letrec temporally set a self-recursive reference to a direct
    % function call.  This is how we handle self-recursion, which works
    % because its the same environment.
    %
:- pred env_letrec_self_recursive(string::in, func_id::in,
    env::in, env::out) is det.

    % Mark the formerly-letrec variable as a fully defined variable, because
    % it has now been defined while processing the letrec.
    %
:- pred env_letrec_defined(string::in, env::in, env::out) is det.

    % Make all letrec variables initalised (we've finished building the
    % letrec).
    %
:- pred env_leave_letrec(env::in, env::out) is det.

%-----------------------------------------------------------------------%
%
% Code to add other symbols to the environment.
%

:- pred env_add_func(q_name::in, func_id::in, env::in, env::out) is semidet.

    % Used to add builtins, which always have unique names.
    %
:- pred env_add_func_det(q_name::in, func_id::in, env::in, env::out) is det.

:- pred env_add_type(q_name::in, arity::in, type_id::in, env::in, env::out)
    is semidet.

:- pred env_add_type_det(q_name::in, arity::in, type_id::in, env::in, env::out)
    is det.

    % Constructors may be overloaded, so this always succeeds.
    %
:- pred env_add_constructor(q_name::in, ctor_id::in, env::in, env::out)
    is det.

:- pred env_add_resource(q_name::in, resource_id::in, env::in, env::out)
    is semidet.

:- pred env_add_resource_det(q_name::in, resource_id::in, env::in, env::out)
    is det.

:- pred env_import_star(q_name::in, env::in, env::out) is det.

%-----------------------------------------------------------------------%
%
% Code to query the environment.
%

:- type env_entry
    --->    ee_var(var)
    ;       ee_func(func_id)
    ;       ee_constructor(ctor_id).

:- inst env_entry_func_or_ctor for env_entry/0
    --->    ee_func(ground)
    ;       ee_constructor(ground).

:- type env_search_result(T)
    --->    ok(T)
    ;       not_found
    ;       not_initaliased
    ;       inaccessible
    ;       maybe_cyclic_retlec.

:- pred env_search(env::in, q_name::in, env_search_result(env_entry)::out)
    is det.

    % Throws an exception if the entry doesn't exist or isn't a function.
    %
:- pred env_lookup_function(env::in, q_name::in, func_id::out) is det.

:- pred env_search_type(env::in, q_name::in, type_id::out, arity::out)
    is semidet.

:- pred env_lookup_type(env::in, q_name::in, type_id::out, arity::out) is det.

:- pred env_search_constructor(env::in, q_name::in, ctor_id::out) is semidet.

    % NOTE: This is currently only implemented for one data type per
    % operator.
    %
:- pred env_operator_entry(env, ast_bop, env_entry).
:- mode env_operator_entry(in, in, out(env_entry_func_or_ctor)) is semidet.

:- pred env_unary_operator_func(env::in, ast_uop::in, func_id::out)
    is semidet.

:- pred env_search_resource(env::in, q_name::in, resource_id::out)
    is semidet.

:- pred env_lookup_resource(env::in, q_name::in, resource_id::out) is det.

%-----------------------------------------------------------------------%
%
% Misc.
%

    % Make a clobbered name for a lambda.
    %
:- func clobber_lambda(string, context) = string.

    % A name->func_id mapping is tracked in the environment.  These aren't
    % actual name bindings in the Plasma language, and env_search won't find
    % them.  It's just convenient to put them in this data structure since
    % they're added at the top level and not needed after the pre-core
    % compilation stage.
    %
    % This is different from the letrec entries added above.
    %
:- pred env_add_lambda(string::in, func_id::in, env::in, env::out) is det.

:- pred env_lookup_lambda(env::in, string::in, func_id::out) is det.

%-----------------------------------------------------------------------%
%
% Lookup very specific symbols.
%

:- func env_get_bool_true(env) = ctor_id.
:- func env_get_bool_false(env) = ctor_id.

:- func env_get_list_nil(env) = ctor_id.
:- func env_get_list_cons(env) = ctor_id.

%-----------------------------------------------------------------------%

:- pred do_var_or_wildcard(pred(X, Y, A, A, B, B),
    var_or_wildcard(X), var_or_wildcard(Y), A, A, B, B).
:- mode do_var_or_wildcard(pred(in, out, in, out, in, out) is det,
    in, out, in, out, in, out) is det.
:- mode do_var_or_wildcard(pred(in, out, in, out, in, out) is semidet,
    in, out, in, out, in, out) is semidet.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

:- import_module list.
:- import_module map.
:- import_module require.

:- import_module builtins.

%-----------------------------------------------------------------------%

    % TODO, use a radix structure.  Lookup errors can be more informative.
    %
:- type env
    --->    env(
                e_map           :: map(q_name, env_entry),
                e_typemap       :: map(q_name, type_entry),
                e_resmap        :: map(q_name, resource_id),
                e_lambdas       :: map(string, func_id),

                % The set of uninitialised variables
                e_uninitialised :: set(var),

                % The set of letrec variables, they're also uninitialised but
                % their definition may be recursive and so we don't generate
                % an error as we do for uninitialised ones.
                e_letrec_vars   :: set(var),

                % Uninitalised variables outside this closure.
                e_inaccessable :: set(var),

                % Some times we need to look up particular constructors, whe
                % we do this we know exactly which constroctor and don't
                % need to use the normal name resolution.

                % We need to lookup bool constructors for generating ITE
                % code.
                e_bool_true     :: ctor_id,
                e_bool_false    :: ctor_id,

                % We need to lookup list constructors to handle built in
                % list syntax.
                e_list_nil      :: ctor_id,
                e_list_cons     :: ctor_id
            ).

:- type type_entry
    --->    type_entry(
                te_id           :: type_id,
                te_arity        :: arity
            ).

%-----------------------------------------------------------------------%

init(BoolTrue, BoolFalse, ListNil, ListCons) =
    env(init, init, init, init, init, init, init, BoolTrue, BoolFalse,
        ListNil, ListCons).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

env_add_uninitialised_var(Name, Var, !Env, !Varmap) :-
    env_add_var(Name, Var, !Env, !Varmap),
    !Env ^ e_uninitialised := insert(!.Env ^ e_uninitialised, Var).

env_add_and_initlalise_var(Name, Var, !Env, !Varmap) :-
    env_add_var(Name, Var, !Env, !Varmap).

:- pred env_add_var(string::in, var::out, env::in, env::out,
    varmap::in, varmap::out) is semidet.

env_add_var(Name, Var, !Env, !Varmap) :-
    ( if Name = "_" then
        unexpected($file, $pred, "Wildcard string as varname")
    else
        add_fresh_var(Name, Var, !Varmap),
        insert(q_name(Name), ee_var(Var),
            !.Env ^ e_map, Map),
        !Env ^ e_map := Map
    ).

env_initialise_var(Name, Result, !Env, !Varmap) :-
    ( if Name = "_" then
        unexpected($file, $pred, "Windcard string as varname")
    else
        ( if search(!.Env ^ e_map, q_name(Name), ee_var(Var))
        then
            ( if remove(Var, !.Env ^ e_uninitialised, Uninitialised) then
                !Env ^ e_uninitialised := Uninitialised,
                Result = ok(Var)
            else if member(Var, !.Env ^ e_inaccessable) then
                Result = inaccessible
            else if member(Var, !.Env ^ e_letrec_vars) then
                unexpected($file, $pred,
                    "Cannot set letrec variables this way")
            else
                Result = already_initialised
            )
        else
            Result = does_not_exist
        )
    ).

%-----------------------------------------------------------------------%

env_uninitialised_vars(Env) = Env ^ e_uninitialised.

env_mark_initialised(Vars, !Env) :-
    !Env ^ e_uninitialised := !.Env ^ e_uninitialised `difference` Vars.

env_enter_closure(!Env) :-
    !Env ^ e_inaccessable := !.Env ^ e_uninitialised,
    !Env ^ e_uninitialised := set.init.

%-----------------------------------------------------------------------%

env_add_for_letrec(Name, Var, !Env, !Varmap) :-
    env_add_var(Name, Var, !Env, !Varmap),
    !Env ^ e_letrec_vars := insert(!.Env ^ e_letrec_vars, Var).

env_letrec_self_recursive(Name, FuncId, !Env) :-
    lookup(!.Env ^ e_map, q_name(Name), Entry),
    ( Entry = ee_var(Var),
        det_update(q_name(Name), ee_func(FuncId), !.Env ^ e_map, Map),
        !Env ^ e_map := Map,
        det_remove(Var, !.Env ^ e_letrec_vars, LetrecVars),
        !Env ^ e_letrec_vars := LetrecVars
    ;
        ( Entry = ee_func(_)
        ; Entry = ee_constructor(_)
        ),
        unexpected($file, $pred, "Entry is not a variable")
    ).

env_letrec_defined(Name, !Env) :-
    lookup(!.Env ^ e_map, q_name(Name), Entry),
    ( Entry = ee_var(Var),
        det_remove(Var, !.Env ^ e_letrec_vars, LetrecVars),
        !Env ^ e_letrec_vars := LetrecVars
    ;
        ( Entry = ee_func(_)
        ; Entry = ee_constructor(_)
        ),
        unexpected($file, $pred, "Not a variable")
    ).

env_leave_letrec(!Env) :-
    ( if not is_empty(!.Env ^ e_letrec_vars) then
        !Env ^ e_letrec_vars := set.init
    else
        unexpected($file, $pred, "Letrec had no variables")
    ).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

env_add_func(Name, Func, !Env) :-
    insert(Name, ee_func(Func), !.Env ^ e_map, Map),
    !Env ^ e_map := Map.

env_add_func_det(Name, Func, !Env) :-
    ( if env_add_func(Name, Func, !Env) then
        true
    else
        unexpected($file, $pred, "Function already exists")
    ).

%-----------------------------------------------------------------------%

env_add_type(Name, Arity, Type, !Env) :-
    insert(Name, type_entry(Type, Arity), !.Env ^ e_typemap, Map),
    !Env ^ e_typemap := Map.

env_add_type_det(Name, Arity, Type, !Env) :-
    ( if env_add_type(Name, Arity, Type, !Env) then
        true
    else
        unexpected($file, $pred, "Type already defined")
    ).

%-----------------------------------------------------------------------%

env_add_constructor(Name, Cons, !Env) :-
    det_insert(Name, ee_constructor(Cons), !.Env ^ e_map, Map),
    !Env ^ e_map := Map.

%-----------------------------------------------------------------------%

env_add_resource(Name, ResId, !Env) :-
    insert(Name, ResId, !.Env ^ e_resmap, Map),
    !Env ^ e_resmap := Map.

env_add_resource_det(Name, ResId, !Env) :-
    det_insert(Name, ResId, !.Env ^ e_resmap, Map),
    !Env ^ e_resmap := Map.

%-----------------------------------------------------------------------%

env_import_star(Name, !Env) :-
    Map0 = !.Env ^ e_map,
    foldl(do_env_import_star(Name), Map0, Map0, Map),
    !Env ^ e_map := Map.

:- pred do_env_import_star(q_name::in, q_name::in, env_entry::in,
    map(q_name, env_entry)::in, map(q_name, env_entry)::out) is det.

do_env_import_star(Module, Name, Entry, !Map) :-
    ( if q_name_append(Module, UnqualName, Name) then
        det_insert(UnqualName, Entry, !Map)
    else
        true
    ).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

env_search(Env, QName, Result) :-
    ( if search(Env ^ e_map, QName, Entry) then
        ( Entry = ee_var(Var),
            ( if member(Var, Env ^ e_inaccessable) then
                Result = inaccessible
            else if member(Var, Env ^ e_uninitialised) then
                Result = not_initaliased
            else if member(Var, Env ^ e_letrec_vars) then
                Result = maybe_cyclic_retlec
            else
                Result = ok(Entry)
            )
        ;
            ( Entry = ee_func(_)
            ; Entry = ee_constructor(_)
            ),
            Result = ok(Entry)
        )
    else
        Result = not_found
    ).

env_lookup_function(Env, QName, FuncId) :-
    ( if env_search(Env, QName, ok(ee_func(FuncIdPrime))) then
        FuncId = FuncIdPrime
    else
        unexpected($file, $pred, "Entry not found or not a function")
    ).

env_search_type(Env, QName, TypeId, Arity) :-
    search(Env ^ e_typemap, QName, type_entry(TypeId, Arity)).

env_lookup_type(Env, QName, TypeId, Arity) :-
    ( if env_search_type(Env, QName, TypeIdPrime, ArityPrime) then
        TypeId = TypeIdPrime,
        Arity = ArityPrime
    else
        unexpected($file, $pred, "Type not found")
    ).

env_search_constructor(Env, QName, CtorId) :-
    env_search(Env, QName, ok(ee_constructor(CtorId))).

%-----------------------------------------------------------------------%

env_operator_entry(Env, Op, Entry) :-
    env_operator_name(Op, Name),
    env_search(Env, nq_to_q_name(Name), ok(Entry)),
    ( Entry = ee_func(_)
    ; Entry = ee_constructor(_)
    ).

:- pred env_operator_name(ast_bop, nq_name).
:- mode env_operator_name(in, out) is semidet.

env_operator_name(b_add,            builtin_add_int).
env_operator_name(b_sub,            builtin_sub_int).
env_operator_name(b_mul,            builtin_mul_int).
env_operator_name(b_div,            builtin_div_int).
env_operator_name(b_mod,            builtin_mod_int).
env_operator_name(b_gt,             builtin_gt_int).
env_operator_name(b_lt,             builtin_lt_int).
env_operator_name(b_gteq,           builtin_gteq_int).
env_operator_name(b_lteq,           builtin_lteq_int).
env_operator_name(b_eq,             builtin_eq_int).
env_operator_name(b_neq,            builtin_neq_int).
env_operator_name(b_logical_and,    builtin_and_bool).
env_operator_name(b_logical_or,     builtin_or_bool).
env_operator_name(b_concat,         builtin_concat_string).
env_operator_name(b_list_cons,      builtin_cons_list).

env_unary_operator_func(Env, UOp, FuncId) :-
    env_unary_operator_name(UOp, Name),
    get_builtin_func(Env, nq_to_q_name(Name), FuncId).

:- pred env_unary_operator_name(ast_uop, nq_name).
:- mode env_unary_operator_name(in, out) is det.

env_unary_operator_name(u_minus,    builtin_minus_int).
env_unary_operator_name(u_not,      builtin_not_bool).

:- pred get_builtin_func(env::in, q_name::in, func_id::out) is semidet.

get_builtin_func(Env, Name, FuncId) :-
    env_search(Env, Name, Result),
    require_complete_switch [Result]
    ( Result = ok(Entry),
        require_complete_switch [Entry]
        ( Entry = ee_var(_),
            unexpected($file, $pred, "var")
        ; Entry = ee_constructor(_),
            unexpected($file, $pred, "constructor")
        ; Entry = ee_func(FuncId)
        )
    ; Result = not_found,
        false
    ;
        ( Result = not_initaliased
        ; Result = inaccessible
        ; Result = maybe_cyclic_retlec
        ),
        unexpected($file, $pred, "unexpected state")
    ).

%-----------------------------------------------------------------------%

env_search_resource(Env, QName, ResId) :-
    search(Env ^ e_resmap, QName, ResId).

env_lookup_resource(Env, QName, ResId) :-
    lookup(Env ^ e_resmap, QName, ResId).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

clobber_lambda(Name, context(_, Line, Col)) =
    string.format("lambda_l%d_%s_c%d", [i(Line), s(Name), i(Col)]).

env_add_lambda(Name, FuncId, !Env) :-
    det_insert(Name, FuncId, !.Env ^ e_lambdas, Lambdas),
    !Env ^ e_lambdas := Lambdas.

env_lookup_lambda(Env, Name, FuncId) :-
    lookup(Env ^ e_lambdas, Name, FuncId).

%-----------------------------------------------------------------------%

env_get_bool_true(Env) = Env ^ e_bool_true.
env_get_bool_false(Env) = Env ^ e_bool_false.

env_get_list_nil(Env) = Env ^ e_list_nil.
env_get_list_cons(Env) = Env ^ e_list_cons.

%-----------------------------------------------------------------------%

do_var_or_wildcard(Pred, var(Name), var(Var), !Env, !Varmap) :-
    Pred(Name, Var, !Env, !Varmap).
do_var_or_wildcard(_, wildcard, wildcard, !Env, !Varmap).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
