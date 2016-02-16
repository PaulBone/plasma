%-----------------------------------------------------------------------%
% Plasma core representation
% vim: ts=4 sw=4 et
%
% Copyright (C) 2015-2016 Plasma Team
% Distributed under the terms of the MIT see ../LICENSE.code
%
% This program compiles plasma modules.
%
%-----------------------------------------------------------------------%
:- module core.
%-----------------------------------------------------------------------%

:- interface.

:- include_module core.code.
:- include_module core.types.

%-----------------------------------------------------------------------%

:- import_module list.
:- import_module set.

:- import_module common_types.
:- import_module core.code.
:- import_module core.types.
:- import_module symtab.
:- import_module varmap.

%-----------------------------------------------------------------------%

:- type core.

:- func init(symbol) = core.

:- func module_name(core) = symbol.

:- pred core_register_function(symbol::in, func_id::out,
    core::in, core::out) is semidet.

:- func core_all_functions(core) = list(func_id).

    % Return all the functions whose name matches the given symbol.
    % When searching for "foo", results may include any of "foo", "bar.foo"
    % "baz.foo".
    %
    % Matching is explained in symtab.m.
    %
:- pred core_search_function(core::in, symbol::in, set(func_id)::out) is det.

    % Return the exact match.
    %
:- pred core_lookup_function(core::in, symbol::in, func_id::out) is semidet.

:- pred core_lookup_function_name(core::in, func_id::in, symbol::out) is det.

    % Return the exact match.
    %
:- pred det_core_lookup_function(core::in, symbol::in, func_id::out) is det.

:- pred core_set_function(func_id::in, function::in, core::in, core::out)
    is det.

:- pred core_get_function_det(core::in, func_id::in, function::out) is det.

%-----------------------------------------------------------------------%

:- type func_id.

:- type function.

    % function_init(SHAring, ParamTypes, ReturnTypes, UsingResources,
    %   ObservingResources) = Function
    %
:- func func_init(sharing, list(type_), list(type_), set(resource),
    set(resource)) = function.

:- func func_get_imported(function) = imported.

:- pred func_get_signature(function::in, list(type_)::out, list(type_)::out)
    is det.

:- pred func_set_body(varmap::in, list(var)::in, expr::in,
    function::in, function::out) is det.

:- pred func_get_body(function::in, varmap::out, list(var)::out,
    expr::out) is semidet.

%-----------------------------------------------------------------------%

    % In later verious resources can be named and may have types, with rules
    % about which resources contain which other resources.  For now there is
    % only an IO resource.
    %
:- type resource
    --->    r_io.

:- func resource_to_string(resource) = string.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

:- import_module int.
:- import_module map.
:- import_module maybe.
:- import_module require.
:- import_module set.

%-----------------------------------------------------------------------%

:- type core
    --->    core(
                c_module_name       :: symbol,
                c_funcs             :: map(func_id, function),
                c_func_syms         :: symtab(func_id),
                c_next_func_id      :: func_id
            ).

%-----------------------------------------------------------------------%

init(ModuleName) = core(ModuleName, init, init, func_id(0)).

module_name(Core) = Core ^ c_module_name.

%-----------------------------------------------------------------------%

:- type func_id
    --->    func_id(int).

core_register_function(Symbol, FuncId, !Core) :-
    FuncId = !.Core ^ c_next_func_id,
    symtab.insert(Symbol, FuncId, !.Core ^ c_func_syms, FuncSyms),
    !Core ^ c_func_syms := FuncSyms,
    FuncId = func_id(N),
    !Core ^ c_next_func_id := func_id(N+1).

core_all_functions(Core) = keys(Core ^ c_funcs).

core_search_function(Core, Symbol, FuncIds) :-
    search(Core ^ c_func_syms, Symbol, FuncIds).

core_lookup_function(Core, Symbol, FuncId) :-
    search_exact(Core ^ c_func_syms, Symbol, FuncId).

core_lookup_function_name(Core, FuncId, Symbol) :-
    lookup(Core ^ c_func_syms, FuncId, Symbol).

det_core_lookup_function(Core, Symbol, FuncId) :-
    ( if core_lookup_function(Core, Symbol, FuncIdPrime) then
        FuncId = FuncIdPrime
    else
        unexpected($file, $pred, "Function not found")
    ).

core_set_function(FuncId, Func, !Core) :-
    map.set(FuncId, Func, !.Core ^ c_funcs, Funcs),
    !Core ^ c_funcs := Funcs.

core_get_function_det(Core, FuncId, Func) :-
    map.lookup(Core ^ c_funcs, FuncId, Func).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- type function
    --->    function(
                f_sharing           :: sharing,
                f_signature         :: signature,
                f_maybe_func_defn   :: maybe(function_defn)
            ).
:- type signature
    --->    signature(
                % The parameter and return types are given in the order they
                % appear in function's definition.
                fs_param_types  :: list(type_),
                fs_return_types :: list(type_),
                fs_using        :: set(resource),
                fs_observing    :: set(resource)
            ).

:- type function_defn
    --->    function_defn(
                fd_var_map          :: varmap,
                fd_param_names      :: list(var),
                fd_body             :: expr
            ).

%-----------------------------------------------------------------------%

func_init(Sharing, Params, Return, Using, Observing) =
    function(Sharing, signature(Params, Return, Using, Observing), no).

func_get_imported(Func) = Imported :-
    MaybeDefn = Func ^ f_maybe_func_defn,
    ( MaybeDefn = yes(_),
        Imported = i_local
    ; MaybeDefn = no,
        Imported = i_imported
    ).

func_get_signature(Func, Inputs, Outputs) :-
    Inputs = Func ^ f_signature ^ fs_param_types,
    Outputs = Func ^ f_signature ^ fs_return_types.

func_set_body(Varmap, ParamNames, Stmts, !Function) :-
    Defn = function_defn(Varmap, ParamNames, Stmts),
    !Function ^ f_maybe_func_defn := yes(Defn).

func_get_body(Func, Varmap, ParamNames, Stmts) :-
    yes(Defn) = Func ^ f_maybe_func_defn,
    function_defn(Varmap, ParamNames, Stmts) = Defn.

%-----------------------------------------------------------------------%

resource_to_string(r_io) = "IO".

%-----------------------------------------------------------------------%
