%-----------------------------------------------------------------------%
% vim: ts=4 sw=4 et
%-----------------------------------------------------------------------%
:- module builtins.
%
% Copyright (C) Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
% Plasma builtins.
%
% Builtins belong in the builtin module which is implicitly imported, both
% with and without the "builtin" qualifier during compilation of any module.
% Builtins may include functions, types and their constructors, interfaces
% and interface implementations.
%
% There are two main types of builtin function, with sub-types:
%
%  + Non-foreign
%  + Foreign
%
% Non-foreign
% ===========
%
% Non-foreign builtins are completely handled by the compiler, by the time
% the runtime is involved they look like regular Plasma code.
%
% Core builtins (bit_core)
% ------------------------
%
% Any procedure that could be written in Plasma, but it instead provided by
% the compiler and compiled (from Core representation, hence the name) with
% the program.  bool_to_string is an example, these builtins have their core
% definitions in this module.
%
% PZ inline builtins (bit_inline_pz)
% ----------------------------------
%
% This covers arithmetic operators and other small "functions" that are
% equivalent to one or maybe 2-3 PZ instructions.  core_to_pz will convert
% calls to these functions into their native PZ bytecodes.  It also
% generates function bodies for these so higher-order references can call to
% them.
%
% Foreign
% =======
%
% The compiler passes calls to foreign builtins through to the runtime where
% they look like references to the imported Builtin module.  pz_builtin.cpp
% decides how each foreign builtin is implemented.  So these are all bit_rts
% builtins.
%
% Runtime inline
% --------------
%
% These builtins are stored as a sequence of PZ instructions within the
% runtime, they're executed just like normal procedures, their definitions
% are simply provided by the runtime rather than a .pz file.
%
% PZ builtins
% -----------
%
% Just like runtime inline builtins, these are a series of PZ instructions.
% The difference is they arn't callable by the programmer, usually being
% responsible for data tagging.
%
% Foreign builtins
% ----------------
%
% These mostly cover operating system services.  They are implemented in
% pz_run_*.c and are transformed when the program is read into an opcode
% that will cause the C procedure built into the RTS to be executed.  The
% specifics depend on which pz_run_*.c file is used.
%
% They are very similar to foreign code generally, but marked as an import
% rather than foreign in the PZ bytecode files since they have a different
% module name.
%
%-----------------------------------------------------------------------%

:- interface.

:- import_module map.

:- import_module common_types.
:- import_module core.
:- import_module core.types.
:- import_module pre.
:- import_module pre.env.
:- import_module pz.
:- import_module pz.pz_ds.
:- import_module q_name.

:- type builtin_item
    --->    bi_func(func_id)
    ;       bi_ctor(ctor_id)
    ;       bi_resource(resource_id)
    ;       bi_type(type_id, arity)
    ;       bi_type_builtin(builtin_type).

:- type builtin_map --->
    builtin_map(
        % Items that should be avaiable without any module qualification.
        bm_root_map         :: map(nq_name, builtin_item),

        % Items that should be available under the builtin_module_name
        % module.
        bm_builtin_map      :: map(nq_name, builtin_item)
    ).

    % setup_builtins(Map, Operators, !Core)
    %
:- pred setup_builtins(builtin_map::out,
    operators::out, core::in, core::out) is det.

:- func builtin_module_name = q_name.

%-----------------------------------------------------------------------%
%
% PZ Builtins
%

:- type pz_builtin_ids
    --->    pz_builtin_ids(
                pbi_make_tag        :: pzi_id,
                pbi_shift_make_tag  :: pzi_id,
                pbi_break_tag       :: pzi_id,
                pbi_break_shift_tag :: pzi_id,
                pbi_unshift_value   :: pzi_id,

                % A struct containing only a secondary tag.
                % TODO: actually make this imported so that the runtime
                % structures can be shared easily.
                pbi_stag_struct     :: pzs_id
            ).

    % Setup procedures that are PZ builtins but not Plasma builtins.  For
    % example things like tagged pointer manipulation.
    %
:- pred setup_pz_builtin_procs(pz_builtin_ids::out, pz::in, pz::out) is det.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

:- import_module list.
:- import_module pair.
:- import_module require.
:- import_module set.

:- import_module context.
:- import_module core.code.
:- import_module core.function.
:- import_module core.resource.
:- import_module core_to_pz.
:- import_module pz.code.
:- import_module varmap.

%-----------------------------------------------------------------------%

setup_builtins(!:Map, Operators, !Core) :-
    !:Map = builtin_map(init, init),
    setup_core_types(MaybeType, !Map, !Core),
    setup_bool_builtins(BoolType, BoolTrue, BoolFalse, BoolAnd, BoolOr,
        BoolNot, !Map, !Core),
    setup_int_builtins(BoolType,
        IntAdd, IntSub, IntMul, IntDiv, IntMod,
        IntGt, IntLt, IntGtEq, IntLtEq, IntEq, IntNEq, IntMinus,
        !Map, !Core),
    setup_list_builtins(ListType, ListNil, ListCons, !Map, !Core),
    setup_string_builtins(BoolType, MaybeType,
        StringConcat, !Map, !Core),
    setup_misc_builtins(BoolType, BoolTrue, BoolFalse, !Map, !Core),

    Operators = operators(
        IntAdd, IntSub, IntMul, IntDiv, IntMod,
        IntGt, IntLt, IntGtEq, IntLtEq, IntEq, IntNEq, IntMinus,
        BoolTrue, BoolFalse, BoolAnd, BoolOr, BoolNot,
        ListType, ListNil, ListCons,
        StringConcat),

    foldl(make_body_for_inline, core_all_functions(!.Core), !Core).

:- pred setup_core_types(type_id::out, builtin_map::in, builtin_map::out,
    core::in, core::out) is det.

setup_core_types(MaybeType, !Map, !Core) :-
    foldl((pred(Type::in, M0::in, M::out) is det :-
            builtin_type_name(Type, Name),
            root_name(Name, bi_type_builtin(Type), M0, M)
        ), [int, codepoint, string, string_pos], !Map),

    core_allocate_type_id(MaybeType, !Core),
    MaybeParamName = "v",

    NoneName = nq_name_det("None"),
    NoneQName = q_name_append(builtin_module_name, NoneName),
    core_allocate_ctor_id(NoneId, !Core),
    core_set_constructor(NoneId, NoneQName, MaybeType,
        constructor(NoneQName, [MaybeParamName], []), !Core),
    root_name(NoneName, bi_ctor(NoneId), !Map),

    SomeName = nq_name_det("Some"),
    SomeQName = q_name_append(builtin_module_name, SomeName),
    core_allocate_ctor_id(SomeId, !Core),
    core_set_constructor(SomeId, SomeQName, MaybeType,
        constructor(SomeQName, [MaybeParamName], [
            type_field(q_name_append_str(builtin_module_name, "value"),
                type_variable(MaybeParamName))]), !Core),
    root_name(SomeName, bi_ctor(SomeId), !Map),

    MaybeName = nq_name_det("Maybe"),
    core_set_type(MaybeType,
        type_init(q_name_append(builtin_module_name, MaybeName),
            [MaybeParamName], [NoneId, SomeId], so_private, i_imported,
            builtin_context),
        !Core),
    root_name(MaybeName, bi_type(MaybeType, arity(1)), !Map).

    % If a function is implemented by inlining PZ instructions during
    % codegen, then give it a definition that does the same so it can be
    % used as a higher order value.
    %
:- pred make_body_for_inline(pair(func_id, function)::in,
    core::in, core::out) is det.

make_body_for_inline(FuncId - Function0, !Core) :-
    ( if func_builtin_inline_pz(Function0, _) then
        func_get_type_signature(Function0, ParamTypes, ReturnTypes, Arity),
        func_get_resource_signature(Function0, Uses, Observes),
        some [!Varmap, !Typemap, !CodeInfo] (
            !:Varmap = varmap.init,
            !:Typemap = init,
            map_foldl2(add_var_with_type, ParamTypes, Params, !Varmap,
                !Typemap),
            % The whacky thing here is that to implement a function whose
            % contents get replaced by a list of PZ instructions, we implement
            % it as a call to itself, because that direct call will be replaced
            % with the PZ instructions during codegen.
            Callee = c_plain(FuncId),
            Resources = resources(Uses, Observes),
            !:CodeInfo = code_info_init(o_builtin),
            code_info_set_arity(Arity, !CodeInfo),
            code_info_set_types(ReturnTypes, !CodeInfo),
            % XXX: If we add extra parts to code_info in the future then
            % this may be incomplete.  We need a typesafe way to make a
            % complete one or we should run this code through the
            % typechecker etc.
            Expr = expr(e_call(Callee, Params, Resources), !.CodeInfo),
            func_set_body(!.Varmap, Params, [], Expr, !.Typemap,
                Function0, Function),
            core_set_function(FuncId, Function, !Core)
        )
    else
        true
    ).

:- pred add_var_with_type(type_::in, var::out, varmap::in, varmap::out,
    map(var, type_)::in, map(var, type_)::out) is det.

add_var_with_type(Type, Var, !Varmap, !Typemap) :-
    add_anon_var(Var, !Varmap),
    det_insert(Var, Type, !Typemap).

%-----------------------------------------------------------------------%

:- pred setup_bool_builtins(type_id::out, ctor_id::out, ctor_id::out,
    func_id::out, func_id::out, func_id::out,
    builtin_map::in, builtin_map::out, core::in, core::out) is det.

setup_bool_builtins(BoolId, TrueId, FalseId, AndId, OrId, NotId, !Map, !Core) :-
    core_allocate_type_id(BoolId, !Core),

    FalseName = nq_name_det("False"),
    FalseQName = q_name_append(builtin_module_name, FalseName),
    core_allocate_ctor_id(FalseId, !Core),
    core_set_constructor(FalseId, FalseQName, BoolId,
        constructor(FalseQName, [], []), !Core),
    root_name(FalseName, bi_ctor(FalseId), !Map),

    TrueName = nq_name_det("True"),
    TrueQName = q_name_append(builtin_module_name, TrueName),
    core_allocate_ctor_id(TrueId, !Core),
    core_set_constructor(TrueId, TrueQName, BoolId,
        constructor(TrueQName, [], []), !Core),
    root_name(TrueName, bi_ctor(TrueId), !Map),

    % NOTE: False is first so that it is allocated 0 for its tag, and true
    % will be allocated 1 for its tag, this will make interoperability
    % easier.
    BoolName = nq_name_det("Bool"),
    core_set_type(BoolId,
        type_init(q_name_append(builtin_module_name, BoolName), [],
            [FalseId, TrueId], so_private, i_imported, builtin_context),
        !Core),
    root_name(BoolName, bi_type(BoolId, arity(0)), !Map),

    BoolWidth = bool_width,
    BoolNotName = nq_name_det("bool_not"),
    register_builtin_func_builtin(BoolNotName,
        func_init_builtin_inline_pz(
            q_name_append(builtin_module_name, BoolNotName),
            [type_ref(BoolId, [])], [type_ref(BoolId, [])], init, init,
            [pzi_not(BoolWidth)]),
        NotId, !Map, !Core),

    register_bool_biop(BoolId, "bool_and",
        [pzi_and(BoolWidth)], AndId, !Map, !Core),
    register_bool_biop(BoolId, "bool_or",
        [pzi_or(BoolWidth)], OrId, !Map, !Core).

:- pred register_bool_biop(type_id::in, string::in, list(pz_instr)::in,
    func_id::out, builtin_map::in, builtin_map::out, core::in, core::out)
    is det.

register_bool_biop(BoolType, NameStr, Defn, FuncId, !Map, !Core) :-
    Name = nq_name_det(NameStr),
    FName = q_name_append(builtin_module_name, Name),
    register_builtin_func_builtin(Name,
        func_init_builtin_inline_pz(FName,
            [type_ref(BoolType, []), type_ref(BoolType, [])],
            [type_ref(BoolType, [])],
            init, init,
            Defn),
        FuncId, !Map, !Core).

%-----------------------------------------------------------------------%

:- pred setup_int_builtins(type_id::in,
    func_id::out, func_id::out, func_id::out, func_id::out, func_id::out,
    func_id::out, func_id::out, func_id::out, func_id::out, func_id::out,
    func_id::out, func_id::out,
    builtin_map::in, builtin_map::out, core::in, core::out) is det.

setup_int_builtins(BoolType,
        AddId, SubId, MulId, DivId, ModId,
        GtId, LtId, GtEqId, LtEqId, EqId, NEqId, MinusId,
        !Map, !Core) :-
    register_int_fn2("int_add", [pzi_add(pzw_fast)], AddId,
        !Map, !Core),
    register_int_fn2("int_sub", [pzi_sub(pzw_fast)], SubId,
        !Map, !Core),
    register_int_fn2("int_mul", [pzi_mul(pzw_fast)], MulId,
        !Map, !Core),
    % Mod and div can maybe be combined into one operator, and optimised at
    % PZ load time.
    register_int_fn2("int_div", [pzi_div(pzw_fast)], DivId,
        !Map, !Core),
    register_int_fn2("int_mod", [pzi_mod(pzw_fast)], ModId,
        !Map, !Core),

    % TODO: remove the extend operation once we fix how booleans are
    % stored.
    BoolWidth = bool_width,
    require(unify(BoolWidth, pzw_ptr),
        "Fix this code once we fix bool storage"),
    register_int_comp(BoolType, "int_gt", [
            pzi_gt_s(pzw_fast),
            pzi_ze(pzw_fast, pzw_ptr)],
        GtId, !Map, !Core),
    register_int_comp(BoolType, "int_lt", [
            pzi_lt_s(pzw_fast),
            pzi_ze(pzw_fast, pzw_ptr)],
        LtId, !Map, !Core),
    register_int_comp(BoolType, "int_gteq", [
            pzi_lt_s(pzw_fast),
            pzi_not(pzw_fast),
            pzi_ze(pzw_fast, pzw_ptr)],
        GtEqId, !Map, !Core),
    register_int_comp(BoolType, "int_lteq", [
            pzi_gt_s(pzw_fast),
            pzi_not(pzw_fast),
            pzi_ze(pzw_fast, pzw_ptr)],
        LtEqId, !Map, !Core),
    register_int_comp(BoolType, "int_eq", [
            pzi_eq(pzw_fast),
            pzi_ze(pzw_fast, pzw_ptr)],
        EqId, !Map, !Core),
    register_int_comp(BoolType, "int_neq", [
            pzi_eq(pzw_fast),
            pzi_not(pzw_fast),
            pzi_ze(pzw_fast, pzw_ptr)],
        NEqId, !Map, !Core),

    register_int_fn1("int_minus",
        [pzi_load_immediate(pzw_fast, im_i32(0i32)),
         pzi_roll(2),
         pzi_sub(pzw_fast)],
        MinusId, !Map, !Core),

    % Register the builtin bitwise functions..
    % TODO: make the number of bits to shift a single byte.
    register_int_fn2("int_lshift",
        [pzi_trunc(pzw_fast, pzw_8),
         pzi_lshift(pzw_fast)], _, !Map, !Core),
    register_int_fn2("int_rshift",
        [pzi_trunc(pzw_fast, pzw_8),
         pzi_rshift(pzw_fast)], _, !Map, !Core),
    register_int_fn2("int_and", [pzi_and(pzw_fast)], _, !Map, !Core),
    register_int_fn2("int_or", [pzi_or(pzw_fast)], _, !Map, !Core),
    register_int_fn2("int_xor",
        [pzi_xor(pzw_fast)], _, !Map, !Core),
    register_int_fn1("int_comp",
        [pzi_load_immediate(pzw_32, im_i32(-1i32)),
         pzi_se(pzw_32, pzw_fast),
         pzi_xor(pzw_fast)],
        _, !Map, !Core).

:- pred register_int_fn1(string::in, list(pz_instr)::in, func_id::out,
    builtin_map::in, builtin_map::out, core::in, core::out) is det.

register_int_fn1(NameStr, Defn, FuncId, !Map, !Core) :-
    Name = nq_name_det(NameStr),
    FName = q_name_append(builtin_module_name, Name),
    register_builtin_func_builtin(Name,
        func_init_builtin_inline_pz(FName,
            [builtin_type(int)], [builtin_type(int)],
            init, init, Defn),
        FuncId, !Map, !Core).

:- pred register_int_fn2(string::in, list(pz_instr)::in, func_id::out,
    builtin_map::in, builtin_map::out, core::in, core::out) is det.

register_int_fn2(NameStr, Defn, FuncId, !Map, !Core) :-
    Name = nq_name_det(NameStr),
    FName = q_name_append(builtin_module_name, Name),
    register_builtin_func_builtin(Name,
        func_init_builtin_inline_pz(FName,
            [builtin_type(int), builtin_type(int)],
            [builtin_type(int)],
            init, init, Defn),
        FuncId, !Map, !Core).

:- pred register_int_comp(type_id::in, string::in, list(pz_instr)::in,
    func_id::out, builtin_map::in, builtin_map::out,
    core::in, core::out) is det.

register_int_comp(BoolType, NameStr, Defn, FuncId, !Map, !Core) :-
    Name = nq_name_det(NameStr),
    FName = q_name_append(builtin_module_name, Name),
    register_builtin_func_builtin(Name,
        func_init_builtin_inline_pz(FName,
            [builtin_type(int), builtin_type(int)],
            [type_ref(BoolType, [])],
            init, init, Defn),
        FuncId, !Map, !Core).

:- pred setup_list_builtins(type_id::out, ctor_id::out, ctor_id::out,
    builtin_map::in, builtin_map::out, core::in, core::out) is det.

setup_list_builtins(ListId, NilId, ConsId, !Map, !Core) :-
    core_allocate_type_id(ListId, !Core),
    T = "T",

    NilName = nq_name_det("list_nil"),
    NilQName = q_name_append(builtin_module_name, NilName),
    core_allocate_ctor_id(NilId, !Core),
    core_set_constructor(NilId, NilQName, ListId,
        constructor(NilQName, [T], []), !Core),
    builtin_name(NilName, bi_ctor(NilId), !Map),

    Head = q_name_append_str(builtin_module_name, "head"),
    Tail = q_name_append_str(builtin_module_name, "tail"),
    ConsName = nq_name_det("list_cons"),
    ConsQName = q_name_append(builtin_module_name, ConsName),
    core_allocate_ctor_id(ConsId, !Core),
    core_set_constructor(ConsId, ConsQName, ListId,
        constructor(ConsQName, [T],
        [type_field(Head, type_variable(T)),
         type_field(Tail, type_ref(ListId, [type_variable(T)]))]), !Core),
    builtin_name(ConsName, bi_ctor(ConsId), !Map),

    core_set_type(ListId,
        type_init(q_name_append_str(builtin_module_name, "List"), [T],
            [NilId, ConsId], so_private, i_imported, builtin_context),
        !Core),

    root_name(nq_name_det("List"), bi_type(ListId, arity(1)), !Map).

%-----------------------------------------------------------------------%

:- pred setup_misc_builtins(type_id::in, ctor_id::in, ctor_id::in,
    builtin_map::in, builtin_map::out, core::in, core::out) is det.

setup_misc_builtins(BoolType, BoolTrue, BoolFalse, !Map, !Core) :-
    register_builtin_resource(nq_name_det("IO"), r_io, RIO, !Map, !Core),

    PrintName = q_name_append_str(builtin_module_name, "print"),
    register_builtin_func_root(nq_name_det("print"),
        func_init_builtin_rts(PrintName,
            [builtin_type(string)], [], list_to_set([RIO]), init),
        _, !Map, !Core),

    core_allocate_type_id(IOResultType, !Core),

    % There's currently no error constructor. but there should be, currently
    % the runtime just aborts.
    OkParamName = "v",
    OkName = nq_name_det("Ok"),
    OkQName = q_name_append(builtin_module_name, OkName),
    core_allocate_ctor_id(OkId, !Core),
    core_set_constructor(OkId, OkQName, IOResultType,
        constructor(OkQName, [OkParamName], [
            type_field(q_name_append_str(builtin_module_name, "value"),
                type_variable(OkParamName))]), !Core),
    root_name(OkName, bi_ctor(OkId), !Map),

    EOFName = nq_name_det("EOF"),
    EOFQName = q_name_append(builtin_module_name, EOFName),
    core_allocate_ctor_id(EOFId, !Core),
    core_set_constructor(EOFId, EOFQName, IOResultType,
        constructor(EOFQName, [OkParamName], []), !Core),
    root_name(EOFName, bi_ctor(EOFId), !Map),

    IOResultName = nq_name_det("IOResult"),
    core_set_type(IOResultType,
        type_init(q_name_append(builtin_module_name, IOResultName),
            [OkParamName], [OkId, EOFId], so_private, i_imported, builtin_context),
        !Core),
    root_name(IOResultName, bi_type(IOResultType, arity(1)), !Map),

    ReadlnName = q_name_append_str(builtin_module_name, "readline"),
    register_builtin_func_root(nq_name_det("readline"),
        func_init_builtin_rts(ReadlnName,
            [], [type_ref(IOResultType, [builtin_type(string)])],
            list_to_set([RIO]), init),
        _, !Map, !Core),

    IntToStringName = q_name_append_str(builtin_module_name, "int_to_string"),
    register_builtin_func_root(nq_name_det("int_to_string"),
        func_init_builtin_rts(IntToStringName,
            [builtin_type(int)], [builtin_type(string)], init, init),
        _, !Map, !Core),

    BoolToStringName = q_name_append_str(builtin_module_name, "bool_to_string"),
    BoolToString0 = func_init_builtin_core(BoolToStringName,
        [type_ref(BoolType, [])], [builtin_type(string)], init, init),
    define_bool_to_string(BoolTrue, BoolFalse, BoolToString0, BoolToString),
    register_builtin_func_root(nq_name_det("bool_to_string"), BoolToString,
        _, !Map, !Core),

    SetParameterName = q_name_append_str(builtin_module_name, "set_parameter"),
    register_builtin_func_builtin(nq_name_det("set_parameter"),
        func_init_builtin_rts(SetParameterName,
            [builtin_type(string), builtin_type(int)],
            [type_ref(BoolType, [])],
            list_to_set([RIO]), init),
        _, !Map, !Core),

    GetParameterName = q_name_append_str(builtin_module_name, "get_parameter"),
    register_builtin_func_builtin(nq_name_det("get_parameter"),
        func_init_builtin_rts(GetParameterName,
            [builtin_type(string)],
            [type_ref(BoolType, []), builtin_type(int)],
            init, list_to_set([RIO])),
        _, !Map, !Core),

    EnvironmentName = nq_name_det("Environment"),
    EnvironmentQName = q_name_append(builtin_module_name, EnvironmentName),
    register_builtin_resource(EnvironmentName,
        r_other(EnvironmentQName, RIO, so_private, i_imported, builtin_context),
        REnv, !Map, !Core),
    SetenvName = q_name_append_str(builtin_module_name, "setenv"),
    register_builtin_func_root(nq_name_det("setenv"),
        func_init_builtin_rts(SetenvName,
            [builtin_type(string), builtin_type(string)],
            [type_ref(BoolType, [])],
            list_to_set([REnv]), init),
        _, !Map, !Core),

    TimeName = nq_name_det("Time"),
    TimeQName = q_name_append(builtin_module_name, TimeName),
    register_builtin_resource(TimeName,
        r_other(TimeQName, RIO, so_private, i_imported, builtin_context),
        RTime, !Map, !Core),
    GettimeofdayName = q_name_append_str(builtin_module_name, "gettimeofday"),
    register_builtin_func_builtin(nq_name_det("gettimeofday"),
        func_init_builtin_rts(GettimeofdayName, [],
            [type_ref(BoolType, []), builtin_type(int), builtin_type(int)],
            init, list_to_set([RTime])),
        _, !Map, !Core),

    DieName = nq_name_det("die"),
    DieQName = q_name_append(builtin_module_name, DieName),
    register_builtin_func_builtin(DieName,
        func_init_builtin_rts(DieQName, [builtin_type(string)], [],
            init, init),
        _, !Map, !Core).

%-----------------------------------------------------------------------%

:- pred setup_string_builtins(type_id::in, type_id::in,
    func_id::out,
    builtin_map::in, builtin_map::out, core::in, core::out) is det.

setup_string_builtins(BoolType, MaybeType, StringConcat, !Map, !Core) :-
    core_allocate_type_id(CodepointCategoryId, !Core),

    % TODO: Implement more character classes.
    WhitespaceName = nq_name_det("Whitespace"),
    WhitespaceQName = q_name_append(builtin_module_name, WhitespaceName),
    core_allocate_ctor_id(WhitespaceId, !Core),
    core_set_constructor(WhitespaceId, WhitespaceQName, CodepointCategoryId,
        constructor(WhitespaceQName, [], []), !Core),
    root_name(WhitespaceName, bi_ctor(WhitespaceId), !Map),

    OtherName = nq_name_det("Other"),
    OtherQName = q_name_append(builtin_module_name, OtherName),
    core_allocate_ctor_id(OtherId, !Core),
    core_set_constructor(OtherId, OtherQName, CodepointCategoryId,
        constructor(OtherQName, [], []), !Core),
    root_name(OtherName, bi_ctor(OtherId), !Map),

    CodepointCategoryTypeName = nq_name_det("CodepointCategory"),
    core_set_type(CodepointCategoryId,
        type_init(q_name_append(builtin_module_name,
                CodepointCategoryTypeName), [],
            [WhitespaceId, OtherId], so_private, i_imported, builtin_context),
        !Core),
    root_name(CodepointCategoryTypeName,
        bi_type(CodepointCategoryId, arity(0)), !Map),

    CodepointCategoryName = nq_name_det("codepoint_category"),
    register_builtin_func_root(CodepointCategoryName,
        func_init_builtin_rts(
            q_name_append(builtin_module_name, CodepointCategoryName),
            [builtin_type(codepoint)],
            [type_ref(CodepointCategoryId, [])],
            init, init),
        _, !Map, !Core),

    CPToStringName = nq_name_det("codepoint_to_string"),
    register_builtin_func_root(CPToStringName,
        func_init_builtin_rts(
            q_name_append(builtin_module_name, CPToStringName),
            [builtin_type(codepoint)],
            [builtin_type(string)],
            init, init),
        _, !Map, !Core),


    CPToNumName = nq_name_det("codepoint_to_number"),
    register_builtin_func_root(CPToNumName,
        func_init_builtin_inline_pz(
            q_name_append(builtin_module_name, CPToNumName),
            [builtin_type(codepoint)],
            [builtin_type(int)],
            init, init, [pzi_ze(pzw_32, pzw_fast)]),
        _, !Map, !Core),

    IntToCPName = nq_name_det("int_to_codepoint"),
    register_builtin_func_builtin(IntToCPName,
        func_init_builtin_inline_pz(
            q_name_append(builtin_module_name, IntToCPName),
            [builtin_type(int)],
            [builtin_type(codepoint)],
            init, init, [pzi_trunc(pzw_fast, pzw_32)]),
        _, !Map, !Core),

    StringConcatName = nq_name_det("string_concat"),
    register_builtin_func_builtin(StringConcatName,
        func_init_builtin_rts(
            q_name_append(builtin_module_name, StringConcatName),
            [builtin_type(string), builtin_type(string)],
            [builtin_type(string)],
            init, init),
        StringConcat, !Map, !Core),

    StrposForwadName = nq_name_det("strpos_forward"),
    register_builtin_func_root(StrposForwadName,
        func_init_builtin_rts(
            q_name_append(builtin_module_name, StrposForwadName),
            [builtin_type(string_pos)],
            [builtin_type(string_pos)],
            init, init),
        _, !Map, !Core),

    StrposBackwardName = nq_name_det("strpos_backward"),
    register_builtin_func_root(StrposBackwardName,
        func_init_builtin_rts(
            q_name_append(builtin_module_name, StrposBackwardName),
            [builtin_type(string_pos)],
            [builtin_type(string_pos)],
            init, init),
        _, !Map, !Core),

    StrposNextName = nq_name_det("strpos_next"),
    register_builtin_func_root(StrposNextName,
        func_init_builtin_rts(
            q_name_append(builtin_module_name, StrposNextName),
            [builtin_type(string_pos)],
                [type_ref(MaybeType, [builtin_type(codepoint)])],
            init, init),
        _, !Map, !Core),

    StrposPrevName = nq_name_det("strpos_prev"),
    register_builtin_func_root(StrposPrevName,
        func_init_builtin_rts(
            q_name_append(builtin_module_name, StrposPrevName),
            [builtin_type(string_pos)],
                [type_ref(MaybeType, [builtin_type(codepoint)])],
            init, init),
        _, !Map, !Core),

    StringBeginName = nq_name_det("string_begin"),
    register_builtin_func_root(StringBeginName,
        func_init_builtin_rts(
            q_name_append(builtin_module_name, StringBeginName),
            [builtin_type(string)],
            [builtin_type(string_pos)],
            init, init),
        _, !Map, !Core),

    StringEndName = nq_name_det("string_end"),
    register_builtin_func_root(StringEndName,
        func_init_builtin_rts(
            q_name_append(builtin_module_name, StringEndName),
            [builtin_type(string)],
            [builtin_type(string_pos)],
            init, init),
        _, !Map, !Core),

    StringSubstringName = nq_name_det("string_substring"),
    register_builtin_func_root(StringSubstringName,
        func_init_builtin_rts(
            q_name_append(builtin_module_name, StringSubstringName),
            [builtin_type(string_pos), builtin_type(string_pos)],
            [builtin_type(string)],
            init, init),
        _, !Map, !Core),

    StringEqualsName = nq_name_det("string_equals"),
    register_builtin_func_root(StringEqualsName,
        func_init_builtin_rts(
            q_name_append(builtin_module_name, StringEqualsName),
            [builtin_type(string), builtin_type(string)],
            [type_ref(BoolType, [])],
            init, init),
        _, !Map, !Core).

%-----------------------------------------------------------------------%

    % Register the builtin function with it's name in the root namespace.
    %
:- pred register_builtin_func_root(nq_name::in, function::in, func_id::out,
    builtin_map::in, builtin_map::out, core::in, core::out) is det.

register_builtin_func_root(Name, Func, FuncId, !Map, !Core) :-
    register_builtin_func(Func, FuncId, !Core),
    root_name(Name, bi_func(FuncId), !Map).

    % Register the builtin function with it's name in the Builtin module
    % namespace.
    %
:- pred register_builtin_func_builtin(nq_name::in, function::in, func_id::out,
    builtin_map::in, builtin_map::out, core::in, core::out) is det.

register_builtin_func_builtin(Name, Func, FuncId, !Map, !Core) :-
    register_builtin_func(Func, FuncId, !Core),
    builtin_name(Name, bi_func(FuncId), !Map).

:- pred register_builtin_func(function::in, func_id::out,
    core::in, core::out) is det.

register_builtin_func(Func, FuncId, !Core) :-
    core_allocate_function(FuncId, !Core),
    core_set_function(FuncId, Func, !Core).

:- pred register_builtin_resource(nq_name::in, resource::in,
    resource_id::out,
    builtin_map::in, builtin_map::out, core::in, core::out) is det.

register_builtin_resource(Name, Res, ResId, !Map, !Core) :-
    core_allocate_resource_id(ResId, !Core),
    core_set_resource(ResId, Res, !Core),
    root_name(Name, bi_resource(ResId), !Map).

%-----------------------------------------------------------------------%

:- pred define_bool_to_string(ctor_id::in, ctor_id::in,
    function::in, function::out) is det.

define_bool_to_string(TrueId, FalseId, !Func) :-
    some [!Varmap] (
        !:Varmap = init,
        CI = code_info_init(o_builtin),

        varmap.add_anon_var(In, !Varmap),
        TrueCase = e_case(p_ctor(make_singleton_set(TrueId), []),
            expr(e_constant(c_string("True")), CI)),
        FalseCase = e_case(p_ctor(make_singleton_set(FalseId), []),
            expr(e_constant(c_string("False")), CI)),
        Expr = expr(e_match(In, [TrueCase, FalseCase]), CI),
        func_set_body(!.Varmap, [In], [], Expr, !Func)
    ).

%-----------------------------------------------------------------------%

:- pred root_name(nq_name::in, builtin_item::in,
    builtin_map::in, builtin_map::out) is det.

root_name(Name, Item, !Map) :-
    det_insert(Name, Item, !.Map ^ bm_root_map, Map),
    !Map ^ bm_root_map := Map.

:- pred builtin_name(nq_name::in, builtin_item::in,
    builtin_map::in, builtin_map::out) is det.

builtin_name(Name, Item, !Map) :-
    det_insert(Name, Item, !.Map ^ bm_builtin_map, Map),
    !Map ^ bm_builtin_map := Map.

%-----------------------------------------------------------------------%

builtin_module_name = q_name_single("Builtin").

%-----------------------------------------------------------------------%

setup_pz_builtin_procs(BuiltinProcs, !PZ) :-
    % pz_signature([pzw_ptr, pzw_ptr], [pzw_ptr])
    pz_new_import(MakeTag, pz_import(make_tag_qname, pzit_import), !PZ),

    % pz_signature([pzw_ptr, pzw_ptr], [pzw_ptr])
    pz_new_import(ShiftMakeTag, pz_import(shift_make_tag_qname, pzit_import),
        !PZ),

    % pz_signature([pzw_ptr], [pzw_ptr, pzw_ptr])
    pz_new_import(BreakTag, pz_import(break_tag_qname, pzit_import), !PZ),

    % pz_signature([pzw_ptr], [pzw_ptr, pzw_ptr])
    pz_new_import(BreakShiftTag,
        pz_import(break_shift_tag_qname, pzit_import), !PZ),

    % pz_signature([pzw_ptr], [pzw_ptr])
    pz_new_import(UnshiftValue, pz_import(unshift_value_qname, pzit_import),
        !PZ),

    STagStruct = pz_struct([pzw_fast]),
    pz_new_struct_id(STagStructId, "Secondary tag struct", !PZ),
    pz_add_struct(STagStructId, STagStruct, !PZ),

    BuiltinProcs = pz_builtin_ids(MakeTag, ShiftMakeTag, BreakTag,
        BreakShiftTag, UnshiftValue, STagStructId).

%-----------------------------------------------------------------------%

:- func make_tag_qname = q_name.

make_tag_qname = q_name_append_str(builtin_module_name, "make_tag").

:- func shift_make_tag_qname = q_name.

shift_make_tag_qname = q_name_append_str(builtin_module_name, "shift_make_tag").

:- func break_tag_qname = q_name.

break_tag_qname = q_name_append_str(builtin_module_name, "break_tag").

:- func break_shift_tag_qname = q_name.

break_shift_tag_qname = q_name_append_str(builtin_module_name, "break_shift_tag").

:- func unshift_value_qname = q_name.

unshift_value_qname = q_name_append_str(builtin_module_name, "unshift_value").

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
