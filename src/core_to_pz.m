%-----------------------------------------------------------------------%
% vim: ts=4 sw=4 et
%-----------------------------------------------------------------------%
:- module core_to_pz.
%
% Copyright (C) 2015-2021 Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
% Plasma core to pz conversion
%
%-----------------------------------------------------------------------%

:- interface.

:- include_module core_to_pz.data.

:- import_module io.

:- import_module core.
:- import_module core_to_pz.data.
:- import_module options.
:- import_module pz.
:- import_module pz.pz_ds.
:- import_module util.
:- import_module util.log.

%-----------------------------------------------------------------------%

:- pred core_to_pz(log_config::in, compile_options::in, core::in, pz::out,
    type_tag_map::out, constructor_data_map::out, io::di, io::uo) is det.

%-----------------------------------------------------------------------%

:- func bool_width = pz_width.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

:- import_module cord.
:- import_module list.
:- import_module map.
:- import_module pair.
:- import_module require.
:- import_module set.
:- import_module string.

:- import_module builtins.
:- import_module common_types.
:- import_module core.code.
:- import_module core.function.
:- import_module core.types.
:- import_module pz.code.
:- import_module q_name.
:- import_module util.mercury.
:- import_module util.pretty.
:- import_module varmap.

:- include_module core_to_pz.code.
:- include_module core_to_pz.closure.
:- include_module core_to_pz.locn.
:- import_module core_to_pz.code.
:- import_module core_to_pz.closure.
:- import_module core_to_pz.locn.

%-----------------------------------------------------------------------%

core_to_pz(Verbose, CompileOpts, !.Core, !:PZ, TypeTagMap, TypeCtorTagMap,
        !IO) :-
    !:PZ = init_pz([module_name(!.Core)], pzft_object),

    % Get ImportIds for builtin procedures.
    setup_pz_builtin_procs(BuiltinProcs, !PZ),

    % Make decisions about how data should be stored in memory.
    % This covers what tag values to use for each constructor and the IDs of
    % each structure.
    pz_new_struct_id(EnvStructId, "Module struct", !PZ),
    verbose_output(Verbose, "Generating type layout (constructor tags)\n",
        !IO),
    gen_constructor_data(!.Core, BuiltinProcs, TypeTagMap, TypeCtorTagMap,
        !PZ),

    some [!ModuleClo, !LocnMap, !FilenameDataMap] (
        !:ModuleClo = closure_builder_init(EnvStructId),
        !:LocnMap = vls_init(EnvStructId),
        !:FilenameDataMap = map.init,

        % Generate constants.
        verbose_output(Verbose, "Generating constants\n", !IO),
        gen_const_data(!.Core, !LocnMap, !ModuleClo, !FilenameDataMap, !PZ),

        % Generate functions.
        verbose_output(Verbose,
            format("Generating %d functions\n", [i(length(Funcs))]), !IO),
        Funcs = core_all_functions(!.Core),
        foldl3(make_proc_and_struct_ids, Funcs, !LocnMap, !ModuleClo, !PZ),
        foldl(gen_func(CompileOpts, !.Core, !.LocnMap, BuiltinProcs,
                !.FilenameDataMap, TypeTagMap, TypeCtorTagMap, EnvStructId),
            Funcs, !PZ),

        % Finalize the module closure.
        verbose_output(Verbose, "Generating module closure\n", !IO),
        closure_finalize_data(!.ModuleClo, EnvDataId, !PZ),
        ExportFuncs0 = core_all_exported_functions(!.Core),

        % Export and mark the entrypoint.
        verbose_output(Verbose, "Generating entrypoint and exports\n", !IO),
        Candidates = core_entry_candidates(!.Core),
        set.fold(create_entry_candidate(!.Core, !.LocnMap, EnvDataId),
            Candidates, !PZ),
        CandidateIDs = map(entry_get_func_id, Candidates),
        ExportFuncs = filter(
            pred(Id - _::in) is semidet :- not member(Id, CandidateIDs),
            ExportFuncs0),

        % Export the other exported functions.
        map_foldl(create_export(!.LocnMap, EnvDataId), ExportFuncs, _, !PZ)
    ).

:- func entry_get_func_id(core_entrypoint) = func_id.

entry_get_func_id(entry_plain(FuncId)) = FuncId.
entry_get_func_id(entry_argv(FuncId)) = FuncId.

:- pred create_entry_candidate(core::in, val_locn_map_static::in,
    pzd_id::in, core_entrypoint::in, pz::in, pz::out) is det.

create_entry_candidate(Core, LocnMap, EnvDataId, Entrypoint, !PZ) :-
    ( Entrypoint = entry_plain(EntryFuncId),
        Signature = pz_es_plain
    ; Entrypoint = entry_argv(EntryFuncId),
        Signature = pz_es_args
    ),
    core_get_function_det(Core, EntryFuncId, EntryFunc),
    create_export(LocnMap, EnvDataId,
        EntryFuncId - EntryFunc, EntryClo, !PZ),
    pz_add_entry_candidate(EntryClo, Signature, !PZ).

:- pred create_export(val_locn_map_static::in, pzd_id::in,
    pair(func_id, function)::in, pzc_id::out, pz::in, pz::out) is det.

create_export(LocnMap, ModuleDataId, FuncId - Function, ClosureId, !PZ) :-
    ProcId = vls_lookup_proc_id(LocnMap, FuncId),
    pz_new_closure_id(ClosureId, !PZ),
    pz_add_closure(ClosureId, pz_closure(ProcId, ModuleDataId), !PZ),
    pz_export_closure(ClosureId, func_get_name(Function), !PZ).

%-----------------------------------------------------------------------%

    % Create proc and struct IDs for functions and any closure environments
    % they require, add these to maps and return them.
    %
:- pred make_proc_and_struct_ids(pair(func_id, function)::in,
    val_locn_map_static::in, val_locn_map_static::out,
    closure_builder::in, closure_builder::out, pz::in, pz::out) is det.

make_proc_and_struct_ids(FuncId - Function, !LocnMap, !BuildModClosure, !PZ) :-
    Name = q_name_to_string(func_get_name(Function)),
    ( if func_builtin_type(Function, BuiltinType) then
        ( BuiltinType = bit_core,
            make_proc_id_core_or_rts(FuncId, Function, !LocnMap,
                !BuildModClosure, !PZ),
            ( if func_get_body(Function, _, _, _, _) then
                true
            else
                unexpected($file, $pred,
                    format("Builtin core function ('%s') has no body",
                        [s(Name)]))
            )
        ; BuiltinType = bit_inline_pz,
            ( if func_builtin_inline_pz(Function, PZInstrs) then
                vls_set_proc_instrs(FuncId, PZInstrs, !LocnMap)
            else
                unexpected($file, $pred, format(
                    "Inline PZ builtin ('%s') without list of instructions",
                    [s(Name)]))
            )
        ; BuiltinType = bit_rts,
            make_proc_id_core_or_rts(FuncId, Function, !LocnMap,
                !BuildModClosure, !PZ),
            ( if
                not func_builtin_inline_pz(Function, _),
                not func_get_body(Function, _, _, _, _)
            then
                true
            else
                unexpected($file, $pred,
                    format("RTS builtin ('%s') with a body",
                        [s(Name)]))
            )
        )
    else
        Imported = func_get_imported(Function),
        make_proc_id_core_or_rts(FuncId, Function, !LocnMap,
            !BuildModClosure, !PZ),
        ( Imported = i_local,
            ( if func_get_body(Function, _, _, _, _) then
                true
            else
                unexpected($file, $pred,
                    format("Local function ('%s') has no body", [s(Name)]))
            )
        ; Imported = i_imported,
            ( if not func_get_body(Function, _, _, _, _) then
                true
            else
                unexpected($file, $pred,
                    format("Imported function ('%s') has a body", [s(Name)]))
            )
        )
    ),
    Captured = func_get_captured_vars_types(Function),
    ( Captured = []
    ; Captured = [_ | _],
        pz_new_struct_id(EnvStructId, "Closure of " ++ Name, !PZ),
        vls_set_closure(FuncId, EnvStructId, !LocnMap),
        EnvStruct = pz_struct([pzw_ptr | map(type_to_pz_width, Captured)]),
        pz_add_struct(EnvStructId, EnvStruct, !PZ)
    ).

:- pred make_proc_id_core_or_rts(func_id::in, function::in,
    val_locn_map_static::in, val_locn_map_static::out,
    closure_builder::in, closure_builder::out, pz::in, pz::out) is det.

make_proc_id_core_or_rts(FuncId, Function, !LocnMap, !BuildModClosure, !PZ) :-
    ( if func_get_body(Function, _, _, _, _) then
        pz_new_proc_id(ProcId, !PZ),
        vls_set_proc(FuncId, ProcId, !LocnMap)
    else
        pz_new_import(ImportId, func_get_name(Function), !PZ),
        closure_add_field(pzv_import(ImportId), FieldNum, !BuildModClosure),
        vls_set_proc_imported(FuncId, ImportId, FieldNum, !LocnMap)
    ).

%-----------------------------------------------------------------------%

bool_width = data.bool_width.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
