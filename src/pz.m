%-----------------------------------------------------------------------%
% vim: ts=4 sw=4 et
%-----------------------------------------------------------------------%
:- module pz.
%
% Low level plasma data structure.
%
% Copyright (C) 2015-2020 Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
%-----------------------------------------------------------------------%

:- interface.

:- import_module assoc_list.
:- import_module list.
:- import_module map.
:- import_module maybe.
:- import_module uint32.

:- include_module pz.code.
:- include_module pz.pretty.
:- include_module pz.read.
:- include_module pz.write.

:- import_module pz.code.
:- import_module q_name.

%-----------------------------------------------------------------------%
%
% Static data.
%

% TODO: Separate structs into new entries.  Allow arrays of structs.
% TODO: Allow data to reference code.
% TODO: Re-arrange data and value types to better match the on-disk format.

:- type pz_struct
    --->    pz_struct(list(pz_width)).

    % A data type.
    %
    % Note that types aren't defined recursively.  All PZ cares about is the
    % width and padding of data, so we don't need recursive definitions.
    % There is one place where recursive definitions would be useful but the
    % costs outweigh the benefit, and the workaround is simple.
    %
:- type pz_data_type
    --->    type_array(
                pza_width       :: pz_width,
                pza_num_items   :: int
            )
    ;       type_struct(
                pzs_id          :: pzs_id
            ).

    % A static data entry
    %
:- type pz_data
    --->    pz_data(pz_data_type, list(pz_data_value)).

:- type pz_closure
    --->    pz_closure(pzp_id, pzd_id).

%-----------------------------------------------------------------------%
%
% Common definitions
%

%
% PZ isn't typed like a high level language.  The only things PZ needs to
% know are data widths (for alignment and padding).
%

:- type pz_width
    --->    pzw_8
    ;       pzw_16
    ;       pzw_32
    ;       pzw_64
    ;       pzw_fast
    ;       pzw_ptr.

:- type pz_data_value
    --->    pzv_num(int)
    ;       pzv_data(pzd_id)
    ;       pzv_import(pzi_id)
    ;       pzv_closure(pzc_id).

%-----------------------------------------------------------------------%

    % Structure ID
    %
:- type pzs_id.

:- func pzs_id_get_num(pzs_id) = uint32.

:- pred pzs_id_from_num(pz::in, uint32::in, pzs_id::out) is semidet.

    % Imported procedure ID
    %
:- type pzi_id.

:- func pzi_id_get_num(pzi_id) = uint32.

:- pred pzi_id_from_num(pz::in, uint32::in, pzi_id::out) is semidet.

    % Procedure ID
    %
:- type pzp_id.

:- func pzp_id_get_num(pzp_id) = uint32.

:- pred pzp_id_from_num(pz::in, uint32::in, pzp_id::out) is semidet.

    % Data ID
    %
:- type pzd_id.

:- func pzd_id_get_num(pzd_id) = uint32.
:- pred pzd_id_from_num(pz::in, uint32::in, pzd_id::out) is semidet.

    % Closure ID
    %
:- type pzc_id.

:- pred pzc_id_from_num(pz::in, uint32::in, pzc_id::out) is semidet.
:- func pzc_id_get_num(pzc_id) = uint32.

%-----------------------------------------------------------------------%

:- type pz.

%-----------------------------------------------------------------------%

    % init_pz(ModuleName)
    % init_pz(ModuleName, NumStructs, NumImports, NumProcs, NumDatas,
    %   NumClosures).
    %
:- func init_pz(q_name) = pz.
:- func init_pz(q_name, uint32, uint32, uint32, uint32, uint32) = pz.

%-----------------------------------------------------------------------%

:- func pz_get_module_name(pz) = q_name.

%-----------------------------------------------------------------------%

:- pred pz_set_entry_closure(pzc_id::in, pz::in, pz::out) is det.

:- func pz_get_maybe_entry_closure(pz) = maybe(pzc_id).

%-----------------------------------------------------------------------%

:- type pz_named_struct
    --->    pz_named_struct(
                pzs_name        :: string,
                pzs_struct      :: pz_struct
            ).

:- func pz_get_structs(pz) = assoc_list(pzs_id, pz_named_struct).

:- func pz_get_struct_names_map(pz) = map(pzs_id, string).

:- func pz_lookup_struct(pz, pzs_id) = pz_struct.

:- pred pz_new_struct_id(pzs_id::out, string::in, pz::in, pz::out) is det.

:- pred pz_add_struct(pzs_id::in, pz_struct::in, pz::in, pz::out) is det.

%-----------------------------------------------------------------------%

:- func pz_get_imports(pz) = assoc_list(pzi_id, q_name).

:- func pz_lookup_import(pz, pzi_id) = q_name.

:- pred pz_new_import(pzi_id::out, q_name::in, pz::in, pz::out) is det.

:- pred pz_add_import(pzi_id::in, q_name::in, pz::in, pz::out) is det.

%-----------------------------------------------------------------------%

:- pred pz_new_proc_id(pzp_id::out, pz::in, pz::out) is det.

:- pred pz_add_proc(pzp_id::in, pz_proc::in, pz::in, pz::out) is det.

:- func pz_get_procs(pz) = assoc_list(pzp_id, pz_proc).

:- func pz_lookup_proc(pz, pzp_id) = pz_proc.

%-----------------------------------------------------------------------%

:- pred pz_new_data_id(pzd_id::out, pz::in, pz::out) is det.

:- pred pz_add_data(pzd_id::in, pz_data::in, pz::in, pz::out) is det.

:- func pz_lookup_data(pz, pzd_id) = pz_data.

:- func pz_get_data_items(pz) = assoc_list(pzd_id, pz_data).

%-----------------------------------------------------------------------%

:- pred pz_new_closure_id(pzc_id::out, pz::in, pz::out) is det.

:- pred pz_add_closure(pzc_id::in, pz_closure::in, pz::in, pz::out) is det.

:- func pz_get_closures(pz) = assoc_list(pzc_id, pz_closure).

%-----------------------------------------------------------------------%

:- func pz_encode_string(string) = pz_data.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

:- import_module char.
:- import_module int.
:- import_module pair.
:- import_module require.
:- import_module string.

:- include_module pz.bytecode.

%-----------------------------------------------------------------------%

:- pragma foreign_decl("C",
"
#include ""pz_common.h""
#include ""pz_format.h""
").

:- pragma foreign_enum("C", pz_width/0, [
    pzw_8       - "PZW_8",
    pzw_16      - "PZW_16",
    pzw_32      - "PZW_32",
    pzw_64      - "PZW_64",
    pzw_fast    - "PZW_FAST",
    pzw_ptr     - "PZW_PTR"
]).

%-----------------------------------------------------------------------%

:- type pzs_id
    ---> pzs_id(pzs_id_num  :: uint32).

pzs_id_get_num(pzs_id(Num)) = Num.

pzs_id_from_num(PZ, Num, pzs_id(Num)) :-
    Num < PZ ^ pz_next_struct_id ^ pzs_id_num.

%-----------------------------------------------------------------------%

:- type pzi_id
    ---> pzi_id(pzi_id_num  :: uint32).

pzi_id_get_num(pzi_id(Num)) = Num.

pzi_id_from_num(PZ, Num, pzi_id(Num)) :-
    Num < PZ ^ pz_next_import_id ^ pzi_id_num.

%-----------------------------------------------------------------------%

:- type pzp_id
    ---> pzp_id(pzp_id_num :: uint32).

pzp_id_get_num(pzp_id(Num)) = Num.

pzp_id_from_num(PZ, Num, pzp_id(Num)) :-
    Num < PZ ^ pz_next_proc_id ^ pzp_id_num.

%-----------------------------------------------------------------------%

:- type pzd_id
    ---> pzd_id(pzd_id_num  :: uint32).

pzd_id_get_num(pzd_id(Num)) = Num.

pzd_id_from_num(PZ, Num, pzd_id(Num)) :-
    Num < PZ ^ pz_next_data_id ^ pzd_id_num.

%-----------------------------------------------------------------------%

:- type pzc_id
    ---> pzc_id(pzc_id_num  :: uint32).

pzc_id_get_num(pzc_id(Num)) = Num.

pzc_id_from_num(PZ, Num, pzc_id(Num)) :-
    Num < PZ ^ pz_next_closure_id ^ pzc_id_num.

%-----------------------------------------------------------------------%

:- type pz
    ---> pz(
        pz_module_name              :: q_name,

        pz_structs                  :: map(pzs_id, {string, maybe(pz_struct)}),
        pz_next_struct_id           :: pzs_id,

        pz_imports                  :: map(pzi_id, q_name),
        pz_next_import_id           :: pzi_id,

        pz_procs                    :: map(pzp_id, pz_proc),
        pz_next_proc_id             :: pzp_id,

        pz_data                     :: map(pzd_id, pz_data),
        pz_next_data_id             :: pzd_id,

        pz_closures                 :: map(pzc_id, pz_closure),
        pz_next_closure_id          :: pzc_id,
        pz_maybe_entry              :: maybe(pzc_id)
    ).

%-----------------------------------------------------------------------%

init_pz(ModuleName) = pz(ModuleName,
    init, pzs_id(0u32),
    init, pzi_id(0u32),
    init, pzp_id(0u32),
    init, pzd_id(0u32),
    init, pzc_id(0u32),
    no).

init_pz(ModuleName, NumImports, NumStructs, NumDatas, NumProcs, NumClosures) =
    pz( ModuleName,
        init, pzs_id(NumStructs),
        init, pzi_id(NumImports),
        init, pzp_id(NumProcs),
        init, pzd_id(NumDatas),
        init, pzc_id(NumClosures),
        no).

%-----------------------------------------------------------------------%

pz_get_module_name(PZ) = PZ ^ pz_module_name.

%-----------------------------------------------------------------------%

pz_set_entry_closure(ClosureID, !PZ) :-
    !PZ ^ pz_maybe_entry := yes(ClosureID).

pz_get_maybe_entry_closure(PZ) = PZ ^ pz_maybe_entry.

%-----------------------------------------------------------------------%

pz_get_structs(PZ) = Structs :-
    filter_map(pred((K - {N, yes(S)})::in, (K - pz_named_struct(N, S))::out)
            is semidet,
        to_assoc_list(PZ ^ pz_structs), Structs).

pz_get_struct_names_map(PZ) = map_values(func(_, {N, _}) = N,
    PZ ^ pz_structs).

pz_lookup_struct(PZ, PZSId) = Struct :-
    {_, MaybeStruct} = map.lookup(PZ ^ pz_structs, PZSId),
    ( MaybeStruct = no,
        unexpected($file, $pred, "Struct not found")
    ; MaybeStruct = yes(Struct)
    ).

pz_new_struct_id(StructId, Name, !PZ) :-
    StructId = !.PZ ^ pz_next_struct_id,
    !PZ ^ pz_next_struct_id := pzs_id(StructId ^ pzs_id_num + 1u32),
    !PZ ^ pz_structs := det_insert(!.PZ ^ pz_structs, StructId, {Name, no}).

pz_add_struct(StructId, Struct, !PZ) :-
    Structs0 = !.PZ ^ pz_structs,
    ( if search(Structs0, StructId, {N, _}) then
        det_update(StructId, {N, yes(Struct)}, Structs0, Structs)
    else
        det_insert(StructId, {string(StructId), yes(Struct)}, Structs0, Structs)
    ),
    !PZ ^ pz_structs := Structs.

%-----------------------------------------------------------------------%

pz_get_imports(PZ) = to_assoc_list(PZ ^ pz_imports).

pz_lookup_import(PZ, ImportId) = lookup(PZ ^ pz_imports, ImportId).

pz_new_import(ImportId, Name, !PZ) :-
    ImportId = !.PZ ^ pz_next_import_id,
    !PZ ^ pz_next_import_id := pzi_id(ImportId ^ pzi_id_num + 1u32),
    pz_add_import(ImportId, Name, !PZ).

pz_add_import(ImportId, Name, !PZ) :-
    Imports0 = !.PZ ^ pz_imports,
    map.det_insert(ImportId, Name, Imports0, Imports),
    !PZ ^ pz_imports := Imports.

%-----------------------------------------------------------------------%

pz_new_proc_id(ProcId, !PZ) :-
    ProcId = !.PZ ^ pz_next_proc_id,
    !PZ ^ pz_next_proc_id := pzp_id(ProcId ^ pzp_id_num + 1u32).

pz_add_proc(ProcID, Proc, !PZ) :-
    Procs0 = !.PZ ^ pz_procs,
    map.det_insert(ProcID, Proc, Procs0, Procs),
    !PZ ^ pz_procs := Procs.

pz_get_procs(PZ) = to_assoc_list(PZ ^ pz_procs).

pz_lookup_proc(PZ, PID) = map.lookup(PZ ^ pz_procs, PID).

%-----------------------------------------------------------------------%

pz_new_data_id(NewID, !PZ) :-
    NewID = !.PZ ^ pz_next_data_id,
    !PZ ^ pz_next_data_id := pzd_id(NewID ^ pzd_id_num + 1u32).

pz_add_data(DataID, Data, !PZ) :-
    Datas0 = !.PZ ^ pz_data,
    map.det_insert(DataID, Data, Datas0, Datas),
    !PZ ^ pz_data := Datas.

pz_lookup_data(PZ, DataId) = Data :-
    lookup(PZ ^ pz_data, DataId, Data).

pz_get_data_items(PZ) = to_assoc_list(PZ ^ pz_data).

%-----------------------------------------------------------------------%

pz_new_closure_id(NewID, !PZ) :-
    NewID = !.PZ ^ pz_next_closure_id,
    !PZ ^ pz_next_closure_id := pzc_id(NewID ^ pzc_id_num + 1u32).

pz_add_closure(ClosureID, Closure, !PZ) :-
    Closures0 = !.PZ ^ pz_closures,
    map.det_insert(ClosureID, Closure, Closures0, Closures),
    !PZ ^ pz_closures := Closures.

pz_get_closures(PZ) = to_assoc_list(PZ ^ pz_closures).

%-----------------------------------------------------------------------%

pz_encode_string(String) = Data :-
    Values = map(func(C) = pzv_num(to_int(C)),
        to_char_list(String)) ++ [pzv_num(0)],
    Data = pz_data(type_array(pzw_8, length(Values)), Values).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
