%-----------------------------------------------------------------------%
% vim: ts=4 sw=4 et
%-----------------------------------------------------------------------%
:- module file_utils.
%
% Copyright (C) 2020-2021 Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
% File handling utils specific to Plasma.  These are general for the
% different compiler tools but not general enough to go into the utils
% package.
%
%-----------------------------------------------------------------------%

:- interface.

:- import_module io.
:- import_module string.

:- import_module q_name.

%-----------------------------------------------------------------------%

:- type dir_info.

:- func init = dir_info.

%-----------------------------------------------------------------------%

:- type find_file_result
    --->    yes(string)
    ;       no
    ;       error(
                e_path  :: string,
                e_error :: string
            ).

    % find_module_file(Path, Extension, ModuleName, Result, !DirInfo).
    %
    % Find the interface on the disk.  For now we look in one directory
    % only, later we'll implement include paths.
    %
:- pred find_module_file(string::in, string::in, q_name::in,
    find_file_result::out, dir_info::in, dir_info::out, io::di, io::uo) is det.

%-----------------------------------------------------------------------%

    % Normalises case and strips - _ and .
    %
:- func strip_file_name_punctuation(string) = string.

%-----------------------------------------------------------------------%

    % Return a canonical file name without an extension for the Plasma
    % module name.
    %
:- func canonical_base_name(q_name) = string.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
:- implementation.

:- import_module char.
:- import_module list.
:- import_module map.
:- import_module maybe.
:- import_module require.

:- import_module constant.
:- import_module util.
:- import_module util.exception.
:- import_module util.io.
:- import_module util.path.

%-----------------------------------------------------------------------%

:- type dir_info == map(string, list(string)).

init = map.init.

%-----------------------------------------------------------------------%

find_module_file(Path, Extension, ModuleName, Result, !DirInfo, !IO) :-
    q_name_parts(ModuleName, MaybeModulePart, NQName),
    ( MaybeModulePart = no,
        ModuleQuals = []
    ; MaybeModulePart = yes(ModulePart),
        ModuleQuals = q_name_to_nq_names(ModulePart)
    ),

    ( ModuleQuals = [],
        find_module_file_in_dir(Path, Extension, ModuleName, Result,
            !DirInfo, !IO)
    ; ModuleQuals = [_ | _],
        find_module_file_2(Path, Extension, [], ModuleQuals, NQName, Result,
            !DirInfo, !IO)
    ).

find_module_file_2(BasePath, Extension, PathQuals, OtherQuals, NQName, Result,
        !DirInfo, !IO) :-
    Path = BasePath ++ "/" ++ q_name_to_string(q_name_from_nq_names(PathQuals)),


%        foldl((pred(Path - NameRest::in, DI0::in, DI::out) is det :-
%            ), PathPairs, !DirInfo),

:- pred find_module_file_in_dir(string::in, string::in, q_name::in,
    find_file_result::out, dir_info::in, dir_info::out, io::di, io::uo) is det.

find_module_file_in_dir(Path, Extension, ModuleName, Result, !DirInfo, !IO) :-
    memo_dir_info(Path,
        find_module_file_in_list(Extension, ModuleName),
        Result, !DirInfo, !IO).

:- pred memo_dir_info(string,
    pred(list(string), find_file_result), find_file_result,
    dir_info, dir_info, io, io).
:- mode memo_dir_info(in,
    pred(in, out) is det, out,
    in, out, di, uo) is det.

memo_dir_info(Path, Pred, Result, !DirInfo, !IO) :-
    ( if search(!.DirInfo, Path, DirList) then
        Pred(DirList, Result)
    else
        get_dir_list(Path, MaybeDirList, !IO),
        ( MaybeDirList = ok(DirList),
            det_insert(Path, DirList, !DirInfo),
            Pred(DirList, Result)
        ; MaybeDirList = error(DirError),
            Result = error(Path, DirError)
        )
    ).

:- pred find_module_file_in_list(string::in, q_name::in, list(string)::in,
    find_file_result::out) is det.

find_module_file_in_list(Extension, ModuleName, DirList, Result) :-
    filter(matching_module_file(ModuleName, Extension), DirList, Matches),
    ( Matches = [],
        Result = no
    ; Matches = [FileName],
        Result = yes(FileName)
    ; Matches = [_, _ | _],
        unexpected($file, $pred, "Ambigious files found")
    ).

:- pred matching_module_file(q_name::in, string::in, string::in) is semidet.

matching_module_file(ModuleName, Extension, FileName) :-
    filename_extension(Extension, FileName, FileNameBase),
    strip_file_name_punctuation(q_name_to_string(ModuleName)) =
        strip_file_name_punctuation(FileNameBase).

%-----------------------------------------------------------------------%

strip_file_name_punctuation(Input) =
    strip_file_name_punctuation(skip_char, Input).

:- func strip_file_name_punctuation(pred(char), string) = string.
:- mode strip_file_name_punctuation(pred(in) is semidet, in) = out is det.

strip_file_name_punctuation(IsPunct, Input) = Output :-
    to_char_list(Input, InputList),
    filter_map((pred(C0::in, C::out) is semidet :-
            ( if IsPunct(C0) then
                false % Strip character
            else
                C = to_lower(C0)
            )
        ), InputList, OutputList),
    from_char_list(OutputList, Output).

:- pred skip_char(char::in) is semidet.

skip_char('_').
skip_char('-').
skip_char('.').

%-----------------------------------------------------------------------%

% This should work on all our filesystems, but by defining it in one place
% we could modify it if we needed to.
canonical_base_name(Name) = q_name_to_string(Name).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
