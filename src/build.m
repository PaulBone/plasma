%-----------------------------------------------------------------------%
% Plasma builder
% vim: ts=4 sw=4 et
%
% Copyright (C) 2020 Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
% This program starts the build process for Plasma projects
%
%-----------------------------------------------------------------------%
:- module build.
%-----------------------------------------------------------------------%

:- interface.

:- import_module io.

:- import_module q_name.

:- pred build(nq_name::in, io::di, io::uo) is det.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
:- implementation.

:- import_module bool.
:- import_module map.
:- import_module maybe.
:- import_module require.
:- import_module string.
:- import_module list.

:- import_module constant.
:- import_module file_utils.
:- import_module util.
:- import_module util.exception.
:- import_module util.io.
:- import_module util.mercury.
:- import_module util.path.

%-----------------------------------------------------------------------%

build(Name, !IO) :-
    % * Read project
    % * Check project (does module exist?)
    ensure_directory(!IO),
    get_dir_list(MaybeDirList, !IO),
    ( MaybeDirList = ok(DirList)
    ; MaybeDirList = error(Error),
        unexpected($file, $pred, "Error listing dir: " ++ Error)
    ),
    DepInfo = build_dependency_info(Name, DirList),
    write_dependency_file(DepInfo, !IO),
    invoke_ninja(!IO).

%-----------------------------------------------------------------------%

:- type dep_info == list(dep_target).

:- type dep_target
    --->    dt_program(
                dtp_name    :: nq_name,
                dtp_output  :: string,
                dtp_inputs  :: list(string)
            )
    ;       dt_object(
                dto_output  :: string,
                dto_input   :: string
            ).

:- func build_dependency_info(nq_name, list(string)) = dep_info.

build_dependency_info(Module, Filenames) = Deps :-
    MaybeFile = find_module_file(Filenames, source_extension,
        q_name(Module)),
    ( MaybeFile = ok(SourceName),
        filename_extension(source_extension, SourceName, BaseName),
        ObjectName = BaseName ++ output_extension,
        ProgramName = BaseName ++ library_extension,
        Deps = [dt_program(Module, ProgramName, [ObjectName]),
            dt_object(ObjectName, SourceName)]
    ; MaybeFile = error(Error),
        compile_error($file, $pred, string(Error))
    ).

%-----------------------------------------------------------------------%

:- pred write_dependency_file(dep_info::in, io::di, io::uo) is det.

write_dependency_file(DepInfo, !IO) :-
    io.open_output(build_file, BuildFileResult, !IO),
    ( BuildFileResult = ok(BuildFile),
        write_string(BuildFile, "# Auto-generated by plzbuild\n", !IO),
        format(BuildFile, "include %s\n\n", [s(rules_file_no_directory)], !IO),
        foldl(write_target(BuildFile), DepInfo, !IO),
        close_output(BuildFile, !IO)
    ; BuildFileResult = error(Error),
        unexpected($file, $pred,
            format("Cannot write '%s': %s",
                [s(build_file), s(error_message(Error))]))
    ).

:- pred write_target(output_stream::in, dep_target::in, io::di, io::uo) is det.

write_target(File, dt_program(ProgName, ProgFile, Objects), !IO) :-
    format(File, "build %s : plzlink %s\n",
        [s(ProgFile), s(string_join(", ", Objects))], !IO),
    format(File, "    name = %s\n\n", [s(nq_name_to_string(ProgName))], !IO).
write_target(File, dt_object(ObjectFile, SourceFile), !IO) :-
    format(File, "build %s : plzc ../%s\n\n",
        [s(ObjectFile), s(SourceFile)], !IO).

:- pred ensure_rules_file(io::di, io::uo) is det.

ensure_rules_file(!IO) :-
    file_type(yes, rules_file, StatResult, !IO),
    ( StatResult = ok(Stat),
        ( Stat = regular_file
        ;
            ( Stat = directory
            ; Stat = symbolic_link
            ; Stat = named_pipe
            ; Stat = socket
            ; Stat = character_device
            ; Stat = block_device
            ; Stat = message_queue
            ; Stat = semaphore
            ; Stat = shared_memory
            ; Stat = unknown
            ),
            compile_error($file, $pred,
                format("Cannot create rules file, '%s' already exists",
                    [s(rules_file)]))
        )
    ; StatResult = error(_),
        write_rules_file(!IO)
    ).

:- pred write_rules_file(io::di, io::uo) is det.

write_rules_file(!IO) :-
    open_output(rules_file, OpenResult, !IO),
    ( OpenResult = ok(File),
        write_string(File, rules_contents, !IO),
        close_output(File, !IO)
    ; OpenResult = error(Error),
        compile_error($file, $pred,
            format("Canot create '%s': %s",
                [s(rules_file), s(error_message(Error))]))
    ).

:- func rules_contents = string.

rules_contents =
"# Auto-generated by plzbuild

rule plzc
    command = ../../src/plzc $in -o $out
    description = Compiling $in

rule plzlink
    command = ../../src/plzlnk -n $name -o $out $in
    description = Linking $name
".

%-----------------------------------------------------------------------%

:- pred invoke_ninja(io::di, io::uo) is det.

invoke_ninja(!IO) :-
    Command = format("ninja -C %s", [s(build_directory)]),
    call_system(Command, Result, !IO),
    ( Result = ok(Status),
        ( if Status = 0 then
            true
        else
            unexpected($file, $pred,
                format("Sub-command '%s' exited with exit-status %d",
                    [s(Command), i(Status)]))
        )
    ; Result = error(Error),
        unexpected($file, $pred,
            format("Could not execute sub-command '%s': %s",
                [s(Command), s(error_message(Error))]))
    ).

%-----------------------------------------------------------------------%

:- pred ensure_directory(io::di, io::uo) is det.

ensure_directory(!IO) :-
    file_type(yes, build_directory, StatResult, !IO),
    ( StatResult = ok(Stat),
        ( Stat = directory,
            ensure_rules_file(!IO)
        ;
            ( Stat = regular_file
            ; Stat = symbolic_link
            ; Stat = named_pipe
            ; Stat = socket
            ; Stat = character_device
            ; Stat = block_device
            ; Stat = message_queue
            ; Stat = semaphore
            ; Stat = shared_memory
            ; Stat = unknown
            ),
            compile_error($file, $pred,
                format("Cannot create build directory, '%s' already exists",
                    [s(build_directory)]))
        )
    ; StatResult = error(_),
        mkdir(build_directory, Result, Error, !IO),
        ( Result = yes,
            write_rules_file(!IO)
        ; Result = no,
            compile_error($file, $pred,
                format("Cannot create build directory '%s': %s",
                    [s(build_directory), s(Error)]))
        )
    ).

:- pragma foreign_decl("C", local,
"
#include <string.h>
").

:- pred mkdir(string::in, bool::out, string::out, io::di, io::uo) is det.

:- pragma foreign_proc("C",
    mkdir(Name::in, Result::out, Error::out, _IO0::di, _IO::uo),
    [promise_pure, will_not_call_mercury, will_not_throw_exception],
    "
        int ret = mkdir(Name, 0755);
        if (ret == 0) {
            Result = MR_YES;
            // Error really is const
            Error = (char *)"""";
        } else {
            Result = MR_NO;
            char *error_msg = MR_GC_NEW_ARRAY(char, 128);
            ret = strerror_r(errno, error_msg, 128);
            if (ret == 0) {
                Error = error_msg;
            } else {
                Error = (char *)""Buffer too small for error message"";
            }
        }
    ").

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
