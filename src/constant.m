%-----------------------------------------------------------------------%
% Plasma constants
% vim: ts=4 sw=4 et
%
% Copyright (C) Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
% This module provides constants used in the compiler and other tools.
%
%-----------------------------------------------------------------------%
:- module constant.
%-----------------------------------------------------------------------%
:- interface.

:- import_module io.

:- func source_extension = string.
:- func typeres_extension = string.
:- func interface_extension = string.
:- func depends_extension = string.
:- func pz_text_extension = string.
:- func output_extension = string.
:- func library_extension = string.

:- func native_object_extension = string.
:- func native_dylib_extension = string.
:- func cpp_extension = string.
:- func c_header_extension = string.

:- func build_file = string.
:- func build_directory = string.
:- func ninja_rules_file = string.
:- func ninja_vars_file = string.
:- func ninja_build_file = string.
:- func import_whitelist_file_no_directroy = string.

%-----------------------------------------------------------------------%

:- func version_string = string.

    % Print the version message.
    %
:- pred version(string::in, io::di, io::uo) is det.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
:- implementation.

:- import_module list.
:- import_module string.

%-----------------------------------------------------------------------%

source_extension = ".p".
typeres_extension = ".typeres".
interface_extension = ".pi".
depends_extension = ".dep".
pz_text_extension = ".pzt".
output_extension = ".pzo".
library_extension = ".pz".

native_object_extension = ".o".
native_dylib_extension = ".so".
cpp_extension = ".cpp".
c_header_extension = ".h".

build_file = "BUILD.plz".
build_directory = "_build".
ninja_rules_file = "rules.ninja".
ninja_vars_file = "vars.ninja".
ninja_build_file = "build.ninja".
% Ninja requires it uses this name.
import_whitelist_file_no_directroy = "include_whitelist.txt".

%-----------------------------------------------------------------------%

:- pragma foreign_decl("C", include_file("../runtime/pz_config.h")).

:- pragma foreign_proc("C",
    version_string = (Version::out),
    [promise_pure, thread_safe, will_not_call_mercury,
        will_not_throw_exception],
    "
    Version = GC_STRDUP(PLASMA_VERSION_STRING);
    ").

version(Name, !IO) :-
    io.format("%s, %s\n", [s(Name), s(version_string)], !IO),
    io.write_string("https://plasmalang.org\n", !IO),
    io.write_string("Copyright (C) 2015-2025 The Plasma Team\n", !IO),
    io.write_string("Distributed under the MIT License\n", !IO).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
