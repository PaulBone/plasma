%-----------------------------------------------------------------------%
% Plasma assembler
% vim: ts=4 sw=4 et
%
% Copyright (C) 2015 Paul Bone
% All rights reserved
%
% This program assembles the pz intermediate representation to LLVM
% intermediate representation.
%
%-----------------------------------------------------------------------%
:- module pzllvm.
%-----------------------------------------------------------------------%

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

:- import_module char.
:- import_module list.
:- import_module maybe.
:- import_module string.

:- import_module llvm.
:- import_module pz.

%-----------------------------------------------------------------------%

main(!IO) :-
    io.command_line_arguments(Args, !IO),
    foldl(assemble, Args, !IO).

:- pred assemble(string::in, io::di, io::uo) is det.

assemble(Filename, !IO) :-
    read_pz(Filename, PZ, !IO),
    do_assemble(PZ, LLVM),
    LLVMFilename = remove_suffix_if_present(".pz", Filename) ++ ".ii",
    format("Writing %s\n", [s(LLVMFilename)], !IO),
    write_llvm(LLVMFilename, LLVM, WriteRes, !IO),
    ( WriteRes = ok
    ; WriteRes = error(ErrMsg),
        io.format("%s: %s", [s(LLVMFilename), s(ErrMsg)], !IO),
        io.set_exit_status(1, !IO)
    ).

%-----------------------------------------------------------------------%

:- pred do_assemble(pz::in, llvm::out) is det.

do_assemble(_, llvm).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
