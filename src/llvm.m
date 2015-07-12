%-----------------------------------------------------------------------%
% Plasma assembler
% vim: ts=4 sw=4 et
%
% Copyright (C) 2015 Paul Bone
% All rights reserved
%
%
% This program assembles the pz intermediate representation to LLVM
% intermediate representation.
%
%-----------------------------------------------------------------------%
:- module llvm.
%-----------------------------------------------------------------------%

:- interface.

:- import_module io.
:- import_module maybe.
:- import_module string.

%-----------------------------------------------------------------------%

:- type llvm
    ---> llvm.

%-----------------------------------------------------------------------%

:- pred write_llvm(string::in, llvm::in, maybe_error::out, io::di, io::uo)
    is det.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

%-----------------------------------------------------------------------%

write_llvm(Filename, _LLVM, Result, !IO) :-
    io.open_output(Filename, MaybeFile, !IO),
    ( MaybeFile = ok(File),
        io.write_string(File, "/* Output */", !IO),
        io.close_output(File, !IO),
        Result = ok
    ; MaybeFile = error(Error),
        Result = error(error_message(Error))
    ).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
