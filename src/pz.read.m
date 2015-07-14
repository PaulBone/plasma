%-----------------------------------------------------------------------%
% vim: ts=4 sw=4 et
%-----------------------------------------------------------------------%
:- module pz.read.
%
% Read the PZ bytecode.
%
% Copyright (C) 2015 Paul Bone
% All rights reserved
%
%-----------------------------------------------------------------------%

:- interface.

:- import_module io.
:- import_module string.

%-----------------------------------------------------------------------%

:- pred read_pz(string::in, pz::out, io::di, io::uo) is det.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

%-----------------------------------------------------------------------%

read_pz(_Name, init_pz, !IO).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%