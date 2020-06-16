%-----------------------------------------------------------------------%
% Utility code
% vim: ts=4 sw=4 et
%
% Copyright (C) 2015-2020 Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
%-----------------------------------------------------------------------%
:- module util.

:- interface.

:- import_module bag.
:- import_module cord.
:- import_module io.
:- import_module list.
:- import_module maybe.
:- import_module set.

:- import_module context.

%-----------------------------------------------------------------------%

    % Print the error to stderror and set the exit code to 1.
    %
    % Does not terminate the program.
    %
:- pred exit_error(string::in, io::di, io::uo) is det.

    % one_item([X]) = X.
    %
:- func one_item(list(T)) = T.

:- func maybe_list(maybe(X)) = list(X).

:- func maybe_cord(maybe(X)) = cord(X).

    % Mercury does not provide a map over maybe_error.
    %
:- func maybe_error_map(func(A) = B, maybe_error(A, E)) = maybe_error(B, E).

    % set_map_foldl2(Pred, Set0, Set, !Acc1, !Acc2),
    %
:- pred set_map_foldl2(pred(X, Y, A, A, B, B),
    set(X), set(Y), A, A, B, B).
:- mode set_map_foldl2(pred(in, out, in, out, in, out) is det,
    in, out, in, out, in, out) is det.

:- pred map2_corresponding(pred(X, Y, A, B), list(X), list(Y), list(A),
    list(B)).
:- mode map2_corresponding(pred(in, in, out, out) is det, in, in, out, out)
    is det.

:- pred map4_corresponding2(pred(A, B, C, D, X, Y), list(A), list(B),
    list(C), list(D), list(X), list(Y)).
:- mode map4_corresponding2(pred(in, in, in, in, out, out) is det, in, in,
    in, in, out, out) is det.

:- pred foldl4_corresponding(pred(X, Y, A, A, B, B, C, C, D, D),
    list(X), list(Y), A, A, B, B, C, C, D, D).
:- mode foldl4_corresponding(
    pred(in, in, in, out, in, out, in, out, in, out) is det,
    in, in, in, out, in, out, in, out, in, out) is det.

:- pred remove_first_match_map(pred(X, Y), Y, list(X), list(X)).
:- mode remove_first_match_map(pred(in, out) is semidet, out, in, out)
    is semidet.

    % det_uint32_to_int
    %
    % For some reason Mercury 20.01 doesn't provide this (it would be
    % uint32.det_to_int).
    %
:- func det_uint32_to_int(uint32) = int.

:- func det_uint64_to_int(uint64) = int.

%-----------------------------------------------------------------------%

:- func list_join(list(T), list(T)) = list(T).

:- func bag_list_to_bag(list(bag(T))) = bag(T).

%-----------------------------------------------------------------------%

    % file_and_dir(Path, Dir, File).
    %
    % Path = Dir ++ "/" ++ File AND File has no '/'.
    %
:- pred file_and_dir(string, string, string).
:- mode file_and_dir(in, out, out) is det.

:- pred file_change_extension(string, string, string, string).
:- mode file_change_extension(in, in, in, out) is det.

    % filename_extension(Ext, FullName, Base).
    %
    % FullName = Base ++ Ext
    %
:- pred filename_extension(string, string, string).
:- mode filename_extension(in, in, out) is det.

%-----------------------------------------------------------------------%

    % This exception and its routines are temporary, they should be used for
    % code that finds a compilation error, but error handling is not
    % properly setup in that area of the compiler.  This helps by making
    % these errors a little more friendly, and by allowing us to search the
    % source code for these locations when we eventually add error handling.
    %
:- type compile_error_exception
    --->    compile_error_exception(string, string, maybe(context), string).

:- pred compile_error(string::in, string::in, string::in) is erroneous.

:- pred compile_error(string::in, string::in, context::in, string::in)
    is erroneous.

    % This is an alternative to the sorry/1 predicate in the Mercury
    % standard library.  This predicate uses a dedicated exception type and
    % is caught explicitly by plasmac's main/2 predicate.
    %
:- type unimplemented_exception
    --->    unimplemented_exception(string, string, string).

:- pred sorry(string::in, string::in, string::in) is erroneous.

:- func sorry(string, string, string) = T.
:- mode sorry(in, in, in) = (out) is erroneous.

    % Like sorry except that these exceptions are used for things we think
    % are unlikely.  Like trying to roll more than 256 items on the PZ
    % stack.  If they happen to real people then we'll try to address them
    % and can probably do something about them.
    %
:- type design_limitation_exception
    --->    design_limitation_exception(string, string, string).

:- pred limitation(string::in, string::in, string::in) is erroneous.

% TODO: add "unexpected" exception.

:- type tool
    --->    plasmac
    ;       pzasm.

:- type had_errors
    --->    had_errors
    ;       did_not_have_errors.

:- pred run_and_catch(pred(io, io), tool, had_errors, io, io).
:- mode run_and_catch(pred(di, uo) is det, in, out, di, uo) is cc_multi.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%

:- implementation.

:- import_module exception.
:- import_module int.
:- import_module pair.
:- import_module require.
:- import_module string.
:- import_module uint32.
:- import_module uint64.

%-----------------------------------------------------------------------%

exit_error(ErrMsg, !IO) :-
    write_string(stderr_stream, ErrMsg ++ "\n", !IO),
    set_exit_status(1, !IO).

%-----------------------------------------------------------------------%

one_item(Xs) =
    ( if Xs = [X] then
        X
    else
        unexpected($file, $pred, "Expected a list with only one item")
    ).

%-----------------------------------------------------------------------%

maybe_list(yes(X)) = [X].
maybe_list(no) = [].

%-----------------------------------------------------------------------%

maybe_cord(yes(X)) = singleton(X).
maybe_cord(no) = init.

%-----------------------------------------------------------------------%

maybe_error_map(_, error(Error)) = error(Error).
maybe_error_map(Func, ok(X)) = ok(Func(X)).

%-----------------------------------------------------------------------%

set_map_foldl2(Pred, Set0, Set, !Acc1, !Acc2) :-
    List0 = to_sorted_list(Set0),
    list.map_foldl2(Pred, List0, List, !Acc1, !Acc2),
    Set = list_to_set(List).

%-----------------------------------------------------------------------%

map2_corresponding(P, Xs0, Ys0, As, Bs) :-
    ( if
        Xs0 = [],
        Ys0 = []
    then
        As = [],
        Bs = []
    else if
        Xs0 = [X | Xs],
        Ys0 = [Y | Ys]
    then
        P(X, Y, A, B),
        map2_corresponding(P, Xs, Ys, As0, Bs0),
        As = [A | As0],
        Bs = [B | Bs0]
    else
        unexpected($file, $pred, "Mismatched inputs")
    ).

map4_corresponding2(P, As0, Bs0, Cs0, Ds0, Xs, Ys) :-
    ( if
        As0 = [],
        Bs0 = [],
        Cs0 = [],
        Ds0 = []
    then
        Xs = [],
        Ys = []
    else if
        As0 = [A | As],
        Bs0 = [B | Bs],
        Cs0 = [C | Cs],
        Ds0 = [D | Ds]
    then
        P(A, B, C, D, X, Y),
        map4_corresponding2(P, As, Bs, Cs, Ds, Xs0, Ys0),
        Xs = [X | Xs0],
        Ys = [Y | Ys0]
    else
        unexpected($file, $pred, "Mismatched inputs")
    ).

foldl4_corresponding(P, Xs0, Ys0, !A, !B, !C, !D) :-
    ( if
        Xs0 = [],
        Ys0 = []
    then
        true
    else if
        Xs0 = [X | Xs],
        Ys0 = [Y | Ys]
    then
        P(X, Y, !A, !B, !C, !D),
        foldl4_corresponding(P, Xs, Ys, !A, !B, !C, !D)
    else
        unexpected($file, $pred, "Input lists of different lengths")
    ).

%-----------------------------------------------------------------------%

remove_first_match_map(Pred, Y, [X | Xs], Ys) :-
    ( if Pred(X, YP) then
        Y = YP,
        Ys = Xs
    else
        remove_first_match_map(Pred, Y, Xs, Ys0),
        Ys = [X | Ys0]
    ).

%-----------------------------------------------------------------------%

det_uint32_to_int(Uint32) = Int :-
    Int = cast_to_int(Uint32),
    % This should catch cases when this doesn't work.
    ( if from_int(Int, Uint32) then
        true
    else
        unexpected($file, $pred, "Uint32 out of range")
    ).

%-----------------------------------------------------------------------%

det_uint64_to_int(Uint64) = Int :-
    Int = cast_to_int(Uint64),
    ( if from_int(Int, Uint64) then
        true
    else
        unexpected($file, $pred, "Uint64 out of range")
    ).

%-----------------------------------------------------------------------%

list_join(_, []) = [].
list_join(_, [X]) = [X].
list_join(J, [X1, X2 | Xs]) =
    [X1 | J ++ list_join(J, [X2 | Xs])].

%-----------------------------------------------------------------------%

bag_list_to_bag(LoB) =
    foldl(union, LoB, init).

%-----------------------------------------------------------------------%

file_and_dir(Path, Dir, File) :-
    FilePartLength = suffix_length((pred(C::in) is semidet :-
            C \= ('/')
        ), Path),
    % This length is in code units.
    left(Path, length(Path) - FilePartLength - 1, Dir0),
    ( if Dir0 \= "" then
        Dir = Dir0
    else
        Dir = "."
    ),

    right(Path, FilePartLength, File).

file_change_extension(ExtA, ExtB, FileA, FileB) :-
    filename_extension(ExtA, FileA, Base),
    FileB = Base ++ ExtB.

filename_extension(Ext, File, Base) :-
    ( if remove_suffix(File, Ext, Base0) then
        Base = Base0
    else
        Base = File
    ).

%-----------------------------------------------------------------------%

compile_error(File, Pred, Message) :-
    throw(compile_error_exception(File, Pred, no, Message)).

compile_error(File, Pred, Context, Message) :-
    throw(compile_error_exception(File, Pred, yes(Context), Message)).

sorry(File, Pred, Message) :-
    throw(unimplemented_exception(File, Pred, Message)).
sorry(File, Pred, Message) = _ :-
    util.sorry(File, Pred, Message).

limitation(File, Pred, Message) :-
    throw(design_limitation_exception(File, Pred, Message)).

%-----------------------------------------------------------------------%

run_and_catch(Run, Tool, HadErrors, !IO) :-
    ( try [io(!IO)] (
        Run(!IO)
    ) then
        HadErrors = did_not_have_errors
    catch compile_error_exception(File, Pred, MbCtx, Msg) ->
        HadErrors = had_errors,
        Description =
"A compilation error occured and this error is not handled gracefully\n" ++
"by the " ++ tool_name(Tool) ++ ". Sorry.",
        ShortName = tool_short_name(Tool),
        ( MbCtx = yes(Ctx),
            print_exception(Description,
                ["Message"                  - Msg,
                 "Context"                  - context_string(Ctx),
                 (ShortName ++ " location") - Pred,
                 (ShortName ++ " file")     - File],
                !IO)
        ; MbCtx = no,
            print_exception(Description,
                ["Message"                  - Msg,
                 (ShortName ++ " location") - Pred,
                 (ShortName ++ " file")     - File],
                !IO)
        )
    catch unimplemented_exception(File, Pred, Feature) ->
        HadErrors = had_errors,
        print_exception(
"A feature required by your program is currently unimplemented,\n" ++
"however this is something we hope to implement in the future. Sorry\n",
            ["Feature"  - Feature,
             "Location" - Pred,
             "File"     - File],
            !IO)
    catch design_limitation_exception(File, Pred, Message) ->
        HadErrors = had_errors,
        print_exception(
"This program pushes Plasma beyond what it is designed to do. If this\n" ++
"happens on real programs (not a stress test) please contact us and\n" ++
"we'll do what we can to fix it.",
        ["Message"  - Message,
         "Location" - Pred,
         "File"     - File],
        !IO)
    catch software_error(Message) ->
        HadErrors = had_errors,
        print_exception(
"The " ++ tool_name(Tool) ++
    " has crashed due to a bug (an assertion failure or\n" ++
"unhandled state). Please make a bug report. Sorry.",
            ["Message" - Message], !IO)
    ).

:- pred print_exception(string::in, list(pair(string, string))::in,
    io::di, io::uo) is det.

print_exception(Message, Fields, !IO) :-
    write_string(stderr_stream, Message, !IO),
    io.nl(!IO),
    foldl(exit_exception_field, Fields, !IO).

:- pred exit_exception_field(pair(string, string)::in, io::di, io::uo)
    is det.

exit_exception_field(Name - Value, !IO) :-
    write_string(pad_right(Name ++ ": ", ' ', 20), !IO),
    write_string(Value, !IO),
    nl(!IO).

:- func tool_name(tool) = string.

tool_name(plasmac) = "Plasma compiler".
tool_name(pzasm) = "Plasma bytecode assembler".

:- func tool_short_name(tool) = string.

tool_short_name(T) = string(T).

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
