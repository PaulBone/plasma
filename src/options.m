%-----------------------------------------------------------------------%
% Plasma compiler options
% vim: ts=4 sw=4 et
%
% Copyright (C) 2015-2016, 2018, 2020 Plasma Team
% Distributed under the terms of the MIT License see ../LICENSE.code
%
% The options structure for the Plasma compiler.
%
%-----------------------------------------------------------------------%
:- module options.
%-----------------------------------------------------------------------%

:- interface.

%-----------------------------------------------------------------------%

:- type compile_options
    --->    compile_options(
                % High-level options
                co_dir              :: string, % The directory of the input
                                               % file.
                co_input_file       :: string,
                co_output_file      :: string,

                % Diagnostic options.
                co_dump_stages      :: dump_stages,
                co_write_output     :: write_output,

                % Feature/optimisation options
                % Although we're not generally implementing optimisations or
                % these options control some optional transformations during
                % compilation, by making them options they're easier toe
                % test.
                co_do_simplify      :: do_simplify,
                co_enable_tailcalls :: enable_tailcalls
            ).

:- type dump_stages
    --->    dump_stages
    ;       dont_dump_stages.

:- type write_output
    --->    write_output
    ;       dont_write_output.

:- type do_simplify
    --->    do_simplify_pass
    ;       skip_simplify_pass.

:- type enable_tailcalls
    --->    enable_tailcalls
    ;       dont_enable_tailcalls.

%-----------------------------------------------------------------------%
%-----------------------------------------------------------------------%
