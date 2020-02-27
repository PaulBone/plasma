# Plasma Runtime System

Plasma uses a byte code interpreter.  One basic interpreter and runtime
system is currently under development but this could change in the future,
including the addition of native code generation.

## Files

The runtime is mostly C++ with small bits of C, some care needs to be taken
with header files.  C++ may call C (and include its headers) but C may not
call C++ or include its headers (without wrappers).

These files break the rule about having matching implementation/header files
for each module.  Since for these headers, multiple alternative files could
provide different implementations.

* [pz\_interp.h](pz\_interp.h) - The header file for the core of the
                                 interpreter
* [pz\_closure.h](pz\_closure.h) - Header file with closure related
                                   declrations.  The implementation is in
                                   the interpreter files themselves.
* [pz\_generic.cpp](pz\_generic.cpp) - The architecture independent (and only)
                                       implementation of the interpreter
* pz\_generic\_\*.{cpp,h} - Other parts of the generic interpreter.  Only files
                            in this group may include other headers in this
                            group, there must be no coupling with the rest of
                            the system other than trhough pz_interp.h
* [pz\_generic\_run.cpp](pz\_generic\_run.cpp)/[pz\_generic\_run.h](pz\_generic\_run.h) - The main loop of the interpreter.
* [pz\_generic\_builtin.cpp](pz\_generic\_builtin.cpp)/[pz\_generic\_builtin.h](pz\_generic\_builtin.h) - The implementation of the builtins.

Other files that may be interesting are:

* [pz\_main.cpp](pz\_main.cpp) - The entry point for pzrun
* [pz\_option.cpp](pz\_option.cpp) - Option processing for pzrun
* [pz\_instructions.h](pz\_instructions.h) and
  [pz\_instructions.c](pz\_instructions.c)
  Instruction data for the bytecode format
* [pz.h](pz.h)/[pz.cpp](pz.cpp),
  [pz\_code.h](pz\_code.h)/[pz\_code.cpp](pz\_code.cpp) and
  [pz\_data.h](pz\_data.h)/[pz\_data.cpp](pz\_data.cpp) -
  Structures used by pzrun
* [pz\_gc.h](pz\_gc.h) and other pz\_gc\* files - The garbage collector is
  across several files here.
  - [pz\_gc\_util.h](pz\_gc\_util.h) contains an API that allows the GC to
    find roots in C++ code and determine when GC is safe.
  - [pz\_gc\_layout.h](pz\_gc\_layout.h) declares the heap structure.
* [pz\_format.h](pz\_format.h) - Constants for the PZ bytecode format
* [pz\_read.h](pz\_read.h)/[pz\_read.cpp](pz\_read.cpp) -
  Code for reading the PZ bytecode format

## Build Options

 * PZ\_DEV - Enable developer build which makes the PZ\_RUNTIME\_DEV\_OPTS
   below available.

 * DEBUG - Enable runtime assertions.

## Runtime Options

Runtime options are specified using environment variables.  They're each
interpreted as comma-seperated, case-sensative tokens.

 * PZ\_RUNTIME\_OPTS for general runtime options.

   * load\_verbose - verbose loading messages

 * PZ\_RUNTIME\_DEV\_OPTS for developer runtime options.
   
   These require PZ\_DEV to be defined during compile time.

   * interp\_trace - tracing of PZ bytecode interpreter

   * gc\_zealous - Make the GC zealously perform a GC before every
                   allocation.  To test this mode run:
                   ( cd tests; ./run-tests.sh gc )

