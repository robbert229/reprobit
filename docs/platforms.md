# Platforms and logical paths

Older compilers can treat the exact spelling of source and include paths as build inputs.
ReproBit therefore reproduces complete compiler-visible paths, not just paths of the same length.
Each run creates a private work area and gives its source, output, and toolchain trees stable DOS
drive letters. Production builds and intervention checks receive the same recorded command line,
working directory, environment, include order, response files, object paths, and PDB paths.

## Source bytes across hosts

The source manifest hashes checked-out bytes, including line endings. Projects that verify on
more than one operating system should declare text normalization in `.gitattributes` and must not
depend on a runner's `core.autocrlf` setting. If a checkout changes admitted bytes, ReproBit treats
it as a different source tree.

## macOS and Linux

Each run uses one private Wine prefix and wineserver for all scheduling lanes. This gives every
compiler process one Windows process namespace and the same fixed compiler-visible `TEMP` and
`TMP` path. Each producer still runs in its own bounded host process group, so a timeout cannot
leave that producer's descendants running. The project locks the host launchers used for the
compiler and resource compiler alongside the toolchain itself. The normal `rbit setup` flow
remembers these launchers; explicit transport options in the [command-line workflow](cli.md) are
advanced one-run overrides. How faithfully Wine reproduces each classic MSVC toolchain's output,
and which DLL overrides the profiles require, is documented in
[Wine fidelity for classic toolchains](wine.md).

## Native Windows

Native builds use a private logon-session drive and Windows Job Objects rather than a controller-
wide drive mapping. `rbit doctor --execute-probe` checks the real descendant path before a build is
trusted. The [native Windows guide](windows.md) is the canonical description of setup, isolation,
toolchain acquisition, and CI evidence.

## What public CI proves

Public CI runs portable tests and package checks on Ubuntu, macOS, and Windows. Its dedicated
`windows-2022` job authenticates the pinned Archaic MSVC 4.2 inputs, exercises the native private-
drive lifecycle, and compiles through the real CL -> C1XX -> C2 chain. Compiler bytes are never
committed, cached, or uploaded.

The MSVC 5.0 SP3 byte-identity fixture gives end-to-end project evidence on both host kinds. A
native Windows lane provisions SP3, authenticates the committed oracle pin, and runs a cold
`rbit verify` to a byte-identical verdict; a POSIX Wine lane provisions the same pinned tree
(including the packaged cross-host transport), and certifies the identical `program.json` pin
through Wine. The two lanes cross-check each other: neither may drift from the committed bytes.

That gate proves the 4.2 host and compiler path, not a project's full byte-identity verdict from
scratch. Project certification still needs the project's locked toolchain, reference data, and a
fixture that builds from scratch on its intended host.
