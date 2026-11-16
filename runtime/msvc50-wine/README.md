# MSVC 5.0 Wine transport snapshot

The five locked shell transports and their `msvcenv.sh` setup helper are
host-side files. They contain no Microsoft compiler, runtime, header, or
library payload. ReproBit ships their fixed bytes so one authenticated project
toolchain lock can be checked on both POSIX and native Windows hosts; the
native host does not execute them.

The `cl`, `rc`, `link`, `lib`, and `wine-msvc.sh` scripts are byte-identical to
the MSVC 4.2 snapshot: those wrappers are tool-agnostic and only consume the
per-profile environment that `msvcenv.sh` installs. `msvcenv.sh` differs
because the 5.0 tools bind against `MSVCRT.dll` instead of
`MSVCRT40.dll`/`msvcrt20.dll`, so the include/library roots and Wine settings
change as well.

## Wine fidelity finding (issue #4)

Every 5.0 bin tool imports `MSVCRT.dll` at startup; `link.exe` additionally
imports `IMAGEHLP.dll` and `msdis100.dll` (which itself imports `MSVCP50.dll`),
`rc.exe` imports `RCDLL.dll`, and the PDB helper `mspdb50.dll` is CRT-only.
Wine provides builtin `msvcrt.dll` and `imagehlp.dll`; it has no builtins for
`msvcp50`, `rcdll`, `mspdb50`, or `msdis100`, so those resolve to the
provisioned native binaries in `bin/` through `WINEPATH`.

The `msvcenv.sh` comment says Wine's builtin `msvcrt` does not perturb 5.0
output. That is not true of LINK: LINK orders each DLL's import slots with the
C runtime's `qsort`, and Wine's `qsort` orders equal keys differently from
Microsoft's 5.00 runtime, as in the MSVC 4.2 finding (see `docs/wine.md`).
A `WINEDLLOVERRIDES` entry cannot force the native runtime, because Wine's own
`advapi32.dll` depends on `msvcrt.dll`, so the 5.0 profiles declare no Wine
DLL overrides and this transport intentionally sets none. Instead, ReproBit's
classic builds run LINK from a staged copy whose `MSVCRT.dll` import is
renamed to the toolchain's own runtime copied as `MSVCR5.dll`
(`src/reprobit/msvc50_link_runtime.py`). The `link` transport here still runs
the installed `link.exe` on Wine's runtime; it is used only for one-off CMake
graph configuration. `msvcenv.sh` keeps its bytes because they are a
provisioned authority.

The copyright and permissive license notice inherited from the archaic-msvc
developers and Martin Storsjo is preserved in every transported file. The
compiler payload itself is still provisioned only from the repository
revision pinned by ReproBit's corresponding MSVC 5.0 profile.