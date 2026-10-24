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

The SP3 byte-identity fixture certifies the same bytes through Wine and
through native Windows: the compiler and linker reproduce the committed oracle
pin with Wine's builtin `msvcrt` and `imagehlp`. This is the opposite of the
MSVC 4.2 finding, where Wine's builtin `msvcrt40`/`msvcrt20` qsort diverged
from Microsoft's and had to be forced native. For 5.0 no `WINEDLLOVERRIDES` is
required -- and one is not even possible: forcing `msvcrt` to "native" breaks
Wine itself because Wine's own `advapi32.dll` depends on `msvcrt.dll`. The 5.0
profiles therefore declare no Wine DLL overrides, and this transport
intentionally sets none.

The copyright and permissive license notice inherited from the archaic-msvc
developers and Martin Storsjo is preserved in every transported file. The
compiler payload itself is still provisioned only from the repository
revision pinned by ReproBit's corresponding MSVC 5.0 profile.