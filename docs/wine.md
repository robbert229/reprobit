# Wine fidelity for classic MSVC toolchains

ReproBit certifies byte-identical output, so the Wine runtime that hosts the
MSVC tools on macOS and Linux must not change the bytes the compiler and
linker emit. This page records what was researched, what differs, and the
profile overrides (if any) each toolchain requires.

## What the tools import

The MSVC binaries load the C runtime at startup, and some load helper DLLs:

| Toolchain | Startup imports beyond the OS API |
| --- | --- |
| MSVC 4.2 | `MSVCRT40.dll`, `msvcrt20.dll`, `mspdb41.dll`, `RCDLL.DLL` (rc) |
| MSVC 5.0 | `MSVCRT.dll`, `mspdb50.dll`, `MSDIS100.DLL` + `IMAGEHLP.dll` (link), `RCDLL.dll` (rc), `MSVCP50.dll` (via `msdis100`) |

## Which Wine builtins exist

Wine provides a builtin reimplementation for a subset of these; for the rest
the provisioned native binaries in the toolchain's `bin/` directory load
through `WINEPATH`.

| DLL | Wine builtin? | 4.2 | 5.0 |
| --- | --- | --- | --- |
| `MSVCRT40.dll` / `msvcrt20.dll` | yes | overridden to native | n/a |
| `MSVCRT.dll` | yes | n/a | used; no override |
| `imagehlp.dll` | yes | n/a | used; no override |
| `msvcp50.dll` | no | n/a | native |
| `rcdll.dll` | no | native | native |
| `mspdb50.dll` / `mspdb41.dll` | no | native | native |
| `msdis100.dll` | no | n/a | native |

## MSVC 4.2 finding

Wine ships a builtin `msvcrt40` whose `qsort` differs from Microsoft's the
moment an array exceeds the insertion-sort cutoff of 8: Wine leaves such a
range in place where Microsoft swaps the pivot value to the low slot. That
single difference reorders LINK's import-thunk arrays and perturbs C2's
register allocator, changing the emitted bytes. The MSVC 4.2 profile therefore
forces the native redistributable CRT (`wine_dll_overrides` =
`msvcrt40=n; msvcrt20=n`), which provisioning drops into `bin/` so Wine finds
it in the application directory.

## MSVC 5.0 finding

Every 5.0 bin tool imports `MSVCRT.dll`. Wine also reimplements `msvcrt.dll`
and `imagehlp.dll`, and both are loaded during a 5.0 build. The SP3
byte-identity fixture certifies that these Wine builtins **do not perturb
5.0 compiler or linker output**: the committed oracle pin
(`79b3416c...dd2a`, 1,024 bytes) reproduces byte-for-byte through Wine, and
the same pin is the native-Windows calibration point. Two CI lanes proved this
(from scratch, cold `rbit verify`) on the same repository, one on
`windows-2022` and one on a POSIX Wine runner.

Consistent with that, the 5.0 profiles declare **no** `wine_dll_overrides`.
There is a second, structural reason this is the only safe choice: forcing
`msvcrt=n` on a 5.0 profile is impossible, because Wine's own `advapi32.dll`
depends on `msvcrt.dll`; a native-only override breaks Wine's boot chain
before any tool starts. No other imported DLL is a Wine builtin, so the
provisioned native `msvcp50`, `rcdll`, `mspdb50`, and `msdis100` load from
`bin/` unchanged.

## Where the overrides live

`wine_dll_overrides` is a field on the toolchain profiles in
`src/reprobit/toolchains.py`; the runtime applies it as
`WINEDLLOVERRIDES` for the Wine producer environment. The shipped host-side
transport snapshots (`runtime/msvc42-wine/`, `runtime/msvc50-wine/`) carry the
per-toolchain environment files, and provisioning authenticates them so a
single project lock works on POSIX and native Windows.