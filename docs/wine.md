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
| `MSVCRT.dll` | yes | n/a | builtin for `cl`, `lib`, `rc`; LINK runs on the native copy staged as `MSVCR5.dll` |
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
and `imagehlp.dll`, and both are loaded during a 5.0 build.

**Wine's builtin `msvcrt` does perturb 5.0 LINK output.** LINK 5.0 builds
each DLL's import address table by sorting the loaded import-library members
with the C runtime's `qsort`, keyed on the DLL name alone, so the imports of
one DLL compare equal and keep whatever order that `qsort` leaves. Below the
cutoff of 8 elements Wine's `small_sort` and Microsoft's `shortsort` are the
same selection sort and agree; from there on Microsoft swaps the pivot to the
front and Wine does not, exactly as in the 4.2 finding above. A program that
imports all 21 `d3drm.lib` functions links with two IAT slots exchanged
(`tests/test_msvc50_link_runtime.py`). The SP3 byte-identity fixture did not
show this because its program has no imports.

A `WINEDLLOVERRIDES` entry cannot fix it: forcing `msvcrt=n` on a 5.0 profile
is impossible, because Wine's own `advapi32.dll` depends on `msvcrt.dll`; a
native-only override breaks Wine's boot chain before any tool starts. So the
5.0 profiles still declare **no** `wine_dll_overrides`, and every classic
build instead runs LINK from a staged copy
(`src/reprobit/msvc50_link_runtime.py`):

- `link.exe`, `mspdb50.dll`, `msdis100.dll` and `msvcp50.dll` are copied with
  their one `MSVCRT.dll` import renamed to the same-length `MSVCR5.dll`;
- the toolchain's `msvcrt.dll` is copied beside them as `MSVCR5.dll`.

The loader searches the executable's directory first and Wine has no
`MSVCR5` builtin, so LINK binds Microsoft's 5.00 runtime while Wine keeps its
own. The copies live in the run's private toolchain projection
(`reprobit-native-crt-link/`), never in the installed toolchain. Their bytes
are a pure function of the locked files: each input must equal its reviewed
profile authority and each output its reviewed derived authority
(`MSVC50_NATIVE_CRT_LINK_AUTHORITIES`, recomputed by
`scripts/audit_msvc50_authorities.py`). The evidence audit admits a staged
file only at its staged path, with its derived digest, and only when the lock
admits all five derivation inputs with their reviewed bytes. Cache keys of
link steps bind the staged set's identity.

`cl`, `lib` and `rc` still run on Wine's builtin `msvcrt`; nothing so far
shows their output depending on it. No other imported DLL is a Wine builtin,
so the provisioned native `msvcp50`, `rcdll`, `mspdb50`, and `msdis100` load
from `bin/` unchanged for those tools.

## Where the overrides live

`wine_dll_overrides` is a field on the toolchain profiles in
`src/reprobit/toolchains.py`; the runtime applies it as
`WINEDLLOVERRIDES` for the Wine producer environment. The shipped host-side
transport snapshots (`runtime/msvc42-wine/`, `runtime/msvc50-wine/`) carry the
per-toolchain environment files, and provisioning authenticates them so a
single project lock works on POSIX and native Windows.