# Literal byte identity on MSVC 5.0 SP3

This small project is the first end-to-end proof for the 5.0 tracer bullet:
ReproBit acquires the pinned MSVC 5.0 SP3 compiler, builds this single C file
from scratch, and certifies that the result is byte-identical to the
normalized reference. The certification uses only the committed source, the
committed producer graph, and the committed oracle pin — no compiler bytes are
ever redistributed. The same committed pin (`79b3416c...dd2a`, 1,024 bytes)
is reproduced byte-for-byte by the native Windows compiler **and** by the
POSIX Wine transport, so one project lock certifies on both host kinds.

The reference executable is built by `prepare_reference.py` on the same
machine that verifies, because reference binaries are never committed. On
native Windows it drives `bin\CL.EXE` and `bin\LINK.EXE` directly; on POSIX it
drives the authenticated `wine/x86/cl` and `wine/x86/link` transport selectors
that provisioning installs.

## Run it

On native Windows or on a POSIX host with Wine, from the ReproBit repository
root:

```console
cd examples/sp3-byte-identity
rbit setup .
python prepare_reference.py
rbit verify .
```

`rbit setup` provisions and authenticates the SP3 compiler (including the
cross-host transport files) and remembers the location, so the other commands
need no machine-specific paths. If SP3 is already set up, skip the first line.

## Wine byte identity

The POSIX backend runs the SP3 tools under Wine. The committed oracle is the
byte-identity cross-check between hosts: both the native Windows CI lane and
the Wine CI lane run `prepare_reference.py` without `--calibrate`, so either
host must reproduce the exact committed pin or its lane fails. The Wine
finding (which built-in DLLs differ and which overrides the profiles require)
is documented in `runtime/msvc50-wine/README.md` and `msvcenv.sh` — the short
version is that Wine's builtin `msvcrt` and `imagehlp` do not perturb 5.0
compiler or linker output, so the 5.0 profiles declare no DLL overrides.

The reference build normalizes only candidate-owned linker timestamp fields to
zero (the same `project.metadata` recipe the project commits); the final
`verify` is a separate build from scratch and must not reuse any cached
artifact as certification evidence.

## Rebuilding the reference

`prepare_reference.py` builds the freshly linked normalized image and compares
it with the committed oracle in `reprobit/oracles/program.json` *before*
publishing anything under `reference/`. When the compiler reproduces the
recorded bytes, it writes `reference/program.exe`. If the bytes differ — as on
the very first run of this example before any host has calibrated the pin — it
leaves `reference/` untouched and prints the actual digest. Re-run with
`--calibrate` to record the produced digest into the oracle document and
publish the reference, then commit both:

```console
python prepare_reference.py --calibrate
git diff -- reprobit/oracles/program.json
```

Both CI lanes (native Windows and Wine) run `prepare_reference.py` without
`--calibrate`: a run that needs calibration fails the lane until the pin is
committed, so a stale pin can never quietly widen the fixture. This is also
the cross-run byte identity check: once committed, every later run on either
host must reproduce the same bytes.

<details>
<summary>Advanced: pinned binary provenance</summary>

### What is deliberately small

`program.c` defines one `transform` function that sums the first ten squares.
The committed producer graph compiles it with `/O2 /Ob1` and links a
`/nodefaultlib` console PE with entry point `transform`. The normalized
reference PE is 1,024 bytes with SHA-256
`79b3416c27aa5ad062800ed09a5efb4534c6080bf5e45b99d21a3bdd207ddd2a`, recorded
in `reprobit/oracles/program.json` (the single source of truth the reference
script checks against).

### Reference provenance

The compiler comes from
[`archaic-msvc/msvc500sp3`](https://github.com/archaic-msvc/msvc500sp3) at the
revision pinned by `reprobit/toolchain.lock.json`. The reference executable is
built by `prepare_reference.py` with that toolchain — compile, link, then
timestamp normalization — and nothing else touches the bytes, on either host.

</details>