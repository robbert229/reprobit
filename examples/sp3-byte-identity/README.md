# Literal byte identity on MSVC 5.0 SP3

This small project is the first native-Windows proof for the 5.0 tracer
bullet: ReproBit acquires the pinned MSVC 5.0 SP3 compiler, builds this single
C file from scratch, and certifies that the result is byte-identical to the
normalized reference. The certification uses only the committed source, the
committed producer graph, and the committed oracle pin — no compiler bytes are
ever redistributed.

The reference executable is built by `prepare_reference.py` on the same
machine that verifies, because reference binaries are never committed and the
SP3 compiler does not yet run through the Linux Wine transport.

## Run it

On native Windows, from the ReproBit repository root:

```console
cd examples/sp3-byte-identity
rbit setup .
python prepare_reference.py
rbit verify .
```

`rbit setup` provisions and authenticates the SP3 compiler and remembers the
location, so the other commands need no machine-specific paths. If SP3 is
already set up, skip the first line. On Linux, set up this checkout's pytest
marker skip: the fixture needs `REPROBIT_MSVC_5_0_SP3_ROOT` to point at an
authenticated SP3 installation, which requires the native Windows transport.

The reference build normalizes only candidate-owned linker timestamp fields to
zero (the same `project.metadata` recipe the project commits); the final
`verify` is a separate build from scratch and must not reuse any cached
artifact as certification evidence.

## Rebuilding the reference

`prepare_reference.py` compares the freshly linked normalized image with the
committed oracle in `reprobit/oracles/program.json`. When the compiler
reproduces the recorded bytes, it just publishes `reference/program.exe`. If
the bytes differ — for example on the first run of a freshly added example, or
when a pinned revision changes — it refuses to touch the existing reference
and prints the actual digest. Re-run with `--calibrate` to record the produced
digest into the oracle document, then commit both:

```console
python prepare_reference.py --calibrate
git diff -- reprobit/oracles/program.json
```

The native Windows CI lane runs `prepare_reference.py` without `--calibrate`:
a run that needs calibration fails the lane until the pin is committed, so a
stale pin can never quietly widen the fixture. This is also the cross-run byte
identity check: once committed, every later run must reproduce the same bytes.

<details>
<summary>Advanced: pinned binary provenance</summary>

### What is deliberately small

`program.c` defines one `transform` function that sums the first ten squares.
The committed producer graph compiles it with `/O2 /Ob1` and links a
`/nodefaultlib` console PE with entry point `transform`. The normalized
reference PE's size and SHA-256 are recorded in `reprobit/oracles/program.json`
(the single source of truth the reference script checks against).

### Reference provenance

The compiler comes from
[`archaic-msvc/msvc500sp3`](https://github.com/archaic-msvc/msvc500sp3) at the
revision pinned by `reprobit/toolchain.lock.json`. The reference executable is
built on native Windows by `prepare_reference.py` with that toolchain: compile,
link, then timestamp normalization — nothing else touches the bytes.

</details>
