#!/usr/bin/env python3
"""Build the SP3 byte-identity example's local reference executable.

The committed project oracle carries the byte pin this toolchain must
reproduce.  With no options this script compiles and links the example with
the MSVC 5.0 SP3 toolchain, normalizes the linker timestamps the same way the
project records, and verifies the result against that committed oracle before
touching any published reference.  When the reference bytes have never been
produced or the toolchain changed them, `--calibrate` rebuilds and records the
actual digest into the committed oracle so the project stays self-consistent;
the printed digest is what a maintainer commits.  The CI job must pass without
`--calibrate` on both native Windows and the POSIX/Wine transport; the byte
pin is the same on either host.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from reprobit.classic.pe_metadata import apply_pe_metadata_candidate
from reprobit.model import Digest
from reprobit.schema import OracleDocument
from reprobit.toolchains import (
    MSVC_50_RTM,
    MSVC_50_SP1,
    MSVC_50_SP2,
    MSVC_50_SP3,
    ClassicMSVCToolchain,
)
from reprobit.user_config import resolve_toolchain_root

SAMPLE_ROOT = Path(__file__).resolve().parent
ORACLE_PATH = SAMPLE_ROOT / "reprobit" / "oracles" / "program.json"
PROFILES = {
    MSVC_50_RTM: MSVC_50_RTM,
    MSVC_50_SP1: MSVC_50_SP1,
    MSVC_50_SP2: MSVC_50_SP2,
    MSVC_50_SP3: MSVC_50_SP3,
}


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--profile",
        choices=tuple(PROFILES),
        default=MSVC_50_SP3,
        help="MSVC 5.0 release profile to build (default: msvc_5_0_sp3)",
    )
    parser.add_argument(
        "--toolchain-root",
        type=Path,
        help="compiler installation override (normally remembered by rbit setup)",
    )
    parser.add_argument(
        "--calibrate",
        action="store_true",
        help=(
            "rebuild the reference, record the produced digest into the committed "
            "oracle document, and print the value to commit"
        ),
    )
    return parser


def _compiler_environment(toolchain_root: Path, temporary_root: Path) -> dict[str, str]:
    if os.name == "posix":
        wine = shutil.which("wine")
        wineserver = shutil.which("wineserver")
        if wine is None or wineserver is None:
            raise RuntimeError("Wine and wineserver must both be available on PATH")
        return {
            "HOME": os.fspath(temporary_root / "home"),
            "USER": "reprobit",
            "LOGNAME": "reprobit",
            "TMPDIR": os.fspath(temporary_root / "tmp"),
            "XDG_RUNTIME_DIR": os.fspath(temporary_root / "xdg-runtime"),
            "WINEPREFIX": os.fspath(temporary_root / "wine-prefix"),
            "PATH": os.pathsep.join(
                dict.fromkeys(
                    (
                        os.fspath(Path(wine).resolve(strict=True).parent),
                        "/usr/bin",
                        "/bin",
                        "/usr/sbin",
                        "/sbin",
                    )
                )
            ),
            "LC_ALL": "C",
            "LANG": "C",
            "WINEDEBUG": "-all",
        }
    if os.name == "nt":
        system_root = os.environ.get("SYSTEMROOT")
        if system_root is None:
            raise RuntimeError("native Windows has no SYSTEMROOT environment")
        return {
            "SYSTEMROOT": system_root,
            "TEMP": os.fspath(temporary_root / "tmp"),
            "TMP": os.fspath(temporary_root / "tmp"),
            "PATH": os.pathsep.join(
                (
                    os.fspath(toolchain_root / "bin"),
                    os.fspath(Path(system_root) / "System32"),
                )
            ),
            "INCLUDE": os.pathsep.join(
                (
                    os.fspath(toolchain_root / "include"),
                    os.fspath(toolchain_root / "mfc" / "include"),
                )
            ),
            "LIB": os.pathsep.join(
                (
                    os.fspath(toolchain_root / "lib"),
                    os.fspath(toolchain_root / "mfc" / "lib"),
                )
            ),
        }
    raise RuntimeError("this example supports POSIX/Wine and native Windows")


def _write_failure_log(step: str, **details: object) -> Path:
    log_dir = Path(
        os.environ.get("REPROBIT_NATIVE_LOG_DIR", os.fspath(SAMPLE_ROOT / ".failure-logs"))
    )
    log_dir.mkdir(parents=True, exist_ok=True)
    log = log_dir / f"sp3-{step}-failure.log"
    log.write_text(json.dumps(details, indent=2, default=str))
    return log


def _build_reference(toolchain_root: Path) -> bytes:
    driver = (
        toolchain_root / "wine" / "x86" / "cl"
        if os.name == "posix"
        else toolchain_root / "bin" / "CL.EXE"
    )
    linker = (
        toolchain_root / "wine" / "x86" / "link"
        if os.name == "posix"
        else toolchain_root / "bin" / "LINK.EXE"
    )
    for executable in (driver, linker):
        if not executable.is_file():
            raise RuntimeError(f"MSVC 5.0 SP3 executable is missing: {executable}")
    with tempfile.TemporaryDirectory(prefix="reprobit-sp3-reference-") as raw_temporary:
        temporary_root = Path(raw_temporary)
        for name in (
            "home",
            "tmp",
            "xdg-runtime",
            "wine-prefix",
            "compile",
            "link",
        ):
            (temporary_root / name).mkdir(mode=0o700)
        environment = _compiler_environment(toolchain_root, temporary_root)
        compiled = subprocess.run(
            (
                os.fspath(driver),
                "/nologo",
                "/I.",
                "/Zi",
                "/O2",
                "/Ob1",
                "/Foprogram.obj",
                "/Fdprogram.pdb",
                "/c",
                os.fspath(SAMPLE_ROOT / "program.c"),
            ),
            cwd=temporary_root / "compile",
            env=environment,
            check=False,
            capture_output=True,
            text=True,
            timeout=120,
        )
        if compiled.returncode != 0:
            log = _write_failure_log(
                "compile",
                returncode=compiled.returncode,
                stdout=compiled.stdout,
                stderr=compiled.stderr,
                toolchain=str(toolchain_root),
            )
            raise RuntimeError("MSVC 5.0 SP3 compile failed; diagnostics: " + os.fspath(log))
        (temporary_root / "link" / "program.obj").write_bytes(
            (temporary_root / "compile" / "program.obj").read_bytes()
        )
        linked = subprocess.run(
            (
                os.fspath(linker),
                "/nologo",
                "/nodefaultlib",
                "/entry:transform",
                "/subsystem:console",
                "/out:program.exe",
                "program.obj",
            ),
            cwd=temporary_root / "link",
            env=environment,
            check=False,
            capture_output=True,
            text=True,
            timeout=120,
        )
        if linked.returncode != 0:
            log = _write_failure_log(
                "link",
                returncode=linked.returncode,
                stdout=linked.stdout,
                stderr=linked.stderr,
                linker=str(linker),
                linker_size=linker.stat().st_size,
                toolchain=str(toolchain_root),
                environment_path=environment["PATH"],
            )
            raise RuntimeError("MSVC 5.0 SP3 linker failed; diagnostics: " + os.fspath(log))
        raw = (temporary_root / "link" / "program.exe").read_bytes()
    image, _proof = apply_pe_metadata_candidate(raw, {"link_time": 0, "resource_time": 0})
    return image


def _publish_reference(image: bytes) -> None:
    reference = SAMPLE_ROOT / "reference" / "program.exe"
    reference.parent.mkdir(parents=True, exist_ok=True)
    temporary = reference.with_name(".program.exe.new")
    temporary.write_bytes(image)
    temporary.replace(reference)


def _committed_oracle() -> OracleDocument:
    return OracleDocument.model_validate_json(ORACLE_PATH.read_bytes())


def _write_calibrated_oracle(digest: Digest, size: int) -> None:
    oracle = _committed_oracle()
    updated = oracle.model_copy(update={"image_digest": digest, "image_size": size})
    ORACLE_PATH.write_text(json.dumps(updated.model_dump(mode="json"), separators=(",", ":")))


def _prepare(args: argparse.Namespace) -> None:
    profile = PROFILES[args.profile]
    toolchain_root = resolve_toolchain_root(profile, args.toolchain_root)
    ClassicMSVCToolchain(profile, toolchain_root).doctor().require_ok()
    oracle = _committed_oracle()
    image = _build_reference(toolchain_root)
    digest = Digest.from_bytes(image)
    size = len(image)

    if size == oracle.image_size and digest == oracle.image_digest:
        _publish_reference(image)
        print(f"prepared reference/program.exe ({digest.value})")
        return
    if not args.calibrate:
        raise RuntimeError(
            f"{args.profile} reference digest differs from the committed oracle: "
            f"actual={digest.value} (size {size}), "
            f"oracle={oracle.image_digest.value} (size {oracle.image_size}). "
            "Nothing was published. Re-run with --calibrate to record the "
            "produced bytes, then commit the updated "
            "reprobit/oracles/program.json."
        )
    _write_calibrated_oracle(digest, size)
    _publish_reference(image)
    print(
        "calibrated reprobit/oracles/program.json to "
        f"{digest.value} ({size} bytes); commit this change"
    )


def main(argv: list[str] | None = None) -> int:
    parser = _parser()
    args = parser.parse_args(argv)
    try:
        _prepare(args)
    except (OSError, RuntimeError, subprocess.SubprocessError, ValueError) as exc:
        parser.exit(2, f"prepare_reference.py: error: {exc}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
