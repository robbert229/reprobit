"""Native Windows byte-identity fixture for the MSVC 5.0 SP3 profile.

The example project is committed with a provisional oracle pin; the native CI
job's first run must pass `prepare_reference.py --calibrate` and commit the
recorded digest so this test's cold verify proves byte identity against a real
SP3 build.  The module marker keeps the test portable on other hosts: it skips
cleanly unless REPROBIT_MSVC_5_0_SP3_ROOT points at an authenticated SP3 tree.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

from reprobit.model import Digest
from reprobit.project_loader import load_project_tree
from reprobit.report import CacheMode, Report
from reprobit.schema import OracleDocument

ROOT = Path(__file__).parents[1]
SAMPLE = ROOT / "examples" / "sp3-byte-identity"

pytestmark = [
    pytest.mark.msvc50_sp3,
    pytest.mark.skipif(
        not os.environ.get("REPROBIT_MSVC_5_0_SP3_ROOT"),
        reason="requires an authenticated MSVC 5.0 SP3 installation",
    ),
]


def _rbit() -> Path:
    name = "rbit.exe" if os.name == "nt" else "rbit"
    beside_python = Path(sys.executable).parent / name
    if beside_python.is_file():
        return beside_python
    discovered = shutil.which(name)
    assert discovered is not None, "the installed public rbit entry point is unavailable"
    return Path(discovered).resolve(strict=True)


def _run(
    argv: tuple[os.PathLike[str] | str, ...],
    *,
    cwd: Path,
    environment: dict[str, str],
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        tuple(str(item) for item in argv),
        cwd=cwd,
        env=environment,
        check=False,
        capture_output=True,
        text=True,
        timeout=600,
    )


def _events(completed: subprocess.CompletedProcess[str]) -> list[dict[str, Any]]:
    assert completed.returncode == 0, completed.stdout + completed.stderr
    assert not completed.stderr.strip(), completed.stderr
    events: list[dict[str, Any]] = []
    for line in completed.stdout.splitlines():
        value = json.loads(line)
        assert isinstance(value, dict)
        events.append(value)
    assert events, "the public CLI emitted no progress or completion events"
    return events


def test_sp3_example_provisions_pins_verifies_byte_identical(
    tmp_path: Path,
) -> None:
    configured = os.environ.get("REPROBIT_MSVC_5_0_SP3_ROOT")
    assert configured, "native CI must provision REPROBIT_MSVC_5_0_SP3_ROOT"
    toolchain_root = Path(configured).resolve(strict=True)

    project = tmp_path / "sp3"
    shutil.copytree(
        SAMPLE,
        project,
        ignore=shutil.ignore_patterns(
            "__pycache__",
            ".reprobit-state",
            ".reprobit-transactions",
            "build",
            "reference",
        ),
    )
    environment = os.environ.copy()
    environment["REPROBIT_MSVC_5_0_SP3_ROOT"] = os.fspath(toolchain_root)
    environment["PYTHONUTF8"] = "1"

    prepared = _run(
        (
            sys.executable,
            project / "prepare_reference.py",
            "--toolchain-root",
            toolchain_root,
        ),
        cwd=project,
        environment=environment,
    )
    assert prepared.returncode == 0, prepared.stdout + prepared.stderr
    reference = project / "reference" / "program.exe"
    assert reference.is_file()
    pinned = OracleDocument.model_validate_json(
        (project / "reprobit" / "oracles" / "program.json").read_bytes()
    )
    committed = Digest.from_path(reference)
    assert committed == pinned.image_digest, (
        "reference did not reproduce the committed SP3 oracle pin; the native job "
        "must run prepare_reference.py --calibrate and commit the recorded digest"
    )
    assert reference.stat().st_size == pinned.image_size

    verified = _run(
        (_rbit(), "--format", "ndjson", "verify", project),
        cwd=project,
        environment=environment,
    )
    events = _events(verified)
    completed = [event for event in events if event.get("event") == "verification"]
    assert len(completed) == 1
    assert completed[0]["accepted"] is True
    assert completed[0]["targets"] == completed[0]["exact_targets"] == 1
    assert completed[0]["total_cost"] == 5

    bundle = load_project_tree(project)
    assert bundle.toolchain_lock.profile == "msvc_5_0_sp3"
    report_source = Path(completed[0]["report_json"])
    report = Report.model_validate_json(report_source.read_bytes())
    assert report.verdict.cold is True
    assert report.verdict.byte_exact is True
    assert report.verdict.logic_certified is True
    assert report.verdict.toolchain_origin is True
    assert report.verdict.clean is True
    assert report.cache.mode is CacheMode.BYPASSED
    assert report.cache.hits == report.cache.misses == 0
    assert report.costs.project_total == 5
    target = report.targets[0]
    assert target.byte_exact is True
    assert target.candidate_size == target.oracle_size
    assert target.candidate_digest == committed
    assert target.oracle_digest == committed
