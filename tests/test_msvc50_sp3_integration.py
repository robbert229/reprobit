"""MSVC 5.0 SP3 byte-identity fixture for native Windows and Wine.

The example project is committed with a calibrated oracle pin; the native CI
job and the Wine job each run `prepare_reference.py` (without `--calibrate`) so
this test's cold verify proves byte identity on both host kinds.  The module
marker keeps the test portable on other hosts: it skips cleanly unless
REPROBIT_MSVC_5_0_SP3_ROOT points at an authenticated SP3 tree.
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
from reprobit.producer_graph import toolchain_document_digest
from reprobit.project_loader import load_project_tree
from reprobit.report import CacheMode, Report
from reprobit.schema import OracleDocument, ToolchainLock
from reprobit.translation_unit_identity import translation_unit_id

ROOT = Path(__file__).parents[1]
SAMPLE = ROOT / "examples" / "sp3-byte-identity"
RELEASE_ORACLES = SAMPLE / "release-oracles.json"
RELEASES = (
    ("rtm", "msvc_5_0_rtm", "REPROBIT_MSVC_5_0_RTM_ROOT"),
    ("sp1", "msvc_5_0_sp1", "REPROBIT_MSVC_5_0_SP1_ROOT"),
    ("sp2", "msvc_5_0_sp2", "REPROBIT_MSVC_5_0_SP2_ROOT"),
    ("sp3", "msvc_5_0_sp3", "REPROBIT_MSVC_5_0_SP3_ROOT"),
)

pytestmark = pytest.mark.msvc50


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


@pytest.mark.parametrize("release,profile,root_variable", RELEASES)
def test_release_fixture_provisions_pins_verifies_byte_identical(
    tmp_path: Path,
    release: str,
    profile: str,
    root_variable: str,
) -> None:
    configured = os.environ.get(root_variable)
    if not configured:
        pytest.skip(f"requires authenticated installation in {root_variable}")
    toolchain_root = Path(configured).resolve(strict=True)

    project = tmp_path / release
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
    config = project / "reprobit.toml"
    config.write_text(config.read_text().replace("msvc_5_0_sp3", profile))
    environment = os.environ.copy()
    environment[root_variable] = os.fspath(toolchain_root)
    environment["PYTHONUTF8"] = "1"

    locked = _run(
        (
            _rbit(),
            "toolchain",
            "lock",
            project,
            "--toolchain-root",
            toolchain_root,
            "--runtime-file",
            "wine/x86/cl",
            "--runtime-file",
            "wine/x86/rc",
            "--runtime-file",
            "wine/x86/link",
            "--runtime-file",
            "wine/x86/lib",
            "--runtime-file",
            "wine/x86/wine-msvc.sh",
        ),
        cwd=project,
        environment=environment,
    )
    assert locked.returncode == 0, locked.stdout + locked.stderr
    lock_path = project / "reprobit" / "toolchain.lock.json"
    lock = ToolchainLock.model_validate_json(lock_path.read_bytes())
    graph_path = project / "reprobit" / "producer-graph.json"
    graph = json.loads(graph_path.read_text())
    graph["toolchain_lock_digest"] = toolchain_document_digest(lock).model_dump(mode="json")
    graph_path.write_text(json.dumps(graph, separators=(",", ":")))
    release_oracles = json.loads(RELEASE_ORACLES.read_text())
    assert profile in release_oracles, f"missing committed {profile} reference pin"
    expected = release_oracles[profile]
    oracle_path = project / "reprobit" / "oracles" / "program.json"
    oracle = OracleDocument.model_validate_json(oracle_path.read_bytes())
    oracle = oracle.model_copy(
        update={
            "image_digest": Digest(algorithm="sha256", value=expected["sha256"]),
            "image_size": expected["size"],
        }
    )
    oracle_path.write_text(json.dumps(oracle.model_dump(mode="json"), separators=(",", ":")))

    prepare_argv = [
        sys.executable,
        project / "prepare_reference.py",
        "--toolchain-root",
        toolchain_root,
        "--profile",
        profile,
    ]
    prepared = _run(
        tuple(prepare_argv),
        cwd=project,
        environment=environment,
    )
    assert prepared.returncode == 0, prepared.stdout + prepared.stderr
    reference = project / "reference" / "program.exe"
    assert reference.is_file()
    pinned = OracleDocument.model_validate_json(
        (project / "reprobit" / "oracles" / "program.json").read_bytes()
    )
    if expected is not None:
        assert pinned.image_digest.value == expected["sha256"]
        assert pinned.image_size == expected["size"]
    artifact_path = os.environ.get("REPROBIT_MSVC_5_0_ORACLE_OUTPUT")
    if artifact_path:
        Path(artifact_path).write_text(
            json.dumps(
                {
                    "profile": profile,
                    "sha256": pinned.image_digest.value,
                    "size": pinned.image_size,
                },
                sort_keys=True,
            )
        )
    committed = Digest.from_path(reference)
    assert committed == pinned.image_digest, (
        f"reference did not reproduce the calibrated {profile} oracle pin; the fixture "
        "job must run prepare_reference.py --calibrate and commit the recorded digest"
    )
    assert reference.stat().st_size == pinned.image_size
    first_image = reference.read_bytes()
    repeated = _run(
        (
            sys.executable,
            project / "prepare_reference.py",
            "--toolchain-root",
            toolchain_root,
            "--profile",
            profile,
        ),
        cwd=project,
        environment=environment,
    )
    assert repeated.returncode == 0, repeated.stdout + repeated.stderr
    assert reference.read_bytes() == first_image, f"{profile} reference build is not byte-stable"

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
    assert bundle.toolchain_lock.profile == profile
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


def test_a_unit_compiled_without_debug_information_builds_and_verifies(
    tmp_path: Path,
) -> None:
    """The RTM fixture with its one unit compiled without /Zi.

    The compile writes no PDB, so the graph declares none.  The unit's
    hand-given id was made for a /Zi compile and is refused until the unit
    takes the identity of a compile without debug information; the build
    then verifies byte-identical and clean.  The link keeps no debug
    information, so the reference image is the /Zi fixture's.
    """

    configured = os.environ.get("REPROBIT_MSVC_5_0_RTM_ROOT")
    if not configured:
        pytest.skip("requires authenticated installation in REPROBIT_MSVC_5_0_RTM_ROOT")
    toolchain_root = Path(configured).resolve(strict=True)
    profile = "msvc_5_0_rtm"

    project = tmp_path / "rtm-without-zi"
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
    config = project / "reprobit.toml"
    config.write_text(config.read_text().replace("msvc_5_0_sp3", profile))
    environment = os.environ.copy()
    environment["REPROBIT_MSVC_5_0_RTM_ROOT"] = os.fspath(toolchain_root)
    environment["PYTHONUTF8"] = "1"

    locked = _run(
        (
            _rbit(),
            "toolchain",
            "lock",
            project,
            "--toolchain-root",
            toolchain_root,
            *(
                argument
                for name in ("cl", "rc", "link", "lib", "wine-msvc.sh")
                for argument in ("--runtime-file", f"wine/x86/{name}")
            ),
        ),
        cwd=project,
        environment=environment,
    )
    assert locked.returncode == 0, locked.stdout + locked.stderr
    lock = ToolchainLock.model_validate_json(
        (project / "reprobit" / "toolchain.lock.json").read_bytes()
    )
    graph_path = project / "reprobit" / "producer-graph.json"
    graph = json.loads(graph_path.read_text())
    graph["toolchain_lock_digest"] = toolchain_document_digest(lock).model_dump(mode="json")
    (compiler,) = (node for node in graph["nodes"] if node["role"] == "compiler")
    compiler["arguments"].remove("/Zi")
    compiler["outputs"] = [item for item in compiler["outputs"] if not item.endswith(".pdb")]
    graph_path.write_text(json.dumps(graph, separators=(",", ":")))
    expected = json.loads(RELEASE_ORACLES.read_text())[profile]
    oracle_path = project / "reprobit" / "oracles" / "program.json"
    oracle = OracleDocument.model_validate_json(oracle_path.read_bytes()).model_copy(
        update={
            "image_digest": Digest(algorithm="sha256", value=expected["sha256"]),
            "image_size": expected["size"],
        }
    )
    oracle_path.write_text(json.dumps(oracle.model_dump(mode="json"), separators=(",", ":")))
    prepared = _run(
        (
            sys.executable,
            project / "prepare_reference.py",
            "--toolchain-root",
            toolchain_root,
            "--profile",
            profile,
        ),
        cwd=project,
        environment=environment,
    )
    assert prepared.returncode == 0, prepared.stdout + prepared.stderr

    refused = _run((_rbit(), "build", project), cwd=project, environment=environment)
    assert refused.returncode != 0
    assert "was planned for a compile with /Zi" in refused.stdout + refused.stderr
    assert not (project / "build" / "program.exe").exists()

    unit_id = translation_unit_id(
        target_id="program",
        build_target="sp3-byte-identity",
        source="program.c",
        debug_information=False,
    )
    for relative in (
        "build-plan.json",
        "interventions/tu.program.json",
        "proofs/tu.program.proof.json",
    ):
        path = project / "reprobit" / relative
        path.write_text(path.read_text().replace('"tu.program"', f'"{unit_id}"'))

    built = _run((_rbit(), "build", project), cwd=project, environment=environment)
    assert built.returncode == 0, built.stdout + built.stderr
    assert not list((project / "build").rglob("*.pdb"))

    verified = _run(
        (_rbit(), "--format", "ndjson", "verify", project, "--policy", "clean"),
        cwd=project,
        environment=environment,
    )
    events = _events(verified)
    (completed,) = [event for event in events if event.get("event") == "verification"]
    assert completed["accepted"] is True
    assert completed["targets"] == completed["exact_targets"] == 1
    report = Report.model_validate_json(Path(completed["report_json"]).read_bytes())
    assert report.verdict.byte_exact is True
    assert report.verdict.clean is True
    assert report.targets[0].candidate_digest == Digest(
        algorithm="sha256", value=expected["sha256"]
    )
