"""Source lock re-pins edited translation units that no saved record depends on."""

from __future__ import annotations

from pathlib import Path

import pytest
from test_cli import _cmake_refresh_project

from reprobit.cli import main
from reprobit.model import Digest
from reprobit.project_loader import load_project, load_project_tree

_PATHS = ("CMakeLists.txt", "project-input.txt", "src/keep.c", "src/remove.c")


def _lock(project: Path) -> list[str]:
    command = ["source", "lock", str(project)]
    for path in _PATHS:
        command += ["--path", path]
    return command


def _records(project: Path) -> dict[Path, bytes]:
    return {path: path.read_bytes() for path in sorted((project / "reprobit").rglob("*.json"))}


def test_lock_repins_an_edited_unit_without_interventions(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    project = tmp_path / "project"
    kept_payload = _cmake_refresh_project(project)
    spec = load_project(project)
    source = project / "src/remove.c"
    source.write_text("int remove(void) { return 3; }\n")

    assert main(_lock(project)) == 0, capsys.readouterr().err

    bundle = load_project_tree(project)
    assert bundle.build_plan is not None
    digest = Digest.from_path(source)
    units = {unit.source: unit for unit in bundle.build_plan.translation_units}
    assert units["src/remove.c"].source_digest == digest
    documents = {item.source: item for item in bundle.intervention_documents if item.source}
    assert documents["src/remove.c"].source_digest == digest
    assert documents["src/remove.c"].interventions == ()
    keep = project / spec.layout.interventions / f"{units['src/keep.c'].id}.json"
    assert keep.read_bytes() == kept_payload


def test_lock_still_refuses_an_edited_unit_with_interventions(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    project = tmp_path / "project"
    _cmake_refresh_project(project)
    (project / "src/keep.c").write_text("int keep(void) { return 4; }\n")
    before = _records(project)
    capsys.readouterr()

    assert main(_lock(project)) == 2
    error = capsys.readouterr().err
    assert "effective translation-unit bytes changed" in error
    assert "src/keep.c" in error
    assert _records(project) == before


def test_lock_refuses_when_any_edited_unit_is_protected(
    tmp_path: Path, capsys: pytest.CaptureFixture[str]
) -> None:
    project = tmp_path / "project"
    _cmake_refresh_project(project)
    (project / "src/keep.c").write_text("int keep(void) { return 4; }\n")
    (project / "src/remove.c").write_text("int remove(void) { return 3; }\n")
    before = _records(project)
    capsys.readouterr()

    assert main(_lock(project)) == 2
    error = capsys.readouterr().err
    assert "src/keep.c" in error
    assert "src/remove.c" not in error
    assert _records(project) == before
