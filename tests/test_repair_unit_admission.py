"""Unplanned census fallout admits its translation unit exactly as a CMake import would."""

from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from reprobit.model import Digest
from reprobit.producer_graph import ProducerRole
from reprobit.repair_census import RepairCensusEntry
from reprobit.repair_unit_admission import (
    TranslationUnitAdmissionError,
    apply_translation_unit_admissions,
    plan_translation_unit_admissions,
)
from reprobit.schema import BuildPlanDocument, ClassicTranslationUnitPlan
from reprobit.strict_json import canonical_json
from reprobit.translation_unit_identity import translation_unit_id

SOURCE = "src/widget.cpp"
CLEAN = Digest.from_bytes(b"int widget;\n")


def _entry(source: str = SOURCE, symbol: str = "?f@@YAXXZ") -> RepairCensusEntry:
    return RepairCensusEntry(
        source, "build/widget.obj", symbol, "a" * 64, 8, "b" * 64, None, "program", "widget"
    )


def _plan(*units: ClassicTranslationUnitPlan) -> BuildPlanDocument:
    return BuildPlanDocument(
        schema_version=3,
        source_manifest_digest=Digest.from_bytes(b"manifest"),
        translation_units=units,
        source_overlay_digest=Digest.from_bytes(b"overlay"),
        source_overlay_interventions=(),
        archives=(),
        target_gates=(),
    )


def _bundle(
    plan: BuildPlanDocument,
    *,
    overlay_effective: str | None = None,
    producer_graph: Any = None,
) -> Any:
    interventions: tuple[Any, ...] = ()
    if overlay_effective is not None:
        interventions = (
            SimpleNamespace(
                family="source_overlay_graph",
                parameters=(
                    SimpleNamespace(
                        name="outputs",
                        value=[
                            {"path": SOURCE, "clean": CLEAN.value, "effective": overlay_effective}
                        ],
                    ),
                ),
            ),
        )
    return SimpleNamespace(
        build_plan=plan,
        source_manifest=SimpleNamespace(
            entries=(SimpleNamespace(path=SOURCE, digest=CLEAN, size=12),)
        ),
        interventions=interventions,
        producer_graph=producer_graph,
    )


def test_a_planned_unit_follows_the_cmake_import_identity_and_effective_digest() -> None:
    (unit,) = plan_translation_unit_admissions(
        _bundle(_plan()), (_entry(), _entry(symbol="?g@@YAXXZ"))
    )

    identity = Digest.from_bytes(
        canonical_json(
            {"schema": 1, "target": "program", "build_target": "widget", "source": SOURCE}
        )
    ).value
    assert unit.id == f"tu.{identity[:24]}"
    assert unit.target_id == "program"
    assert unit.build_target == "widget"
    assert unit.source == SOURCE
    assert unit.source_digest == CLEAN

    (overlaid,) = plan_translation_unit_admissions(
        _bundle(_plan(), overlay_effective="c" * 64), (_entry(),)
    )
    assert overlaid.source_digest.value == "c" * 64


@pytest.mark.parametrize("debug", (True, False))
def test_a_planned_unit_takes_its_compile_lane_s_debug_format(debug: bool) -> None:
    # The import's identity includes whether the unit compiles with /Zi.
    lane = SimpleNamespace(
        id="compiler.widget.0000",
        role=ProducerRole.COMPILER,
        owner="widget",
        inputs=(f"source/{SOURCE}",),
        arguments=("/nologo", *(("/Zi",) if debug else ()), "/O2", f"${{SOURCE}}/{SOURCE}"),
    )

    (unit,) = plan_translation_unit_admissions(
        _bundle(_plan(), producer_graph=SimpleNamespace(nodes=(lane,))), (_entry(),)
    )

    assert unit.id == translation_unit_id(
        target_id="program", build_target="widget", source=SOURCE, debug_information=debug
    )


def test_planning_refuses_unmanifested_or_already_planned_sources() -> None:
    with pytest.raises(TranslationUnitAdmissionError, match="not in the locked source manifest"):
        plan_translation_unit_admissions(_bundle(_plan()), (_entry(source="src/other.cpp"),))
    (unit,) = plan_translation_unit_admissions(_bundle(_plan()), (_entry(),))
    with pytest.raises(TranslationUnitAdmissionError, match="already planned"):
        plan_translation_unit_admissions(_bundle(_plan(unit)), (_entry(),))
    with pytest.raises(TranslationUnitAdmissionError, match="names no target"):
        plan_translation_unit_admissions(
            _bundle(_plan()),
            (RepairCensusEntry(SOURCE, "build/widget.obj", "?f@@YAXXZ", "a" * 64, 8, "b" * 64),),
        )


def _project(tmp_path: Path, *, shard_subdirectory: bool) -> Any:
    (tmp_path / "reprobit").mkdir()
    (tmp_path / "reprobit" / "build-plan.json").write_bytes(canonical_json(_plan()))
    for directory in ("interventions", "proofs"):
        target = tmp_path / "reprobit" / directory
        (target / "tus" if shard_subdirectory else target).mkdir(parents=True)
        if shard_subdirectory:
            (target / "tus" / "program--tu.existing.json").write_text("{}")
    return SimpleNamespace(
        layout=SimpleNamespace(
            build_plan="reprobit/build-plan.json",
            interventions="reprobit/interventions",
            proofs="reprobit/proofs",
        )
    )


@pytest.mark.parametrize("shard_subdirectory", [False, True])
def test_admission_writes_the_plan_and_empty_shards_in_one_transaction(
    tmp_path: Path, shard_subdirectory: bool
) -> None:
    spec = _project(tmp_path, shard_subdirectory=shard_subdirectory)
    (unit,) = plan_translation_unit_admissions(_bundle(_plan()), (_entry(),))

    changed = apply_translation_unit_admissions(tmp_path, spec, (unit,))

    shard = f"tus/program--{unit.id}.json" if shard_subdirectory else f"{unit.id}.json"
    assert changed == (
        "reprobit/build-plan.json",
        f"reprobit/interventions/{shard}",
        f"reprobit/proofs/{shard}",
    )
    plan = BuildPlanDocument.model_validate_json(
        (tmp_path / "reprobit" / "build-plan.json").read_bytes()
    )
    assert plan.translation_units == (unit,)
    interventions = json.loads((tmp_path / "reprobit" / "interventions" / shard).read_text())
    assert interventions == {
        "build_target": "widget",
        "interventions": [],
        "schema_version": 3,
        "source": SOURCE,
        "source_digest": {"algorithm": "sha256", "value": CLEAN.value},
        "target_id": "program",
        "translation_unit_id": unit.id,
    }
    proofs = json.loads((tmp_path / "reprobit" / "proofs" / shard).read_text())
    assert proofs == {
        "expected_observations": [],
        "schema_version": 3,
        "target_id": "program",
        "translation_unit_id": unit.id,
    }
    with pytest.raises(TranslationUnitAdmissionError, match="already in the build plan"):
        apply_translation_unit_admissions(tmp_path, spec, (unit,))


def test_admission_refuses_to_replace_an_existing_shard(tmp_path: Path) -> None:
    spec = _project(tmp_path, shard_subdirectory=False)
    (unit,) = plan_translation_unit_admissions(_bundle(_plan()), (_entry(),))
    (tmp_path / "reprobit" / "proofs" / f"{unit.id}.json").write_text("{}")

    with pytest.raises(TranslationUnitAdmissionError, match="will not replace"):
        apply_translation_unit_admissions(tmp_path, spec, (unit,))
    assert (
        BuildPlanDocument.model_validate_json(
            (tmp_path / "reprobit" / "build-plan.json").read_bytes()
        ).translation_units
        == ()
    )
