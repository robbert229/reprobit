"""MSVC 5.0 compiles without debug information (no ``/Zi``).

Such a compile writes no PDB and no CodeView sections.  The build declares
and expects no PDB for it, its translation unit has an identity of its own,
and the producers that read debug data refuse it with the reason.  These
tests cover one unit of each kind and a project that mixes them.
"""

from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace
from typing import Any

import pytest

from reprobit.binary import ByteIdentityError
from reprobit.classic.coff import _comdat_child
from reprobit.classic.frame_objects import frame_locals, object_type_records
from reprobit.classic_orchestration import (
    classic_compiler_translation_unit_authority,
    translation_unit_debug_format_mismatch,
)
from reprobit.classic_project import ClassicProjectError
from reprobit.classic_runtime_graph import _graph_compile_records, classic_compiler_pdb_ref
from reprobit.cli_paths import CLIError
from reprobit.cmake_import import reconciled_debug_format_units
from reprobit.coff_format import CoffObject
from reprobit.model import Digest
from reprobit.producer_graph import (
    CMakeImportRecipe,
    ProducerGraphDocument,
    ProducerNode,
    ProducerRole,
)
from reprobit.schema import (
    BuildPlanDocument,
    ClassicTranslationUnitPlan,
    InterventionDocument,
    LogicalPathProfile,
    ProofDocument,
)
from reprobit.strict_json import canonical_json
from reprobit.translation_unit_identity import translation_unit_id

PATHS = LogicalPathProfile(source=r"R:\source", build=r"R:\build", toolchain=r"R:\toolchain")


def _compiler(index: int, source: str, *, debug: bool, pdb: bool | None = None) -> ProducerNode:
    """One CMake-shaped compiler node; ``pdb`` overrides the declared PDB output."""

    stem = source.removesuffix(".c")
    declares_pdb = debug if pdb is None else pdb
    return ProducerNode(
        id=f"compiler.program.{index:04d}",
        role=ProducerRole.COMPILER,
        owner="program",
        arguments=(
            "/nologo",
            *(("/Zi",) if debug else ()),
            "/O2",
            f"/Fo${{BUILD}}/obj/{stem}.obj",
            f"/Fd${{BUILD}}/obj/{stem}.obj.pdb",
            "-c",
            f"${{SOURCE}}/{source}",
        ),
        inputs=(f"source/{source}",),
        outputs=(
            f"build/obj/{stem}.obj",
            *((f"build/obj/{stem}.obj.pdb",) if declares_pdb else ()),
        ),
    )


def _graph(*compilers: ProducerNode) -> ProducerGraphDocument:
    linker = ProducerNode(
        id="linker.program.9999",
        role=ProducerRole.LINKER,
        owner="program",
        target_id="program",
        arguments=(
            *(f"${{BUILD}}/{node.outputs[0].removeprefix('build/')}" for node in compilers),
            "/out:${BUILD}/program.exe",
        ),
        inputs=tuple(sorted((node.outputs[0] for node in compilers), key=str.casefold)),
        outputs=("build/program.exe",),
        depends_on=tuple(node.id for node in compilers),
    )
    return ProducerGraphDocument(
        schema_version=3,
        toolchain_lock_digest=Digest.from_bytes(b"lock"),
        path_profile_id=PATHS.id,
        extractor="cmake-makefiles-v1",
        import_recipe=CMakeImportRecipe(),
        nodes=(*compilers, linker),
    )


def _mixed_graph() -> ProducerGraphDocument:
    return _graph(_compiler(0, "game.c", debug=True), _compiler(1, "engine.c", debug=False))


def _unit(source: str, *, debug: bool, unit_id: str | None = None) -> ClassicTranslationUnitPlan:
    return ClassicTranslationUnitPlan(
        id=unit_id
        or translation_unit_id(
            target_id="program", build_target="program", source=source, debug_information=debug
        ),
        target_id="program",
        build_target="program",
        source=source,
        source_digest=Digest.from_bytes(source.encode()),
    )


def _plan(*units: ClassicTranslationUnitPlan) -> BuildPlanDocument:
    return BuildPlanDocument(
        schema_version=3,
        source_manifest_digest=Digest.from_bytes(b"source"),
        translation_units=tuple(sorted(units, key=lambda item: item.id)),
        source_overlay_digest=Digest.from_bytes(b"overlay"),
        source_overlay_interventions=(),
        archives=(),
        target_gates=(),
    )


# Identity


def test_a_compile_with_zi_keeps_the_identity_it_always_had() -> None:
    legacy = Digest.from_bytes(
        canonical_json(
            {"schema": 1, "target": "program", "build_target": "program", "source": "a.c"}
        )
    ).value
    assert (
        translation_unit_id(
            target_id="program", build_target="program", source="a.c", debug_information=True
        )
        == f"tu.{legacy[:24]}"
    )


def test_dropping_zi_gives_the_unit_a_new_identity() -> None:
    with_debug, without_debug = (
        translation_unit_id(
            target_id="program", build_target="program", source="a.c", debug_information=debug
        )
        for debug in (True, False)
    )
    assert with_debug != without_debug
    assert without_debug.startswith("tu.") and len(without_debug) == 27


# Producer graph: declared outputs and compile records


def test_a_node_declares_a_pdb_exactly_when_it_compiles_with_zi() -> None:
    assert classic_compiler_pdb_ref(_compiler(0, "a.c", debug=True)) == "build/obj/a.obj.pdb"
    assert classic_compiler_pdb_ref(_compiler(0, "a.c", debug=False)) is None
    with pytest.raises(ClassicProjectError, match="a compile without /Zi writes none"):
        classic_compiler_pdb_ref(_compiler(0, "a.c", debug=False, pdb=True))
    with pytest.raises(ClassicProjectError, match="a compile with /Zi writes one"):
        classic_compiler_pdb_ref(_compiler(0, "a.c", debug=True, pdb=False))


def _records(tmp_path: Path, graph: ProducerGraphDocument) -> dict[str, Any]:
    source_root = tmp_path / "source"
    source_root.mkdir(exist_ok=True)
    for name in ("game.c", "engine.c", "a.c"):
        (source_root / name).write_text("int f(void) { return 0; }\n", encoding="utf-8")
    bundle = SimpleNamespace(spec=SimpleNamespace(paths=PATHS))
    records = _graph_compile_records(
        bundle,  # type: ignore[arg-type]
        graph,
        effective_root=source_root,
        build_root=tmp_path / "build",
        toolchain_root=tmp_path / "toolchain",
        compiler_command=tmp_path / "toolchain" / "CL.EXE",
    )
    return {record.node_id: record for record in records}


def test_a_mixed_project_records_a_pdb_only_for_its_zi_units(tmp_path: Path) -> None:
    records = _records(tmp_path, _mixed_graph())

    game, engine = records["compiler.program.0000"], records["compiler.program.0001"]
    assert game.pdb_path == (tmp_path / "build/obj/game.obj.pdb").resolve(strict=False)
    assert engine.pdb_path is None
    assert engine.object_path == (tmp_path / "build/obj/engine.obj").resolve(strict=False)


@pytest.mark.parametrize(
    ("node", "message"),
    (
        (_compiler(0, "a.c", debug=False, pdb=True), "without /Zi writes none"),
        (_compiler(0, "a.c", debug=True, pdb=False), "with /Zi writes one"),
    ),
)
def test_compile_records_refuse_a_pdb_the_compile_does_not_write(
    tmp_path: Path, node: ProducerNode, message: str
) -> None:
    with pytest.raises(ClassicProjectError, match=message):
        _records(tmp_path, _graph(node))


def test_without_zi_the_inert_pdb_option_still_stays_in_the_build_seat(tmp_path: Path) -> None:
    node = _compiler(0, "a.c", debug=False)
    escaped = node.model_copy(
        update={
            "arguments": tuple(
                "/Fd${SOURCE}/a.pdb" if argument.startswith("/Fd") else argument
                for argument in node.arguments
            )
        }
    )
    with pytest.raises(ClassicProjectError, match="output arguments differ from its outputs"):
        _records(tmp_path, _graph(escaped))


# Translation-unit binding: records made for one debug format


def test_a_mixed_project_binds_each_unit_to_its_lane() -> None:
    bundle = SimpleNamespace(
        build_plan=_plan(_unit("game.c", debug=True), _unit("engine.c", debug=False))
    )

    bound = classic_compiler_translation_unit_authority(bundle, _mixed_graph())  # type: ignore[arg-type]

    assert {node_id: unit.source for node_id, unit in bound.items()} == {
        "compiler.program.0000": "game.c",
        "compiler.program.0001": "engine.c",
    }


def test_a_unit_planned_with_zi_is_refused_once_its_compile_drops_it() -> None:
    bundle = SimpleNamespace(
        build_plan=_plan(_unit("game.c", debug=True), _unit("engine.c", debug=True))
    )

    with pytest.raises(
        ClassicProjectError,
        match=r"engine\.c\) was planned for a compile with /Zi, but its compiler lane "
        r"'compiler\.program\.0001' compiles without /Zi",
    ):
        classic_compiler_translation_unit_authority(bundle, _mixed_graph())  # type: ignore[arg-type]


def test_a_unit_planned_without_zi_is_refused_once_its_compile_adds_it() -> None:
    bundle = SimpleNamespace(
        build_plan=_plan(_unit("game.c", debug=False), _unit("engine.c", debug=False))
    )

    with pytest.raises(ClassicProjectError, match=r"game\.c\) was planned for a compile without"):
        classic_compiler_translation_unit_authority(bundle, _mixed_graph())  # type: ignore[arg-type]


def test_a_zi_unit_keeps_an_id_it_was_given_by_hand() -> None:
    unit = _unit("game.c", debug=True, unit_id="tu.program")

    assert not translation_unit_debug_format_mismatch(unit, _compiler(0, "game.c", debug=True))
    assert translation_unit_debug_format_mismatch(unit, _compiler(0, "game.c", debug=False))


# Re-import: re-key units without records, refuse units with records


def _project(tmp_path: Path, plan: BuildPlanDocument, *, records: frozenset[str]) -> Any:
    root = tmp_path / "project"
    (root / "reprobit/interventions").mkdir(parents=True)
    (root / "reprobit/proofs").mkdir(parents=True)
    (root / "reprobit/build-plan.json").write_bytes(canonical_json(plan))
    for unit in plan.translation_units:
        (root / f"reprobit/interventions/{unit.id}.json").write_bytes(
            canonical_json(
                InterventionDocument(
                    schema_version=3,
                    target_id=unit.target_id,
                    translation_unit_id=unit.id,
                    source=unit.source,
                    source_digest=unit.source_digest,
                    build_target=unit.build_target,
                )
            )
        )
        proof: dict[str, object] = json.loads(
            canonical_json(
                ProofDocument(schema_version=3, target_id="program", translation_unit_id=unit.id)
            )
        )
        if unit.source in records:
            proof["expected_observations"] = [
                {
                    "expected_values": {},
                    "family": "extern_run_pair",
                    "id": f"proof.{unit.source}",
                    "intervention_id": f"donor.{unit.source}",
                    "kind": "expected_observations",
                    "redactions": [],
                }
            ]
        (root / f"reprobit/proofs/{unit.id}.json").write_bytes(
            canonical_json(ProofDocument.model_validate_json(json.dumps(proof)))
        )
    spec = SimpleNamespace(
        layout=SimpleNamespace(
            interventions="reprobit/interventions",
            proofs="reprobit/proofs",
            build_plan="reprobit/build-plan.json",
        )
    )
    return root, SimpleNamespace(spec=spec, build_plan=plan)


def test_a_reimport_rekeys_a_unit_without_records_whose_compile_drops_zi(
    tmp_path: Path,
) -> None:
    game, engine = _unit("game.c", debug=True), _unit("engine.c", debug=True)
    root, bundle = _project(tmp_path, _plan(game, engine), records=frozenset({"game.c"}))

    reconciled = reconciled_debug_format_units(root, bundle, _mixed_graph())

    assert reconciled is not None
    new_id = _unit("engine.c", debug=False).id
    files = {path.as_posix(): data for path, data in reconciled.files.items()}
    assert files[f"reprobit/interventions/{engine.id}.json"] is None
    assert files[f"reprobit/proofs/{engine.id}.json"] is None
    moved = InterventionDocument.model_validate_json(
        files[f"reprobit/interventions/{new_id}.json"] or b""
    )
    assert moved.translation_unit_id == new_id and moved.source == "engine.c"
    proof = ProofDocument.model_validate_json(files[f"reprobit/proofs/{new_id}.json"] or b"")
    assert proof.translation_unit_id == new_id
    plan = BuildPlanDocument.model_validate_json(files["reprobit/build-plan.json"] or b"")
    # The /Zi unit, which holds records, keeps its identity and its shards.
    assert {unit.id for unit in plan.translation_units} == {game.id, new_id}
    assert not any(game.id in path for path in files)


def test_a_reimport_refuses_a_unit_with_records_whose_compile_drops_zi(tmp_path: Path) -> None:
    game, engine = _unit("game.c", debug=True), _unit("engine.c", debug=True)
    root, bundle = _project(tmp_path, _plan(game, engine), records=frozenset({"engine.c"}))

    with pytest.raises(
        CLIError,
        match=rf"change the debug format \(/Zi\) of translation units that hold records.*"
        rf"{engine.id} \(program/engine\.c\)",
    ):
        reconciled_debug_format_units(root, bundle, _mixed_graph())


def test_a_reimport_that_changes_no_debug_format_writes_nothing(tmp_path: Path) -> None:
    game, engine = _unit("game.c", debug=True), _unit("engine.c", debug=False)
    root, bundle = _project(tmp_path, _plan(game, engine), records=frozenset({"engine.c"}))

    assert reconciled_debug_format_units(root, bundle, _mixed_graph()) is None


# Producers that read debug data


def _object_without_debug_information() -> bytes:
    """A COFF object with one ``.text`` COMDAT and its ``.debug$F``, as cl /O2 writes."""

    text = b"\xc3"
    fpo = bytes(16)
    header_size, section_size = 20, 40
    data_offset = header_size + 2 * section_size
    symbols_offset = data_offset + len(text) + len(fpo)
    header = (
        (0x14C).to_bytes(2, "little")
        + (2).to_bytes(2, "little")
        + bytes(4)
        + symbols_offset.to_bytes(4, "little")
        + (4).to_bytes(4, "little")
        + bytes(4)
    )

    def section(name: bytes, size: int, offset: int, characteristics: int) -> bytes:
        return (
            name.ljust(8, b"\0")
            + bytes(8)
            + size.to_bytes(4, "little")
            + offset.to_bytes(4, "little")
            + bytes(12)
            + characteristics.to_bytes(4, "little")
        )

    sections = section(b".text", len(text), data_offset, 0x60301020) + section(
        b".debug$F", len(fpo), data_offset + len(text), 0x42101048
    )

    def symbol(name: bytes, value: int, number: int, kind: int, klass: int, aux: int) -> bytes:
        return (
            name.ljust(8, b"\0")
            + value.to_bytes(4, "little")
            + number.to_bytes(2, "little", signed=True)
            + kind.to_bytes(2, "little")
            + bytes((klass, aux))
        )

    def definition(length: int, number: int, selection: int) -> bytes:
        return (
            length.to_bytes(4, "little")
            + bytes(8)
            + number.to_bytes(2, "little")
            + bytes((selection,))
            + bytes(3)
        )

    symbols = (
        symbol(b".text", 0, 1, 0, 3, 1)
        + definition(len(text), 0, 2)
        + symbol(b".debug$F", 0, 2, 0, 3, 1)
        + definition(len(fpo), 1, 5)
    )
    return header + sections + text + fpo + symbols + (4).to_bytes(4, "little")


def test_a_step_reading_codeview_symbols_names_the_missing_debug_information() -> None:
    coff = CoffObject(_object_without_debug_information())
    primary = next(section for section in coff.sections if section["name"] == ".text")

    assert _comdat_child(coff, primary, ".debug$F")["name"] == ".debug$F"
    with pytest.raises(ByteIdentityError, match=r"no \.debug\$S section at all: its unit compiles"):
        _comdat_child(coff, primary, ".debug$S")


def test_a14_refuses_a_donor_compiled_without_zi() -> None:
    coff = CoffObject(_object_without_debug_information())
    primary = next(section for section in coff.sections if section["name"] == ".text")

    with pytest.raises(
        ByteIdentityError,
        match=r"frame-objects pass \(a14\) reads the donor's locals .* compiles without /Zi",
    ):
        frame_locals(coff, primary, None, base=-8, params_end=8, context="donor")
    records, reason = object_type_records(coff, b"pdb", "donor")
    assert records is None
    assert "no type stream: its unit compiles without /Zi" in reason
