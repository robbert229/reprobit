from __future__ import annotations

import gc
import weakref
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass, field
from pathlib import Path
from types import SimpleNamespace
from typing import Any, cast

import pytest

import reprobit.discovery_grind as grind
from reprobit.discovery_contracts import (
    DeclarationFamily,
    DeclarationParameter,
    DeclarationState,
    DiscoveryError,
    declaration_state_id,
)
from reprobit.discovery_grind import (
    ColdTrialEvidence,
    ProjectGrindCallbacks,
    run_project_grind,
)
from reprobit.model import Digest


def _state(classes: int, functions: int) -> DeclarationState:
    return DeclarationState(
        family=DeclarationFamily.DECLARATION_SHAPE,
        parameters=(
            DeclarationParameter(name="classes", value=classes),
            DeclarationParameter(name="functions", value=functions),
        ),
    )


def _donor_id(classes: int, functions: int) -> str:
    return f"donor.{classes}.{functions}"


def _state_shape_for_test(state: DeclarationState) -> tuple[int, int]:
    classes = state.parameter("classes")
    functions = state.parameter("functions")
    assert type(classes) is int and type(functions) is int
    return classes, functions


@dataclass
class _Trace:
    seed_calls: list[tuple[Path, str]] = field(default_factory=list)
    donor_calls: list[tuple[Path, tuple[str, ...]]] = field(default_factory=list)
    cold_calls: list[Path] = field(default_factory=list)
    donor_authoring: list[tuple[str, str, str, int, int]] = field(default_factory=list)
    equal_body_authoring: list[tuple[str, str, str, str, int, int]] = field(default_factory=list)
    reference_objects: list[bytes] = field(default_factory=list)
    publication_calls: int = 0


@dataclass
class _ColdReport:
    run_id: Digest
    rejection_reason: str | None


def _context(
    root: Path,
    *,
    label: str,
    plan: object,
    reference: bytes,
    compiler_arguments: tuple[str, ...] = ("/Zi",),
) -> SimpleNamespace:
    root.mkdir(parents=True)
    reference_path = root / "reference.obj"
    reference_path.write_bytes(reference)
    return SimpleNamespace(
        root=root,
        config=SimpleNamespace(plan=plan),
        bundle=SimpleNamespace(
            spec=SimpleNamespace(
                project_id=f"project.{label}",
                state_dir=".reprobit-state",
                toolchain=SimpleNamespace(profile=f"profile.{label}"),
            ),
            interventions=(),
        ),
        unit=SimpleNamespace(
            target_id=f"target.{label}",
            id=f"tu.{label}",
            build_target=f"build.{label}",
        ),
        intervention_document=SimpleNamespace(interventions=()),
        proof_document=object(),
        intervention_path=root / "reprobit/interventions/tu.json",
        proof_path=root / "reprobit/proofs/tu.json",
        compiler_node=SimpleNamespace(id=f"compiler.{label}", arguments=compiler_arguments),
        reference_path=reference_path,
        symbol=f"_{label}_symbol",
    )


def _install_grind_fixture(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    *,
    live_states: tuple[DeclarationState, ...],
    staged_states: tuple[DeclarationState, ...] | None = None,
    existing_donor_ids: tuple[str, ...] = (),
    seat_collisions: dict[str, str] | None = None,
    qualification_rejections: frozenset[tuple[int, int]] = frozenset(),
    cold_reasons: tuple[str | None, ...] = (None,),
    compiler_arguments: tuple[str, ...] = ("/Zi",),
) -> tuple[Path, Path, _Trace, ProjectGrindCallbacks]:
    staged_states = live_states if staged_states is None else staged_states
    live_root = tmp_path / "live"
    staged_root = tmp_path / "sealed"
    live_plan = object()
    staged_plan = object()
    live = _context(
        live_root,
        label="live",
        plan=live_plan,
        reference=b"live reference",
        compiler_arguments=compiler_arguments,
    )
    staged = _context(
        staged_root,
        label="sealed",
        plan=staged_plan,
        reference=b"sealed reference",
        compiler_arguments=compiler_arguments,
    )
    for context in (live, staged):
        existing = tuple(
            SimpleNamespace(id=donor_id, parameters=()) for donor_id in existing_donor_ids
        )
        context.bundle.interventions = existing
        context.intervention_document.interventions = existing
    trace = _Trace()
    cold_results = iter(cold_reasons)

    def resolve(root: Path, *, config_relative: str) -> SimpleNamespace:
        assert config_relative == "reprobit/discovery.json"
        if root == live_root:
            return live
        assert root == staged_root
        return staged

    def enumerate_states(plan: object) -> tuple[DeclarationState, ...]:
        return live_states if plan is live_plan else staged_states

    def capture(context: object) -> SimpleNamespace:
        assert context is live
        return SimpleNamespace(files=(object(),), authority_directories=())

    @contextmanager
    def stage(
        root: Path,
        state_dir: str,
        snapshots: tuple[object, ...],
    ) -> Iterator[Path]:
        assert root == live_root
        assert state_dir == ".reprobit-state"
        assert len(snapshots) == 1
        yield staged_root

    def donor_authoring(
        *,
        target_id: str,
        translation_unit_id: str,
        build_target: str,
        classes: int,
        functions: int,
    ) -> SimpleNamespace:
        trace.donor_authoring.append(
            (
                target_id,
                translation_unit_id,
                build_target,
                classes,
                functions,
            )
        )
        return SimpleNamespace(
            intervention=SimpleNamespace(id=_donor_id(classes, functions), parameters=()),
            receipt=None,
        )

    def equal_body_authoring(
        *,
        target_id: str,
        translation_unit_id: str,
        build_target: str,
        symbol: str,
        classes: int,
        functions: int,
        seed_object: bytes,
        donor_object: bytes,
    ) -> SimpleNamespace:
        assert seed_object == b"sealed seed"
        assert donor_object == f"donor object {classes}.{functions}".encode()
        trace.equal_body_authoring.append(
            (
                target_id,
                translation_unit_id,
                build_target,
                symbol,
                classes,
                functions,
            )
        )
        donor = SimpleNamespace(intervention=SimpleNamespace(id=_donor_id(classes, functions)))
        function = SimpleNamespace(
            intervention=SimpleNamespace(id=f"function.{classes}.{functions}")
        )
        return SimpleNamespace(
            donor=donor,
            function=function,
            candidate_object=f"candidate {classes}.{functions}".encode(),
            records=(donor, function),
        )

    def qualify(
        *,
        reference_object: bytes,
        candidate_object: bytes,
        symbol: str,
    ) -> None:
        trace.reference_objects.append(reference_object)
        assert reference_object == b"sealed reference"
        assert symbol == "_sealed_symbol"
        key = tuple(int(part) for part in candidate_object.decode().split()[1].split("."))
        if key in qualification_rejections:
            raise DiscoveryError("fixture compatibility rejection")

    def seed(root: Path, compiler_id: str) -> bytes:
        trace.seed_calls.append((root, compiler_id))
        return b"sealed seed"

    def donors(
        root: Path,
        donor_ids: tuple[str, ...],
        progress: grind.DonorProgress | None,
    ) -> dict[str, grind.DonorCompileProduct]:
        trace.donor_calls.append((root, donor_ids))
        assert progress is not None
        for index, donor_id in enumerate(donor_ids, start=1):
            progress(index, len(donor_ids), donor_id)
        return {
            donor_id: grind.DonorCompileProduct(
                f"donor object {donor_id.removeprefix('donor.')}".encode(),
                f"donor pdb {donor_id.removeprefix('donor.')}".encode(),
            )
            for donor_id in donor_ids
        }

    def cold(root: Path) -> ColdTrialEvidence:
        trace.cold_calls.append(root)
        reason = next(cold_results)
        report = SimpleNamespace(
            run_id=Digest.from_bytes(f"cold {len(trace.cold_calls)}".encode()),
            rejection_reason=reason,
        )
        return ColdTrialEvidence(accepted=reason is None, report=report)

    def publish(*_args: object, **_kwargs: object) -> str:
        trace.publication_calls += 1
        return "transaction.fixture"

    monkeypatch.setattr(grind, "resolve_project_grind_context", resolve)
    monkeypatch.setattr(grind, "capture_project_grind_inputs", capture)
    monkeypatch.setattr(grind, "enumerate_declaration_states", enumerate_states)
    monkeypatch.setattr(grind, "stage_grind_project", stage)
    monkeypatch.setattr(grind, "build_declaration_shape_donor", donor_authoring)
    monkeypatch.setattr(grind, "build_declaration_shape_equal_body", equal_body_authoring)
    monkeypatch.setattr(grind, "qualify_msvc_reference_object", qualify)

    def merge_records(
        interventions: object,
        proofs: object,
        records: tuple[object, ...],
    ) -> tuple[object, object]:
        merged = {item.id: item for item in interventions.interventions}
        merged.update((record.intervention.id, record.intervention) for record in records)
        return SimpleNamespace(interventions=tuple(merged.values())), proofs

    monkeypatch.setattr(grind, "merge_authored_records", merge_records)
    # A saved donor's seat is its own; a collision names the saved donor whose
    # seat a candidate donor would take.
    collisions = seat_collisions or {}
    monkeypatch.setattr(
        grind,
        "saved_donor_seats",
        lambda document, _proofs: {f"seat.{item.id}": item for item in document.interventions},
    )
    monkeypatch.setattr(
        grind,
        "donor_compiler_seat",
        lambda intervention, _receipt: f"seat.{collisions.get(intervention.id, intervention.id)}",
    )
    monkeypatch.setattr(grind, "_write_staged_documents", lambda *_args: None)
    published_ids = tuple(
        SimpleNamespace(id=identifier)
        for state in staged_states
        for identifier in (
            _donor_id(*_state_shape_for_test(state)),
            f"function.{'.'.join(str(value) for value in _state_shape_for_test(state))}",
        )
    )
    monkeypatch.setattr(
        grind,
        "load_project_tree",
        lambda _root: SimpleNamespace(interventions=published_ids),
    )
    monkeypatch.setattr(
        grind,
        "calculate_cost",
        lambda interventions: SimpleNamespace(
            project_total=sum(1 if item.id.startswith("donor.") else 25 for item in interventions)
        ),
    )
    monkeypatch.setattr(
        grind,
        "_validate_cold_report",
        lambda evidence, **_kwargs: (
            evidence.report.rejection_reason,
            evidence.report.rejection_reason is None,
        ),
    )
    monkeypatch.setattr(grind, "_publish_solution", publish)
    callbacks = ProjectGrindCallbacks(seed, donors, cold)
    return live_root, staged_root, trace, callbacks


def test_grind_uses_the_sealed_context_after_capture(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    live_state = _state(1, 1)
    sealed_state = _state(2, 2)
    second_sealed_state = _state(3, 3)
    live_root, staged_root, trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(live_state,),
        staged_states=(sealed_state, second_sealed_state),
    )

    result = run_project_grind(live_root, callbacks=callbacks)

    assert result.solution is not None
    assert result.solution.state == sealed_state
    assert result.project_id == "project.sealed"
    assert result.target_id == "target.sealed"
    assert result.translation_unit_id == "tu.sealed"
    assert result.symbol == "_sealed_symbol"
    assert trace.seed_calls == [(staged_root, "compiler.sealed")]
    assert trace.donor_calls == [(staged_root, ("donor.2.2", "donor.3.3"))]
    assert trace.cold_calls == [staged_root]
    assert trace.reference_objects == [b"sealed reference", b"sealed reference"]
    assert trace.donor_authoring == [
        ("target.sealed", "tu.sealed", "build.sealed", 2, 2),
        ("target.sealed", "tu.sealed", "build.sealed", 3, 3),
    ]
    assert trace.equal_body_authoring == [
        (
            "target.sealed",
            "tu.sealed",
            "build.sealed",
            "_sealed_symbol",
            2,
            2,
        ),
        (
            "target.sealed",
            "tu.sealed",
            "build.sealed",
            "_sealed_symbol",
            3,
            3,
        ),
    ]


def test_exact_preview_never_calls_publication_without_acceptance(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    live_root, _staged_root, trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1),),
    )

    result = run_project_grind(live_root, callbacks=callbacks, accept_exact=False)

    assert result.exact
    assert not result.published
    assert result.transaction_id is None
    assert trace.publication_calls == 0


@pytest.mark.parametrize(
    ("accept_exact", "accept_progress", "published"),
    (
        (False, False, False),
        (True, False, False),
        (False, True, True),
    ),
)
def test_local_progress_requires_its_explicit_publication_mode(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    accept_exact: bool,
    accept_progress: bool,
    published: bool,
) -> None:
    live_root, _staged_root, trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1),),
    )
    monkeypatch.setattr(
        grind,
        "_validate_cold_report",
        lambda _evidence, **_kwargs: (None, False),
    )

    result = run_project_grind(
        live_root,
        callbacks=callbacks,
        accept_exact=accept_exact,
        accept_progress=accept_progress,
    )

    assert result.locally_qualified
    assert not result.exact
    assert result.published is published
    assert (result.transaction_id is not None) is published
    assert trace.publication_calls == int(published)


def test_progress_acceptance_stops_after_the_cheapest_cold_proven_candidate(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    states = (_state(1, 1), _state(2, 2))
    live_root, _staged_root, trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=states,
    )
    monkeypatch.setattr(
        grind,
        "_validate_cold_report",
        lambda _evidence, **_kwargs: (None, False),
    )

    result = run_project_grind(
        live_root,
        callbacks=callbacks,
        accept_progress=True,
    )

    assert result.published
    assert result.locally_qualified
    assert not result.exact
    assert result.solution is not None
    assert result.solution.state == states[0]
    assert result.cold_trials == 1
    assert len(trace.cold_calls) == 1


def test_grind_rejects_ambiguous_acceptance_modes(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    live_root, _staged_root, _trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1),),
    )

    with pytest.raises(grind.GrindError, match="mutually exclusive"):
        run_project_grind(
            live_root,
            callbacks=callbacks,
            accept_exact=True,
            accept_progress=True,
        )


def test_exact_preview_reuses_and_recertifies_an_identical_existing_donor(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    live_root, staged_root, trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1),),
        existing_donor_ids=("donor.1.1",),
    )

    result = run_project_grind(live_root, callbacks=callbacks)

    assert result.solution is not None
    assert result.solution.reused_donor is True
    assert result.solution.added_interventions == 1
    assert result.solution.added_cost == 25
    assert trace.donor_calls == [(staged_root, ("donor.1.1",))]
    assert trace.cold_calls == [staged_root]


def test_progress_is_monotonic_and_finishes_its_bounded_total(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    states = (_state(1, 1), _state(2, 2), _state(3, 3))
    live_root, _staged_root, _trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=states,
        qualification_rejections=frozenset({(1, 1)}),
        cold_reasons=("cold mismatch", None),
    )
    progress: list[tuple[int, int]] = []

    result = run_project_grind(
        live_root,
        callbacks=callbacks,
        progress=lambda completed, total, *_args: progress.append((completed, total)),
    )

    assert result.exact
    assert result.qualified_candidates == 2
    assert result.cold_trials == 2
    assert len(result.rejections) == 2
    assert {total for _completed, total in progress} == {11}
    assert [completed for completed, _total in progress] == sorted(
        completed for completed, _total in progress
    )
    assert progress[-1] == (11, 11)


def test_early_exact_result_skips_remaining_qualified_states_cleanly(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    live_root, _staged_root, trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1), _state(2, 2)),
    )
    events: list[tuple[int, int, str, str]] = []

    result = run_project_grind(
        live_root,
        callbacks=callbacks,
        progress=lambda completed, total, phase, item, *_args: events.append(
            (completed, total, phase, item)
        ),
    )

    assert result.exact
    assert result.cold_trials == 1
    assert len(trace.cold_calls) == 1
    skipped = [item for _completed, _total, phase, item in events if phase == "grind-skip"]
    assert declaration_state_id(_state(2, 2)) in skipped
    assert events[-1][:2] == (8, 8)


def test_rejected_cold_report_is_released_before_the_next_verifier(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    live_root, staged_root, _trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1), _state(2, 2)),
    )
    report_refs: list[weakref.ReferenceType[_ColdReport]] = []

    def cold(root: Path) -> ColdTrialEvidence:
        assert root == staged_root
        if report_refs:
            gc.collect()
            assert report_refs[-1]() is None
        reason = "cold mismatch" if not report_refs else None
        report = _ColdReport(
            Digest.from_bytes(f"cold {len(report_refs)}".encode()),
            reason,
        )
        report_refs.append(weakref.ref(report))
        return ColdTrialEvidence(accepted=reason is None, report=report)

    result = run_project_grind(
        live_root,
        callbacks=ProjectGrindCallbacks(
            callbacks.probe_seed,
            callbacks.probe_donors,
            cold,
        ),
    )

    assert result.solution is not None
    assert report_refs[0]() is None
    assert report_refs[1]() is result.solution.report


def test_no_solution_never_publishes_even_with_advance_acceptance(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    live_root, _staged_root, trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1), _state(2, 2)),
        qualification_rejections=frozenset({(1, 1)}),
        cold_reasons=("still not byte-identical",),
    )

    result = run_project_grind(live_root, callbacks=callbacks, accept_exact=True)

    assert not result.exact
    assert result.solution is None
    assert not result.published
    assert result.cold_trials == 1
    assert len(result.rejections) == 2
    assert trace.publication_calls == 0


def test_grind_skips_a_state_that_would_share_a_saved_donors_seat(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    live_root, staged_root, trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1), _state(2, 2)),
        existing_donor_ids=("donor.saved",),
        seat_collisions={"donor.1.1": "donor.saved"},
    )

    result = run_project_grind(live_root, callbacks=callbacks)

    assert result.solution is not None
    assert result.solution.state == _state(2, 2)
    assert trace.donor_calls == [(staged_root, ("donor.2.2",))]
    assert [(item.state_id, item.stage) for item in result.rejections] == [
        (declaration_state_id(_state(1, 1)), "qualification")
    ]
    assert "saved donor 'donor.saved'" in result.rejections[0].reason
    assert "one seat holds one donor" in result.rejections[0].reason


def test_grind_finishes_when_every_state_shares_a_saved_donors_seat(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    live_root, _staged_root, trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1),),
        existing_donor_ids=("donor.saved",),
        seat_collisions={"donor.1.1": "donor.saved"},
    )

    result = run_project_grind(live_root, callbacks=callbacks, accept_progress=True)

    assert result.solution is None
    assert not result.published
    assert trace.donor_calls == []
    assert trace.cold_calls == []
    assert len(result.rejections) == 1


def _extern_run_state(count: int) -> DeclarationState:
    return DeclarationState(
        family=DeclarationFamily.EXTERN_RUN_PAIR,
        parameters=(
            DeclarationParameter(name="header_count", value=count),
            DeclarationParameter(name="header_prefix", value="ReproBitPad"),
            DeclarationParameter(name="seat_count", value=0),
            DeclarationParameter(name="seat_prefix", value="ReproBitPadSeat"),
            DeclarationParameter(name="width", value=3),
        ),
    )


def _extern_run_context(placement: str, *saved: object) -> SimpleNamespace:
    from reprobit.discovery_authoring import merge_authored_records
    from reprobit.schema import InterventionDocument, ProofDocument

    interventions = InterventionDocument(
        schema_version=3,
        target_id="program",
        translation_unit_id="tu.unit",
        build_target="program",
        interventions=(),
    )
    proofs = ProofDocument(
        schema_version=3,
        target_id="program",
        translation_unit_id="tu.unit",
        expected_observations=(),
    )
    if saved:
        interventions, proofs = merge_authored_records(interventions, proofs, saved)
    return SimpleNamespace(
        unit=SimpleNamespace(target_id="program", id="tu.unit", build_target="program"),
        config=SimpleNamespace(extern_runs=SimpleNamespace(placement=placement)),
        intervention_document=interventions,
        proof_document=proofs,
        symbol="_second",
    )


def _saved_extern_run(count: int, placement: str) -> object:
    from reprobit.discovery_authoring import build_extern_run_donor

    return build_extern_run_donor(
        target_id="program",
        translation_unit_id="tu.unit",
        build_target="program",
        header_prefix="ReproBitPad",
        header_count=count,
        seat_prefix="ReproBitPadSeat",
        seat_count=0,
        width=3,
        beneficiary_symbols=("_first",),
        header_placement=placement,
    )


def test_an_extern_run_in_another_placement_than_a_saved_donor_is_skipped() -> None:
    saved = _saved_extern_run(10, "prefix")
    context = _extern_run_context("after_includes", saved)
    states = (_extern_run_state(9), _extern_run_state(10), _extern_run_state(11))

    admitted, skipped = grind._admit_against_saved_seats(states, context)

    assert [state for state, _record in admitted] == [states[0], states[2]]
    assert [item.state_id for item in skipped] == [declaration_state_id(states[1])]
    reason = skipped[0].reason
    assert saved.intervention.id in reason
    assert "header_placement is 'prefix' there and '(default)' here" in reason


def test_an_extern_run_a_saved_donor_already_is_reuses_it() -> None:
    saved = _saved_extern_run(10, "prefix")
    context = _extern_run_context("prefix", saved)

    admitted, skipped = grind._admit_against_saved_seats((_extern_run_state(10),), context)

    assert skipped == []
    assert [record.intervention.id for _state, record in admitted] == [saved.intervention.id]


# --- a function no declaration state moves ---------------------------------------------


def _coff_with_body(body: bytes) -> bytes:
    from test_classic_register_bijection_reencoding_full import codeview_stream, make_coff

    return make_coff(
        body=body,
        relocations=(6, len(body) - 9),
        lines=((4, 11),),
        debug_stream=codeview_stream(len(body), 4, len(body) - 5),
    )


SEED_BODY = bytes.fromhex("535657558b1d000000008b43048b0d000000005d5f5e5bc3")
MOVED_BODY = bytes.fromhex("535657558b1d000000008b4b048b0d000000005d5f5e5bc3")


def test_seed_body_states_name_the_states_that_compile_the_seeds_body() -> None:
    from test_classic_register_bijection_reencoding_full import TARGET_SYMBOL

    seed = _coff_with_body(SEED_BODY)
    states = (_state(1, 1), _state(2, 2))
    same, sensitive = grind.seed_body_states(
        tuple((state, seed) for state in states), seed, TARGET_SYMBOL
    )
    assert same == {declaration_state_id(state) for state in states} and not sensitive
    moved = _coff_with_body(MOVED_BODY)
    same, sensitive = grind.seed_body_states(
        ((states[0], seed), (states[1], moved)), seed, TARGET_SYMBOL
    )
    assert same == {declaration_state_id(states[0])} and sensitive
    # A body that cannot be read is never the seed's.
    same, sensitive = grind.seed_body_states(((states[0], b"junk"),), seed, TARGET_SYMBOL)
    assert same == frozenset() and sensitive


def test_the_seed_body_rewriting_takes_a_saved_donor_before_a_new_one() -> None:
    states = (("state.a", "donor.a"), ("state.b", "donor.b"), ("state.c", "donor.c"))
    every = frozenset({"state.a", "state.b", "state.c"})
    assert grind.seed_body_choice(states, every, frozenset()) == "state.a"
    assert grind.seed_body_choice(states, every, frozenset({"donor.b"})) == "state.b"
    assert grind.seed_body_choice(states, frozenset(), frozenset()) is None


def test_a_seed_body_donor_goes_straight_to_the_rewriting(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    calls: list[str] = []

    def splice(*_args: object, **_kwargs: object) -> object:
        calls.append("equal body")
        raise grind.DiscoveryAuthoringError("seed and donor function bodies are identical")

    def rewrite(*_args: object, **_kwargs: object) -> object:
        calls.append("rewriting")
        return SimpleNamespace(candidate_object=b"candidate")

    monkeypatch.setattr(grind, "_state_equal_body", splice)
    monkeypatch.setattr(grind, "_state_rewriting", rewrite)
    monkeypatch.setattr(grind, "qualify_msvc_reference_object", lambda **_kwargs: None)
    context = SimpleNamespace(symbol="_f")
    kwargs = {"seed_object": b"s", "donor_object": b"d", "reference_object": b"r"}
    grind.qualify_state(_state(1, 1), context, seed_body=True, **kwargs)
    assert calls == ["rewriting"]
    calls.clear()
    grind.qualify_state(_state(1, 1), context, **kwargs)
    assert calls == ["equal body", "rewriting"]

    def refuse(*_args: object, **_kwargs: object) -> object:
        raise grind.DiscoveryAuthoringError("no region replacement reaches the reference")

    monkeypatch.setattr(grind, "_state_rewriting", refuse)
    with pytest.raises(grind.DiscoveryAuthoringError) as refused:
        grind.qualify_state(_state(1, 1), context, **kwargs)
    # Both reasons are reported, not only the splice's.
    assert "bodies are identical; rewriting: no region replacement" in str(refused.value)


def test_grind_authors_a_seed_body_rewriting_once(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    states = (_state(1, 1), _state(2, 2), _state(3, 3))
    live_root, _staged_root, trace, callbacks = _install_grind_fixture(
        monkeypatch, tmp_path, live_states=states
    )
    monkeypatch.setattr(
        grind,
        "seed_body_states",
        lambda donors, _seed, _symbol: (
            frozenset(declaration_state_id(state) for state, _object in donors),
            False,
        ),
    )
    rewritten: list[DeclarationState] = []

    def rewrite(state: DeclarationState, _context: object, **_kwargs: object) -> object:
        rewritten.append(state)
        classes, functions = _state_shape_for_test(state)
        donor = SimpleNamespace(intervention=SimpleNamespace(id=_donor_id(classes, functions)))
        function = SimpleNamespace(
            intervention=SimpleNamespace(id=f"function.{classes}.{functions}")
        )
        return SimpleNamespace(
            donor=donor,
            function=function,
            candidate_object=f"candidate {classes}.{functions}".encode(),
            records=(donor, function),
        )

    monkeypatch.setattr(grind, "_state_rewriting", rewrite)

    result = run_project_grind(live_root, callbacks=callbacks, accept_exact=True)

    assert rewritten == [states[0]]
    assert trace.equal_body_authoring == []
    assert result.solution is not None and result.solution.state == states[0]
    assert [rejection.reason for rejection in result.rejections] == [
        "every state compiles the seed's body; its rewriting is authored once, with "
        + declaration_state_id(states[0])
    ] * 2


def test_the_sealed_profile_s_toolchain_library_reaches_every_donor_rewriting(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    from reprobit.discovery_authoring import DiscoveryAuthoringError

    live_root, _staged_root, _trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1), _state(2, 2)),
        qualification_rejections=frozenset({(1, 1), (2, 2)}),
    )
    library = object()
    loads: list[str] = []
    received: list[object] = []

    def load(profile: str) -> object:
        loads.append(profile)
        return library

    def rewriting(*_args: object, helper_library: object = None, **_kwargs: object) -> None:
        received.append(helper_library)
        raise DiscoveryAuthoringError("fixture rewriting refusal")

    monkeypatch.setattr(grind, "_state_rewriting", rewriting)
    callbacks = ProjectGrindCallbacks(
        callbacks.probe_seed,
        callbacks.probe_donors,
        callbacks.cold_verify,
        helper_library=load,
    )

    result = run_project_grind(live_root, callbacks=callbacks)

    assert result.solution is None
    assert loads == ["profile.sealed"]
    assert received == [library, library]


def test_an_unreviewed_toolchain_library_supplies_none(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    from reprobit.classic.toolchain_helpers import HelperLibraryError
    from reprobit.discovery_authoring import DiscoveryAuthoringError

    live_root, _staged_root, _trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1),),
        qualification_rejections=frozenset({(1, 1)}),
    )
    received: list[object] = []

    def load(_profile: str) -> object:
        raise HelperLibraryError("the toolchain library lib/libc.lib is not the reviewed one")

    def rewriting(*_args: object, helper_library: object = None, **_kwargs: object) -> None:
        received.append(helper_library)
        raise DiscoveryAuthoringError("fixture rewriting refusal")

    monkeypatch.setattr(grind, "_state_rewriting", rewriting)
    callbacks = ProjectGrindCallbacks(
        callbacks.probe_seed,
        callbacks.probe_donors,
        callbacks.cold_verify,
        helper_library=load,
    )

    result = run_project_grind(live_root, callbacks=callbacks)

    assert result.solution is None
    assert received == [None]


def test_each_donor_s_own_compile_pdb_reaches_its_rewriting(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    from reprobit.discovery_authoring import DiscoveryAuthoringError

    live_root, _staged_root, _trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1), _state(2, 2)),
        qualification_rejections=frozenset({(1, 1), (2, 2)}),
    )
    received: list[tuple[object, object]] = []

    def rewriting(
        *_args: object,
        donor_object: object = None,
        donor_type_server: object = None,
        **_kwargs: object,
    ) -> None:
        received.append((donor_object, donor_type_server))
        raise DiscoveryAuthoringError("fixture rewriting refusal")

    monkeypatch.setattr(grind, "_state_rewriting", rewriting)

    result = run_project_grind(live_root, callbacks=callbacks)

    assert result.solution is None
    # The object and the PDB come from the one compile: never another donor's.
    assert received == [
        (b"donor object 1.1", b"donor pdb 1.1"),
        (b"donor object 2.2", b"donor pdb 2.2"),
    ]


@pytest.mark.parametrize("type_server", [b"", None])
def test_a_donor_probe_without_its_compile_s_pdb_is_refused(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
    type_server: bytes | None,
) -> None:
    live_root, _staged_root, _trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1),),
    )

    def donors(
        root: Path, donor_ids: tuple[str, ...], progress: grind.DonorProgress | None
    ) -> dict[str, grind.DonorCompileProduct]:
        products = callbacks.probe_donors(root, donor_ids, progress)
        return {
            donor_id: grind.DonorCompileProduct(product.object_payload, cast(bytes, type_server))
            for donor_id, product in products.items()
        }

    with pytest.raises(grind.GrindError, match="incomplete compiler result set"):
        run_project_grind(
            live_root,
            callbacks=ProjectGrindCallbacks(callbacks.probe_seed, donors, callbacks.cold_verify),
        )


def _without_type_servers(
    callbacks: ProjectGrindCallbacks, type_server: bytes | None = None
) -> ProjectGrindCallbacks:
    def donors(
        root: Path, donor_ids: tuple[str, ...], progress: grind.DonorProgress | None
    ) -> dict[str, grind.DonorCompileProduct]:
        products = callbacks.probe_donors(root, donor_ids, progress)
        return {
            donor_id: grind.DonorCompileProduct(product.object_payload, type_server)
            for donor_id, product in products.items()
        }

    return ProjectGrindCallbacks(callbacks.probe_seed, donors, callbacks.cold_verify)


def test_a_unit_without_debug_information_grinds_with_donors_that_have_no_pdb(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    from reprobit.discovery_authoring import DiscoveryAuthoringError

    # The unit compiles without /Zi, so its donors write no type-server PDB:
    # each rewriting receives none, and a14 would refuse for want of it.
    live_root, _staged_root, _trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1),),
        qualification_rejections=frozenset({(1, 1)}),
        compiler_arguments=("/O2",),
    )
    received: list[tuple[object, object]] = []

    def rewriting(
        *_args: object,
        donor_object: object = None,
        donor_type_server: object = None,
        **_kwargs: object,
    ) -> None:
        received.append((donor_object, donor_type_server))
        raise DiscoveryAuthoringError("fixture rewriting refusal")

    monkeypatch.setattr(grind, "_state_rewriting", rewriting)

    result = run_project_grind(live_root, callbacks=_without_type_servers(callbacks))

    assert result.solution is None
    assert received == [(b"donor object 1.1", None)]


def test_a_pdb_from_a_donor_compiled_without_debug_information_is_refused(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    # Without /Zi the compile writes no PDB, so a PDB here came from elsewhere.
    live_root, _staged_root, _trace, callbacks = _install_grind_fixture(
        monkeypatch,
        tmp_path,
        live_states=(_state(1, 1),),
        compiler_arguments=("/O2",),
    )

    with pytest.raises(grind.GrindError, match="incomplete compiler result set"):
        run_project_grind(live_root, callbacks=callbacks)


def test_the_cli_donor_probe_returns_each_compile_s_object_and_pdb(
    monkeypatch: pytest.MonkeyPatch,
    tmp_path: Path,
) -> None:
    import reprobit.discovery_grind_cli as grind_cli

    closed: list[bool] = []

    class Probes:
        def probe_donor_compilers(
            self, donor_ids: tuple[str, ...], *, progress: object
        ) -> tuple[object, ...]:
            del progress
            return tuple(
                SimpleNamespace(
                    donor_id=donor_id,
                    object_payload=f"{donor_id}.obj".encode(),
                    pdb_payload=f"{donor_id}.pdb".encode(),
                )
                for donor_id in donor_ids
            )

    prepared = SimpleNamespace(probes=Probes(), close=lambda: closed.append(True))
    session = tmp_path / "session"
    session.mkdir()
    monkeypatch.setattr(grind_cli, "_prepare_probe", lambda *_args, **_kwargs: (prepared, session))

    products = grind_cli._probe_donors(
        cast(Any, None),
        staged_root=tmp_path,
        donor_ids=("donor.a", "donor.b"),
        progress=None,
    )

    assert products == {
        "donor.a": grind.DonorCompileProduct(b"donor.a.obj", b"donor.a.pdb"),
        "donor.b": grind.DonorCompileProduct(b"donor.b.obj", b"donor.b.pdb"),
    }
    assert closed == [True] and not session.exists()
