"""Bounded project discovery with private proof and atomic publication.

The normal discovery analyzer only produces proposals.  This module is the
small admission path for one deliberately narrow, executable recipe:
declaration-shape compiler state plus strict equal-body composition.  Every
candidate is compiled through project authority, tried in a sealed project
copy, and cold-verified before the real project can be changed.
"""

from __future__ import annotations

from collections.abc import Callable, Mapping
from dataclasses import dataclass
from pathlib import Path, PurePosixPath
from typing import Literal

from reprobit.authority_snapshot import (
    JsonAuthorityDirectorySnapshot,
    assert_json_authority_unchanged,
)
from reprobit.classic_donors import (
    generate_declaration_shape,
    generate_extern_run,
    merge_candidate_constraints,
)
from reprobit.classic_project import ClassicDispatchMaterials, ClassicFamilyDispatcher
from reprobit.costs import calculate_cost
from reprobit.discovery_authoring import (
    AuthoredClassicRecord,
    DeclarationShapeEqualBodyAuthoring,
    DiscoveryAuthoringError,
    build_declaration_shape_donor,
    build_declaration_shape_equal_body,
    build_donor_equal_body,
    build_donor_reloc_layout_equal_body,
    build_extern_run_donor,
    build_measured_function_record,
    merge_authored_records,
)
from reprobit.discovery_contracts import (
    DeclarationFamily,
    DeclarationState,
    DiscoveryError,
    declaration_state_id,
    enumerate_declaration_states,
)
from reprobit.discovery_function_validation import build_function_validation_rewriting
from reprobit.discovery_project import (
    ProjectGrindContext,
    capture_project_grind_inputs,
    resolve_project_grind_context,
    stage_grind_project,
)
from reprobit.discovery_region_resize import build_region_resize_rewriting
from reprobit.discovery_rewriting import build_donor_schedule_rewriting
from reprobit.execution import classic_semantic_obligation_name
from reprobit.intervention_metadata import (
    ClassicRecipeFamily,
    ClassicRecipeRole,
)
from reprobit.model import Digest
from reprobit.msvc_discovery_coff import qualify_msvc_reference_object
from reprobit.progress import ProgressKind
from reprobit.project_loader import load_project_tree
from reprobit.report import Report
from reprobit.schema import (
    ClassicRecipeIntervention,
    InterventionDocument,
    LegacyOracleInstallIntervention,
    ProofDocument,
)
from reprobit.staged_project import ProjectFileSnapshot
from reprobit.strict_json import canonical_json
from reprobit.transactions import CASTransaction


class GrindError(RuntimeError):
    """A grind cannot continue without weakening its admission boundary."""


@dataclass(frozen=True, slots=True)
class ColdTrialEvidence:
    """The public cold verifier's verdict and its self-authenticating report."""

    accepted: bool
    report: Report


SeedProbe = Callable[[Path, str], bytes]
DonorProgress = Callable[[int, int, str], None]
DonorProbe = Callable[[Path, tuple[str, ...], DonorProgress | None], Mapping[str, bytes]]
ColdVerifier = Callable[[Path], ColdTrialEvidence]
GrindProgress = Callable[
    [int, int, str, str, ProgressKind, str | None],
    None,
]


@dataclass(frozen=True, slots=True)
class ProjectGrindCallbacks:
    """Execution seams supplied by the CLI's authenticated runtime."""

    probe_seed: SeedProbe
    probe_donors: DonorProbe
    cold_verify: ColdVerifier


@dataclass(frozen=True, slots=True)
class GrindRejection:
    state_id: str
    stage: Literal["qualification", "cold_verification"]
    reason: str


@dataclass(frozen=True, slots=True)
class GrindSolution:
    state: DeclarationState
    symbol: str
    donor_id: str
    function_id: str
    added_cost: int
    added_interventions: int
    reused_donor: bool
    authority_files: tuple[str, str]
    report: Report
    project_exact: bool = True


@dataclass(frozen=True, slots=True)
class ProjectGrindResult:
    project_id: str
    target_id: str
    translation_unit_id: str
    symbol: str
    states: int
    compiler_trials: int
    qualified_candidates: int
    cold_trials: int
    rejections: tuple[GrindRejection, ...]
    solution: GrindSolution | None
    published: bool
    transaction_id: str | None

    @property
    def exact(self) -> bool:
        return self.solution is not None and self.solution.project_exact

    @property
    def locally_qualified(self) -> bool:
        return self.solution is not None


@dataclass(frozen=True, slots=True)
class _QualifiedCandidate:
    state: DeclarationState
    authored: DeclarationShapeEqualBodyAuthoring
    added_cost: int
    added_interventions: int
    reused_donor: bool
    documents: tuple[InterventionDocument, ProofDocument]


def _relative(root: Path, path: Path) -> str:
    return PurePosixPath(*path.relative_to(root).parts).as_posix()


def _write_staged_documents(
    context: ProjectGrindContext,
    staged_root: Path,
    interventions: InterventionDocument,
    proofs: ProofDocument,
) -> None:
    intervention_path = staged_root.joinpath(
        *PurePosixPath(_relative(context.root, context.intervention_path)).parts
    )
    proof_path = staged_root.joinpath(
        *PurePosixPath(_relative(context.root, context.proof_path)).parts
    )
    intervention_path.write_bytes(canonical_json(interventions))
    proof_path.write_bytes(canonical_json(proofs))


_GRIND_DONOR_FAMILIES = frozenset(
    {ClassicRecipeFamily.DECLARATION_SHAPE, ClassicRecipeFamily.EXTERN_RUN_PAIR}
)


def _int_parameter(state: DeclarationState, name: str) -> int:
    value = state.parameter(name)
    if type(value) is not int:
        raise GrindError(f"{state.family.value} state has a non-integer {name}")
    return value


def _str_parameter(state: DeclarationState, name: str) -> str:
    value = state.parameter(name)
    if type(value) is not str:
        raise GrindError(f"{state.family.value} state has a non-text {name}")
    return value


def _state_shape(state: DeclarationState) -> tuple[int, int]:
    return _int_parameter(state, "classes"), _int_parameter(state, "functions")


@dataclass(frozen=True, slots=True)
class _ExternRun:
    header_prefix: str
    header_count: int
    seat_prefix: str
    seat_count: int
    width: int


def _extern_run(state: DeclarationState) -> _ExternRun:
    return _ExternRun(
        header_prefix=_str_parameter(state, "header_prefix"),
        header_count=_int_parameter(state, "header_count"),
        seat_prefix=_str_parameter(state, "seat_prefix"),
        seat_count=_int_parameter(state, "seat_count"),
        width=_int_parameter(state, "width"),
    )


def _require_grind_family(state: DeclarationState) -> None:
    if state.family not in (
        DeclarationFamily.DECLARATION_SHAPE,
        DeclarationFamily.EXTERN_RUN_PAIR,
    ):
        raise GrindError(f"project grind cannot author a {state.family.value} donor")


_DEFAULT_HEADER_PLACEMENT = "after_includes"


def _header_placement(context: ProjectGrindContext) -> str:
    runs = context.config.extern_runs
    return runs.placement if runs is not None else _DEFAULT_HEADER_PLACEMENT


def _state_digest(state: DeclarationState, context: ProjectGrindContext) -> tuple[str, str]:
    """The generated-header digest and placement the state's donor would carry."""

    _require_grind_family(state)
    if state.family is DeclarationFamily.DECLARATION_SHAPE:
        generated = generate_declaration_shape(*_state_shape(state))
        return Digest.from_bytes(generated).value, _DEFAULT_HEADER_PLACEMENT
    run = _extern_run(state)
    generated = b""
    if run.header_count:
        generated += generate_extern_run(run.header_prefix, run.header_count, run.width)
    if run.seat_count:
        generated += generate_extern_run(run.seat_prefix, run.seat_count, run.width)
    return Digest.from_bytes(generated).value, _header_placement(context)


def _state_donor(state: DeclarationState, context: ProjectGrindContext) -> AuthoredClassicRecord:
    """The payload-free donor record one grind state compiles."""

    _require_grind_family(state)
    unit = context.unit
    if state.family is DeclarationFamily.DECLARATION_SHAPE:
        classes, functions = _state_shape(state)
        return build_declaration_shape_donor(
            target_id=unit.target_id,
            translation_unit_id=unit.id,
            build_target=unit.build_target,
            classes=classes,
            functions=functions,
        )
    run = _extern_run(state)
    return build_extern_run_donor(
        target_id=unit.target_id,
        translation_unit_id=unit.id,
        build_target=unit.build_target,
        header_prefix=run.header_prefix,
        header_count=run.header_count,
        seat_prefix=run.seat_prefix,
        seat_count=run.seat_count,
        width=run.width,
        header_placement=_header_placement(context),
    )


def _state_equal_body(
    state: DeclarationState,
    context: ProjectGrindContext,
    *,
    seed_object: bytes,
    donor_object: bytes,
) -> DeclarationShapeEqualBodyAuthoring:
    """Author the state's donor, naming the symbol, and its strict equal-body consumer."""

    _require_grind_family(state)
    unit = context.unit
    if state.family is DeclarationFamily.DECLARATION_SHAPE:
        classes, functions = _state_shape(state)
        return build_declaration_shape_equal_body(
            target_id=unit.target_id,
            translation_unit_id=unit.id,
            build_target=unit.build_target,
            symbol=context.symbol,
            classes=classes,
            functions=functions,
            seed_object=seed_object,
            donor_object=donor_object,
        )
    run = _extern_run(state)
    donor = build_extern_run_donor(
        target_id=unit.target_id,
        translation_unit_id=unit.id,
        build_target=unit.build_target,
        header_prefix=run.header_prefix,
        header_count=run.header_count,
        seat_prefix=run.seat_prefix,
        seat_count=run.seat_count,
        width=run.width,
        beneficiary_symbols=(context.symbol,),
        header_placement=_header_placement(context),
    )
    try:
        return build_donor_equal_body(
            donor=donor,
            target_id=unit.target_id,
            translation_unit_id=unit.id,
            build_target=unit.build_target,
            symbol=context.symbol,
            seed_object=seed_object,
            donor_object=donor_object,
        )
    except DiscoveryAuthoringError as strict_error:
        # An extern run renumbers the file statics it precedes; the strict
        # splice refuses those renames, the relocation-layout family proves them.
        try:
            return build_donor_reloc_layout_equal_body(
                donor=donor,
                target_id=unit.target_id,
                translation_unit_id=unit.id,
                build_target=unit.build_target,
                symbol=context.symbol,
                seed_object=seed_object,
                donor_object=donor_object,
            )
        except DiscoveryAuthoringError:
            pass
        # A donor whose body has a different length still fits its slot when
        # the same-slot resize family's closed checks hold.
        try:
            record = build_measured_function_record(
                target_id=unit.target_id,
                translation_unit_id=unit.id,
                build_target=unit.build_target,
                symbol=context.symbol,
                family=ClassicRecipeFamily.SAME_SLOT_RESIZE,
                donor_id=donor.intervention.id,
                seed_object=seed_object,
                donor_object=donor_object,
            )
        except DiscoveryAuthoringError:
            raise strict_error from None
        candidate = ClassicFamilyDispatcher().dispatch(
            record.intervention,
            ClassicDispatchMaterials(
                seed_object=seed_object,
                donor_object=donor_object,
                candidate_constraints=merge_candidate_constraints(
                    record.intervention, record.receipt
                ).materialize(),
            ),
        )
        return DeclarationShapeEqualBodyAuthoring(
            donor=donor, function=record, candidate_object=candidate.output, composition_proof=None
        )


def _state_rewriting(
    state: DeclarationState,
    context: ProjectGrindContext,
    *,
    seed_object: bytes,
    donor_object: bytes,
    reference_object: bytes,
) -> DeclarationShapeEqualBodyAuthoring:
    """Author the state's extern-run donor and a donor rewriting reaching the reference.

    A reordering is tried first; when none reaches the reference, a
    region-resize rewriting (whose replacements may change the length); when
    no region replacement proves, a whole-function translation validation.
    """

    _require_grind_family(state)
    if state.family is not DeclarationFamily.EXTERN_RUN_PAIR:
        raise DiscoveryAuthoringError("donor rewriting is authored for extern-run donors only")
    unit = context.unit
    run = _extern_run(state)
    donor = build_extern_run_donor(
        target_id=unit.target_id,
        translation_unit_id=unit.id,
        build_target=unit.build_target,
        header_prefix=run.header_prefix,
        header_count=run.header_count,
        seat_prefix=run.seat_prefix,
        seat_count=run.seat_count,
        width=run.width,
        beneficiary_symbols=(context.symbol,),
        header_placement=_header_placement(context),
    )
    try:
        return build_donor_schedule_rewriting(
            donor=donor,
            target_id=unit.target_id,
            translation_unit_id=unit.id,
            build_target=unit.build_target,
            symbol=context.symbol,
            seed_object=seed_object,
            donor_object=donor_object,
            reference_object=reference_object,
        )
    except DiscoveryAuthoringError as rewriting_error:
        # No reordering reaches the reference, typically because the bodies
        # differ in length: replace the differing regions by the reference's
        # instructions where a path simulation proves them equivalent.
        try:
            return build_region_resize_rewriting(
                donor=donor,
                target_id=unit.target_id,
                translation_unit_id=unit.id,
                build_target=unit.build_target,
                symbol=context.symbol,
                seed_object=seed_object,
                donor_object=donor_object,
                reference_object=reference_object,
            )
        except DiscoveryAuthoringError:
            pass
        # The difference spans the function (registers, spill slots and
        # scheduling across joins and loops): prove the whole body join by join.
        try:
            return build_function_validation_rewriting(
                donor=donor,
                target_id=unit.target_id,
                translation_unit_id=unit.id,
                build_target=unit.build_target,
                symbol=context.symbol,
                seed_object=seed_object,
                donor_object=donor_object,
                reference_object=reference_object,
            )
        except DiscoveryAuthoringError:
            raise rewriting_error from None


def describe_state(state: DeclarationState) -> str:
    """A short human label for one grind state's declarations."""

    if state.family is DeclarationFamily.EXTERN_RUN_PAIR:
        return f"extern run of {state.parameter('header_count')} declarations"
    return f"classes={state.parameter('classes')}, functions={state.parameter('functions')}"


def _advance(
    progress: GrindProgress | None,
    completed: int,
    total: int,
    phase: str,
    item: str,
    *,
    kind: ProgressKind = ProgressKind.UNIT_FINISHED,
    reason: str | None = None,
) -> None:
    if progress is not None:
        progress(completed, total, phase, item, kind, reason)


def _validate_cold_report(
    evidence: ColdTrialEvidence,
    *,
    context: ProjectGrindContext,
    authored: DeclarationShapeEqualBodyAuthoring,
    added_cost: int,
) -> tuple[str | None, bool]:
    """Return a rejection reason and whether the complete project is exact.

    A non-exact report may still close the two local obligations needed to save
    one bounded discovery result: the compiler-produced donor matches the
    project-owned reference object, and the normal semantic checker accepts the
    composed function.  That is useful progress, but it is never represented as
    project certification.
    """

    report = evidence.report
    if report.project_id != context.bundle.spec.project_id:
        return "cold report belongs to a different project", False
    if not report.verdict.cold:
        return "candidate check was not a build from scratch", False
    if not report.verdict.logic_certified:
        return "candidate check did not certify intervention logic", False
    if report.proof.audit_issues:
        return "candidate check contains an authenticity audit defect", False

    existing_legacy = {
        intervention.id
        for intervention in context.bundle.interventions
        if isinstance(intervention, LegacyOracleInstallIntervention)
    }
    if any(item.id not in existing_legacy for item in report.verdict.quarantines):
        return "candidate introduced an authenticity exception", False
    if not report.verdict.toolchain_origin and not existing_legacy:
        return "candidate check did not preserve toolchain origin", False

    original_cost = calculate_cost(context.bundle.interventions).project_total
    if report.costs.project_total != original_cost + added_cost:
        return "cold report cost differs from the admitted intervention delta", False

    certificates = {
        certificate.intervention_id: certificate for certificate in report.proof.certificates
    }
    for record in authored.records:
        intervention = record.intervention
        certificate = certificates.get(intervention.id)
        if certificate is None or not certificate.passed:
            return f"cold report lacks a passing local proof for {intervention.id}", False
        names = {obligation.name for obligation in certificate.obligations}
        expected_semantic = classic_semantic_obligation_name(intervention.family)
        if "fresh_execution" not in names or expected_semantic not in names:
            return f"cold report lacks closed execution proof for {intervention.id}", False
        if (
            len(certificate.semantic_proofs) != 1
            or certificate.semantic_proofs[0].family != intervention.family.value
        ):
            return f"cold report lacks typed semantic proof for {intervention.id}", False

    project_exact = (
        evidence.accepted
        and report.verdict.byte_exact
        and all(target.byte_exact for target in report.targets)
    )
    if report.verdict.byte_exact != all(target.byte_exact for target in report.targets):
        return "candidate report has inconsistent target exactness", False
    if report.verdict.byte_exact and not evidence.accepted:
        return "exact candidate did not satisfy the committed authenticity policy", False
    return None, project_exact


def _publish_solution(
    project_root: Path,
    snapshots: tuple[ProjectFileSnapshot, ...],
    authority_directories: tuple[JsonAuthorityDirectorySnapshot, ...],
    intervention_relative: str,
    proof_relative: str,
    interventions: InterventionDocument,
    proofs: ProofDocument,
) -> str:
    by_path = {snapshot.relative_path: snapshot for snapshot in snapshots}
    if intervention_relative not in by_path or proof_relative not in by_path:
        raise GrindError("grind authority shards were not sealed for publication")

    transaction = CASTransaction(project_root)
    transaction.write(
        intervention_relative,
        canonical_json(interventions),
        expected_sha256=by_path[intervention_relative].digest.value,
    )
    transaction.write(
        proof_relative,
        canonical_json(proofs),
        expected_sha256=by_path[proof_relative].digest.value,
    )
    mutable_paths = frozenset({intervention_relative, proof_relative})
    authority_paths = {
        relative
        for directory in authority_directories
        for relative, _digest in directory.file_digests
    }
    for snapshot in snapshots:
        if snapshot.relative_path in mutable_paths or snapshot.relative_path in authority_paths:
            continue
        transaction.assert_unchanged(
            snapshot.relative_path,
            expected_sha256=snapshot.digest.value,
        )
    assert_json_authority_unchanged(
        transaction,
        authority_directories,
        mutable_paths=mutable_paths,
    )
    result = transaction.commit()
    return result.transaction_id


def require_single_acceptance(
    accept_exact: bool,
    accept_progress: bool,
    *,
    error: Callable[[str], Exception],
    message: str = "exact and progress acceptance are mutually exclusive",
) -> None:
    """Refuse a request that pre-authorizes both exact and progress publication."""

    if accept_exact and accept_progress:
        raise error(message)


def _saved_donor_digests(document: InterventionDocument) -> frozenset[tuple[str, str]]:
    """Generated-header digests and placements of the unit's saved grind-family donors."""

    digests: set[tuple[str, str]] = set()
    for intervention in document.interventions:
        if (
            isinstance(intervention, ClassicRecipeIntervention)
            and intervention.role is ClassicRecipeRole.DONOR
            and intervention.family in _GRIND_DONOR_FAMILIES
        ):
            values = {field.name: field.value for field in intervention.parameters}
            digest = values.get("generated_header_sha256")
            placement = values.get("header_placement", _DEFAULT_HEADER_PLACEMENT)
            if isinstance(digest, str) and isinstance(placement, str):
                digests.add((digest, placement))
    return frozenset(digests)


def run_project_grind(
    project_root: Path,
    *,
    callbacks: ProjectGrindCallbacks,
    plan_relative: str = "reprobit/discovery.json",
    accept_exact: bool = False,
    accept_progress: bool = False,
    progress: GrindProgress | None = None,
) -> ProjectGrindResult:
    """Find the cheapest exact declaration intervention and optionally publish it.

    Acceptance is advance authorization, not evidence.  With or without it,
    candidates pass the same fresh compiler probes and cold semantic checks.
    ``accept_progress`` may publish a locally proven function while other
    project bytes still differ; only an exact cold result is project
    certification.
    """

    require_single_acceptance(accept_exact, accept_progress, error=GrindError)

    live_context = resolve_project_grind_context(
        project_root,
        config_relative=plan_relative,
    )
    snapshot = capture_project_grind_inputs(live_context)
    states: tuple[DeclarationState, ...] = ()
    total = 0
    completed = 0
    rejections: list[GrindRejection] = []
    cold_trials = 0
    chosen_documents: tuple[InterventionDocument, ProofDocument] | None = None
    chosen_paths: tuple[str, str] | None = None
    chosen: GrindSolution | None = None
    progress_choice: (
        tuple[
            _QualifiedCandidate,
            GrindSolution,
            tuple[InterventionDocument, ProofDocument],
            tuple[str, str],
        ]
        | None
    ) = None

    with stage_grind_project(
        live_context.root,
        live_context.bundle.spec.state_dir,
        snapshot.files,
    ) as staged_root:
        # This second load is the only operative authority. The first live
        # context chose the input set; the sealed copy proves that those exact
        # captured bytes form one valid, self-consistent project snapshot.
        context = resolve_project_grind_context(
            staged_root,
            config_relative=plan_relative,
        )
        original_shard_cost = calculate_cost(
            context.intervention_document.interventions
        ).project_total
        try:
            states = enumerate_declaration_states(context.config.plan)
        except DiscoveryError as exc:
            raise GrindError(f"invalid bounded grind plan: {exc}") from exc
        # A state one of the unit's saved donors already renders would share
        # that donor's compiler arena; it is that donor's, not a fresh cell.
        saved_digests = _saved_donor_digests(context.intervention_document)
        states = tuple(
            state for state in states if _state_digest(state, context) not in saved_digests
        )
        # Each state has one compatibility disposition and one cold-trial
        # disposition. States that cannot qualify consume the latter as an
        # explicit skip, keeping one honest and monotonic progress total.
        # Derive the total from sealed authority, never from the earlier live
        # context used only to choose the snapshot input set.
        total = 2 + 3 * len(states)
        _advance(
            progress,
            completed,
            total,
            "grind-seed",
            "Compiling the project's current translation unit",
            kind=ProgressKind.PHASE_STARTED,
        )
        seed_object = callbacks.probe_seed(staged_root, context.compiler_node.id)
        if type(seed_object) is not bytes or not seed_object:
            raise GrindError("compiler seed probe returned no immutable COFF object")
        completed += 1
        _advance(progress, completed, total, "grind-seed", context.compiler_node.id)

        provisional: list[tuple[DeclarationState, AuthoredClassicRecord]] = []
        for state in states:
            provisional.append((state, _state_donor(state, context)))
        provisional_documents = merge_authored_records(
            context.intervention_document,
            context.proof_document,
            tuple(record for _state, record in provisional),
        )
        _write_staged_documents(context, staged_root, *provisional_documents)
        load_project_tree(staged_root)
        donor_ids = tuple(record.intervention.id for _state, record in provisional)
        _advance(
            progress,
            completed,
            total,
            "grind-donors",
            f"Compiling {len(donor_ids)} bounded declaration candidate(s)",
            kind=ProgressKind.PHASE_STARTED,
        )
        donor_completed = 0

        def donor_progress(done: int, donor_total: int, donor_id: str) -> None:
            nonlocal completed, donor_completed
            if donor_total != len(donor_ids) or done != donor_completed + 1:
                raise GrindError("donor compiler progress differs from the sealed campaign")
            donor_completed = done
            completed += 1
            _advance(progress, completed, total, "grind-donors", donor_id)

        donor_objects = dict(callbacks.probe_donors(staged_root, donor_ids, donor_progress))
        if donor_completed != len(donor_ids):
            raise GrindError("donor compiler probe omitted completion progress")
        if set(donor_objects) != set(donor_ids) or any(
            type(payload) is not bytes or not payload for payload in donor_objects.values()
        ):
            raise GrindError("donor probe returned an incomplete compiler result set")
        reference_object = context.reference_path.read_bytes()
        qualified: list[_QualifiedCandidate] = []
        original_ids = {item.id for item in context.intervention_document.interventions}
        for state, provisional_record in provisional:
            state_id = declaration_state_id(state)
            rejected = False
            try:
                donor_object = donor_objects[provisional_record.intervention.id]
                try:
                    authored = _state_equal_body(
                        state,
                        context,
                        seed_object=seed_object,
                        donor_object=donor_object,
                    )
                    qualify_msvc_reference_object(
                        reference_object=reference_object,
                        candidate_object=authored.candidate_object,
                        symbol=context.symbol,
                    )
                except (DiscoveryAuthoringError, DiscoveryError) as splice_error:
                    # The donor holds the reference's instructions in another
                    # order: a proved reorder of its body reaches the reference.
                    try:
                        authored = _state_rewriting(
                            state,
                            context,
                            seed_object=seed_object,
                            donor_object=donor_object,
                            reference_object=reference_object,
                        )
                    except DiscoveryAuthoringError:
                        raise splice_error from None
                    qualify_msvc_reference_object(
                        reference_object=reference_object,
                        candidate_object=authored.candidate_object,
                        symbol=context.symbol,
                    )
                if authored.donor.intervention.id != provisional_record.intervention.id:
                    raise GrindError("final donor identity differs from its compiler probe")
                final_documents = merge_authored_records(
                    context.intervention_document,
                    context.proof_document,
                    authored.records,
                )
                reused_donor = authored.donor.intervention.id in original_ids
                merged_shard_cost = calculate_cost(final_documents[0].interventions).project_total
                added_cost = merged_shard_cost - original_shard_cost
                if added_cost <= 0:
                    raise GrindError("qualified discovery did not add positive intervention cost")
                qualified.append(
                    _QualifiedCandidate(
                        state=state,
                        authored=authored,
                        added_cost=added_cost,
                        added_interventions=1 if reused_donor else 2,
                        reused_donor=reused_donor,
                        documents=final_documents,
                    )
                )
            except (DiscoveryAuthoringError, DiscoveryError) as exc:
                rejections.append(
                    GrindRejection(
                        state_id=state_id,
                        stage="qualification",
                        reason=str(exc),
                    )
                )
                rejected = True
            completed += 1
            _advance(progress, completed, total, "grind-qualify", state_id)
            if rejected:
                completed += 1
                _advance(
                    progress,
                    completed,
                    total,
                    "grind-skip",
                    state_id,
                )

        qualified.sort(key=lambda item: (item.added_cost, canonical_json(item.state)))
        for candidate in qualified:
            state_id = declaration_state_id(candidate.state)
            final_documents = candidate.documents
            _write_staged_documents(context, staged_root, *final_documents)
            load_project_tree(staged_root)
            cold_trials += 1
            _advance(
                progress,
                completed,
                total,
                "grind-verify",
                f"Verifying {state_id} from scratch",
                kind=ProgressKind.PHASE_STARTED,
            )
            evidence = callbacks.cold_verify(staged_root)
            reason, project_exact = _validate_cold_report(
                evidence,
                context=context,
                authored=candidate.authored,
                added_cost=candidate.added_cost,
            )
            completed += 1
            if reason is not None:
                rejections.append(
                    GrindRejection(
                        state_id=state_id,
                        stage="cold_verification",
                        reason=reason,
                    )
                )
                _advance(
                    progress,
                    completed,
                    total,
                    "grind-verify",
                    state_id,
                )
                # The next verifier may construct another very large report.
                # Release rejected evidence before entering that call.
                del evidence
                continue
            _advance(progress, completed, total, "grind-verify", state_id)
            candidate_paths = (
                _relative(context.root, context.intervention_path),
                _relative(context.root, context.proof_path),
            )
            candidate_solution = GrindSolution(
                state=candidate.state,
                symbol=context.symbol,
                donor_id=candidate.authored.donor.intervention.id,
                function_id=candidate.authored.function.intervention.id,
                added_cost=candidate.added_cost,
                added_interventions=candidate.added_interventions,
                reused_donor=candidate.reused_donor,
                authority_files=candidate_paths,
                report=evidence.report,
                project_exact=project_exact,
            )
            # Progress mode is deliberately a cheapest-first fire-and-forget
            # path.  Once the first sorted candidate passes the same cold
            # local proof, publishing it is useful even when the whole image
            # still differs. Preview and exact-only approval keep searching
            # for a complete project match.
            if project_exact or accept_progress:
                chosen_documents = final_documents
                chosen_paths = candidate_paths
                chosen = candidate_solution
                break
            if progress_choice is None:
                progress_choice = (
                    candidate,
                    candidate_solution,
                    final_documents,
                    candidate_paths,
                )

        if chosen is None and progress_choice is not None:
            _candidate, chosen, chosen_documents, chosen_paths = progress_choice

        for candidate in qualified[cold_trials:]:
            completed += 1
            _advance(
                progress,
                completed,
                total,
                "grind-skip",
                declaration_state_id(candidate.state),
            )

    # Progress accounting is an internal completeness invariant. Check it
    # before the only live-project mutation so an instrumentation regression
    # can never turn a successful CAS commit into a reported failure.
    if completed + 1 != total:
        raise AssertionError("grind progress accounting differs from its bounded plan")

    published = False
    transaction_id: str | None = None
    publish_authorized = chosen is not None and (
        accept_progress or (accept_exact and chosen.project_exact)
    )
    if publish_authorized:
        if chosen is None:
            raise AssertionError("grind publication omitted its chosen result")
        if chosen_documents is None or chosen_paths is None:
            raise AssertionError("grind result omitted its authority documents")
        _advance(
            progress,
            completed,
            total,
            "grind-publish",
            "Publishing the locally proven intervention pair",
            kind=ProgressKind.PHASE_STARTED,
        )
        transaction_id = _publish_solution(
            live_context.root,
            snapshot.files,
            snapshot.authority_directories,
            *chosen_paths,
            *chosen_documents,
        )
        reloaded = load_project_tree(live_context.root)
        admitted_ids = {intervention.id for intervention in reloaded.interventions}
        if {chosen.donor_id, chosen.function_id} - admitted_ids:
            raise GrindError("published discovery authority did not reload exactly")
        published = True

    _advance(
        progress,
        total,
        total,
        "grind-finalize",
        (
            "exact solution"
            if chosen is not None and chosen.project_exact
            else ("local progress" if chosen is not None else "bounded search complete")
        ),
    )

    return ProjectGrindResult(
        project_id=context.bundle.spec.project_id,
        target_id=context.unit.target_id,
        translation_unit_id=context.unit.id,
        symbol=context.symbol,
        states=len(states),
        compiler_trials=1 + len(states),
        qualified_candidates=len(qualified),
        cold_trials=cold_trials,
        rejections=tuple(rejections),
        solution=chosen,
        published=published,
        transaction_id=transaction_id,
    )


__all__ = [
    "ColdTrialEvidence",
    "GrindError",
    "GrindRejection",
    "GrindSolution",
    "ProjectGrindCallbacks",
    "ProjectGrindResult",
    "require_single_acceptance",
    "run_project_grind",
]
