"""Bounded CMake Makefiles producer-graph extraction."""

from __future__ import annotations

import os
import re
from collections import Counter
from collections.abc import Mapping, Sequence
from dataclasses import dataclass
from pathlib import Path, PurePosixPath

from reprobit.cmake_graph_paths import (
    attached_value as _attached_value,
)
from reprobit.cmake_graph_paths import (
    build_working_directory as _build_working_directory,
)
from reprobit.cmake_graph_paths import (
    normalize_arguments as _normalize_arguments,
)
from reprobit.cmake_graph_paths import (
    path_reference as _path_reference,
)
from reprobit.cmake_graph_paths import (
    replace_attached_value as _replace_attached_value,
)
from reprobit.cmake_graph_paths import (
    toolchain_executable as _toolchain_executable,
)
from reprobit.cmake_makefile_metadata import (
    MetadataReader,
    read_compile_database,
)
from reprobit.cmake_makefile_metadata import (
    command_recipe as _command_recipe,
)
from reprobit.cmake_makefile_metadata import (
    compile_commands as _compile_commands,
)
from reprobit.cmake_makefile_metadata import (
    expand_response as _expand_response,
)
from reprobit.cmake_makefile_metadata import (
    metadata_files as _metadata_files,
)
from reprobit.cmake_makefile_metadata import (
    resource_commands as _resource_commands,
)
from reprobit.cmake_makefile_metadata import (
    split_command_line as _split_command_line,
)
from reprobit.coff_weak_alias import (
    CoffWeakAliasDeclaration,
    CoffWeakAliasError,
    CoffWeakSearch,
    declare_coff_weak_alias,
    parse_alias_argument,
    read_coff_weak_alias,
)
from reprobit.model import Digest
from reprobit.producer_graph import (
    ProducerGraphDocument,
    ProducerGraphError,
    ProducerNode,
    ProducerRole,
    graph_reference,
    toolchain_system_library,
    validate_graph_reference,
)

_LINK_RECIPE = re.compile(r'(?i)(?:^|[/\\"])(?:link|link\.exe|lib|lib\.exe)(?=(?:"|\s|$))')
# The one project custom command the import maps to a ReproBit producer: lrr's
# ``python3 <source>/tools/coff_weak_external.py OUT WEAK=DEFAULT...``.  The
# import never runs that script; it reads the alias set from the argv and
# ReproBit's own producer writes the object in each run.
COFF_WEAK_ALIAS_SCRIPT = "source/tools/coff_weak_external.py"
_PYTHON_PROGRAM = re.compile(r"(?i)python(?:3(?:\.[0-9]+)?)?(?:\.exe)?")
_CMAKE_ECHO = re.compile(r"^@?\$\(CMAKE_COMMAND\) -E cmake_echo_color ")


@dataclass(frozen=True, slots=True)
class _RawNode:
    role: ProducerRole
    owner: str
    arguments: tuple[str, ...]
    outputs: tuple[str, ...]
    working_directory: Path
    inputs: tuple[str, ...] = ()
    coff_weak_alias: CoffWeakAliasDeclaration | None = None


def _nmake_inline_response(
    arguments: tuple[str, ...],
    lines: list[str],
    offset: int,
    *,
    owner: str,
) -> tuple[tuple[str, ...], int]:
    """Fold one bounded NMake ``@<<`` response block into its command."""

    markers = tuple(index for index, argument in enumerate(arguments) if argument == "@<<")
    if not markers:
        return arguments, offset
    if len(markers) != 1:
        raise ProducerGraphError(f"CMake target {owner!r} has ambiguous inline link metadata")

    body: list[str] = []
    while offset < len(lines):
        line = lines[offset].strip()
        offset += 1
        if line == "<<":
            marker = markers[0]
            expanded = _split_command_line(" ".join(body))
            return arguments[:marker] + expanded + arguments[marker + 1 :], offset
        tokens = _split_command_line(line)
        if "@<<" in tokens or "<<" in tokens:
            raise ProducerGraphError(f"CMake target {owner!r} has malformed inline link metadata")
        body.append(line)
    raise ProducerGraphError(f"CMake target {owner!r} has unterminated inline link metadata")


def _normalize_directive_inputs(
    target_outputs: Mapping[str, str],
    directive_inputs: Mapping[str, Sequence[str]] | None,
) -> dict[str, tuple[str, ...]]:
    normalized: dict[str, tuple[str, ...]] = {}
    for target_id, references in (directive_inputs or {}).items():
        if target_id not in target_outputs:
            raise ProducerGraphError(f"directive inputs name unknown target {target_id!r}")
        canonical = tuple(validate_graph_reference(value) for value in references)
        if any(not value.startswith("system-library/") for value in canonical):
            raise ProducerGraphError("directive inputs must be system-library references")
        if len({value.casefold() for value in canonical}) != len(canonical) or canonical != tuple(
            sorted(canonical, key=str.casefold)
        ):
            raise ProducerGraphError(
                f"directive inputs for {target_id!r} are not canonical and unique"
            )
        normalized[target_id] = canonical
    return normalized


def _compiler_nodes(
    raw_database: list[object],
    *,
    build_root: Path,
    source_root: Path,
    toolchain_root: Path,
) -> tuple[_RawNode, ...]:
    commands = _compile_commands(
        raw_database,
        build_root=build_root,
        source_root=source_root,
        toolchain_root=toolchain_root,
    )
    pdb_directory_owners = Counter(
        command.pdb_directory_ref.casefold()
        for command in commands
        if command.pdb_directory_ref is not None
    )
    nodes: list[_RawNode] = []
    for command in commands:
        arguments = command.arguments
        pdb_ref = command.pdb_ref
        if command.pdb_directory_ref is not None:
            if pdb_directory_owners[command.pdb_directory_ref.casefold()] == 1:
                # Preserve authentic CMake argv for a directory's sole owner.
                # VC 4.2 materializes ``vc40.pdb`` beneath that directory.
                pdb_ref = command.pdb_directory_ref.rstrip("/") + "/vc40.pdb"
            else:
                # Shared ``vc40.pdb`` is incompatible with isolated compiler
                # lanes. Make the per-TU policy explicit as ``<object>.pdb``.
                # This changes debug-path input and is not byte-neutral by itself.
                pdb_ref = command.output_ref + ".pdb"
                pdb_relative = PurePosixPath(pdb_ref.removeprefix("build/"))
                pdb_path = build_root.joinpath(*pdb_relative.parts)
                arguments = _replace_attached_value(
                    arguments,
                    ("/Fd", "-Fd"),
                    os.fspath(pdb_path),
                )
        assert pdb_ref is not None
        nodes.append(
            _RawNode(
                role=ProducerRole.COMPILER,
                owner=command.owner,
                arguments=arguments[1:],
                inputs=(command.source_ref,),
                outputs=(command.output_ref, pdb_ref),
                working_directory=command.directory,
            )
        )
    return tuple(nodes)


def _resource_nodes(
    *,
    build_root: Path,
    source_root: Path,
    toolchain_root: Path,
    reader: MetadataReader,
) -> tuple[_RawNode, ...]:
    nodes: list[_RawNode] = []
    for owner, directory, arguments in _resource_commands(
        build_root,
        toolchain_root=toolchain_root,
        reader=reader,
    ):
        output = _attached_value(arguments, ("/fo", "-fo"))
        if output is None or not arguments:
            raise ProducerGraphError("resource command omits its output")
        output_ref = _path_reference(
            output,
            working_directory=directory,
            source_root=source_root,
            build_root=build_root,
            toolchain_root=toolchain_root,
        )
        source_ref = _path_reference(
            arguments[-1],
            working_directory=directory,
            source_root=source_root,
            build_root=build_root,
            toolchain_root=toolchain_root,
        )
        if not output_ref.startswith("build/"):
            raise ProducerGraphError("resource output is outside the configured build")
        nodes.append(
            _RawNode(
                role=ProducerRole.RESOURCE,
                owner=owner,
                arguments=arguments,
                inputs=(source_ref,),
                outputs=(output_ref,),
                working_directory=directory,
            )
        )
    return tuple(nodes)


def _link_outputs(
    *,
    owner: str,
    role: ProducerRole,
    arguments: tuple[str, ...],
    directory: Path,
    source_root: Path,
    build_root: Path,
    toolchain_root: Path,
) -> tuple[str, ...]:
    output = _attached_value(arguments, ("/out:", "-out:"))
    if output is None:
        raise ProducerGraphError(f"link command for {owner!r} omits /out")
    outputs = [
        _path_reference(
            output,
            working_directory=directory,
            source_root=source_root,
            build_root=build_root,
            toolchain_root=toolchain_root,
        )
    ]
    if role is ProducerRole.LIBRARIAN and _attached_value(arguments, ("/def:", "-def:")):
        # LIB /DEF writes the export file beside the import library.
        archive = _attached_value(arguments, ("/out:", "-out:"))
        if archive is None:
            raise ProducerGraphError(f"librarian /DEF command for {owner!r} omits /out")
        outputs.append(
            _path_reference(
                os.fspath(Path(archive).with_suffix(".exp")),
                working_directory=directory,
                source_root=source_root,
                build_root=build_root,
                toolchain_root=toolchain_root,
            )
        )
    if role is ProducerRole.LINKER:
        switches = {item.casefold() for item in arguments}
        implementation_library = _attached_value(arguments, ("/implib:", "-implib:"))
        if switches & {"/dll", "-dll"}:
            if implementation_library is None:
                raise ProducerGraphError(f"DLL link command for {owner!r} omits /implib")
            outputs.append(
                _path_reference(
                    implementation_library,
                    working_directory=directory,
                    source_root=source_root,
                    build_root=build_root,
                    toolchain_root=toolchain_root,
                )
            )
            outputs.append(
                _path_reference(
                    os.fspath(Path(implementation_library).with_suffix(".exp")),
                    working_directory=directory,
                    source_root=source_root,
                    build_root=build_root,
                    toolchain_root=toolchain_root,
                )
            )
        has_debug = any(
            item.casefold() in {"/debug", "-debug"}
            or item.casefold().startswith(("/debug:", "-debug:"))
            for item in arguments
        )
        if has_debug:
            pdb = _attached_value(arguments, ("/pdb:", "-pdb:"))
            if pdb is None:
                raise ProducerGraphError(f"debug link command for {owner!r} omits /pdb")
            outputs.append(
                _path_reference(
                    pdb,
                    working_directory=directory,
                    source_root=source_root,
                    build_root=build_root,
                    toolchain_root=toolchain_root,
                )
            )
    if any(not reference.startswith("build/") for reference in outputs):
        raise ProducerGraphError(f"link outputs for {owner!r} leave the build seat")
    return tuple(outputs)


def _link_nodes(
    *,
    build_root: Path,
    source_root: Path,
    toolchain_root: Path,
    reader: MetadataReader,
) -> tuple[_RawNode, ...]:
    nodes: list[_RawNode] = []

    def append(owner: str, directory: Path, arguments: tuple[str, ...]) -> None:
        if not arguments:
            raise ProducerGraphError(f"empty link command for {owner!r}")
        executable_path = _toolchain_executable(
            arguments[0],
            working_directory=directory,
            toolchain_root=toolchain_root,
            label=f"link command for {owner!r}",
        )
        expanded = _expand_response(
            arguments[1:],
            build_root=build_root,
            working_directory=directory,
            reader=reader,
        )
        executable = executable_path.name.casefold()
        role = ProducerRole.LIBRARIAN if executable in {"lib", "lib.exe"} else ProducerRole.LINKER
        nodes.append(
            _RawNode(
                role=role,
                owner=owner,
                arguments=expanded,
                outputs=_link_outputs(
                    owner=owner,
                    role=role,
                    arguments=expanded,
                    directory=directory,
                    source_root=source_root,
                    build_root=build_root,
                    toolchain_root=toolchain_root,
                ),
                working_directory=directory,
            )
        )

    for link_file in _metadata_files(build_root, "link.txt"):
        owner = link_file.parent.name.removesuffix(".dir")
        directory = _build_working_directory(
            link_file.parent.parent.parent,
            build_root=build_root,
            label=f"link target {owner!r} working directory",
        )
        command_text = reader.read_text(
            link_file,
            label=f"link target {owner!r} metadata",
        ).strip()
        append(owner, directory, _split_command_line(command_text))

    # CMake's NMake generator deliberately disables link scripts, so its
    # authenticated LINK/LIB invocation lives directly in build.make.  Unix
    # Makefiles retain link.txt and take the path above.
    for makefile in _metadata_files(build_root, "build.make"):
        if (makefile.parent / "link.txt").is_file():
            continue
        owner = makefile.parent.name.removesuffix(".dir")
        declared_directory = _build_working_directory(
            makefile.parent.parent.parent,
            build_root=build_root,
            label=f"link target {owner!r} working directory",
        )
        candidates: list[tuple[Path, tuple[str, ...]]] = []
        lines = reader.read_text(
            makefile,
            label=f"link target {owner!r} build metadata",
        ).splitlines()
        offset = 0
        while offset < len(lines):
            raw_line = lines[offset]
            offset += 1
            line = raw_line.strip()
            if not line or line.startswith("#"):
                continue
            if _LINK_RECIPE.search(line.removeprefix("@")) is None:
                continue
            directory, arguments = _command_recipe(
                line,
                declared_working_directory=declared_directory,
                build_root=build_root,
            )
            if not arguments or Path(arguments[0]).name.casefold() not in {
                "link",
                "link.exe",
                "lib",
                "lib.exe",
            }:
                continue
            arguments, offset = _nmake_inline_response(
                arguments,
                lines,
                offset,
                owner=owner,
            )
            _toolchain_executable(
                arguments[0],
                working_directory=directory,
                toolchain_root=toolchain_root,
                label=f"link command for {owner!r}",
            )
            candidates.append((directory, arguments))
        if len(candidates) > 1:
            raise ProducerGraphError(f"CMake target {owner!r} has ambiguous link metadata")
        if candidates:
            append(owner, *candidates[0])
    return tuple(nodes)


def _custom_command_rules(
    build_root: Path,
    *,
    reader: MetadataReader,
) -> dict[str, tuple[str, Path, tuple[str, ...], Path]]:
    """Return each build.make rule target with its owner, directory and recipe.

    Keys are case-folded absolute target paths.  A rule's recipe is its run of
    tab-indented lines; CMake's own progress echo is dropped.
    """

    rules: dict[str, tuple[str, Path, tuple[str, ...], Path]] = {}
    for makefile in _metadata_files(build_root, "build.make"):
        owner = makefile.parent.name.removesuffix(".dir")
        directory = _build_working_directory(
            makefile.parent.parent.parent,
            build_root=build_root,
            label=f"custom command target {owner!r} working directory",
        )
        lines = reader.read_text(
            makefile, label=f"custom command target {owner!r} build metadata"
        ).splitlines()
        offset = 0
        while offset < len(lines):
            line = lines[offset]
            offset += 1
            if not line or line[0].isspace() or line.startswith("#") or ":" not in line:
                continue
            head = line.split(": ", 1)[0] if ": " in line else line.rstrip(":")
            if not head.casefold().endswith(".obj") or " " in head:
                continue
            recipe: list[str] = []
            while offset < len(lines) and lines[offset].startswith("\t"):
                command = lines[offset].strip()
                offset += 1
                if command and _CMAKE_ECHO.match(command) is None:
                    recipe.append(command)
            if not recipe:
                # A dependency-only line (``x.obj: flags.make``) carries no command.
                continue
            target = Path(head)
            if not target.is_absolute():
                target = directory / target
            key = os.fspath(target.resolve(strict=False)).casefold()
            if key in rules:
                raise ProducerGraphError(f"CMake custom command target {head!r} is ambiguous")
            rules[key] = (owner, directory, tuple(recipe), makefile)
    return rules


def _coff_weak_alias_nodes(
    nodes: Sequence[_RawNode],
    *,
    build_root: Path,
    source_root: Path,
    toolchain_root: Path,
    reader: MetadataReader,
) -> tuple[_RawNode, ...]:
    """Map lrr's weak-alias custom command to ReproBit's in-run producer.

    Only an object that a linker or librarian consumes and no toolchain node
    produces is looked up, so ordinary projects see no change.  Its CMake rule
    must be exactly ``<python> ${SOURCE}/tools/coff_weak_external.py
    [--search=nolibrary|library|alias] OUT WEAK=DEFAULT...``; any other custom
    command is refused rather than guessed at.  Without ``--search`` the
    script's documented default, NOLIBRARY, is declared.  The script is never
    run.  When the configured build already holds the object (the project's own
    build wrote it), its bytes must be the ones ReproBit writes for the same
    alias set.
    """

    produced = {output.casefold() for node in nodes for output in node.outputs}
    wanted: dict[str, str] = {}
    for node in nodes:
        if node.role not in {ProducerRole.LINKER, ProducerRole.LIBRARIAN}:
            continue
        for reference in node.inputs:
            if (
                reference.startswith("build/")
                and PurePosixPath(reference).suffix.casefold() == ".obj"
                and reference.casefold() not in produced
            ):
                wanted.setdefault(reference.casefold(), reference)
    if not wanted:
        return ()
    rules = _custom_command_rules(build_root, reader=reader)
    result: list[_RawNode] = []
    for reference in sorted(wanted.values(), key=str.casefold):
        path = build_root.joinpath(*PurePosixPath(reference.removeprefix("build/")).parts)
        rule = rules.get(os.fspath(path.resolve(strict=False)).casefold())
        if rule is None:
            # Left unproduced: the graph refuses it as an object without
            # current-run ancestry.
            continue
        owner, declared_directory, recipe, makefile = rule
        label = f"custom command for {reference!r} ({makefile.relative_to(build_root)})"
        if len(recipe) != 1:
            raise ProducerGraphError(f"{label} must be one command, found {len(recipe)}")
        if "$" in recipe[0] or "`" in recipe[0]:
            raise ProducerGraphError(f"{label} uses make or shell expansion")
        directory, tokens = _command_recipe(
            recipe[0],
            declared_working_directory=declared_directory,
            build_root=build_root,
        )
        if (
            len(tokens) < 4
            or _PYTHON_PROGRAM.fullmatch(Path(tokens[0]).name) is None
            or any(token in {"&&", "||", ";", "|", ">", "<"} for token in tokens)
        ):
            raise ProducerGraphError(
                f"{label} is not an importable command; ReproBit imports only "
                "'python3 <project>/tools/coff_weak_external.py OUT WEAK=DEFAULT ...'"
            )

        def seat(value: str, *, current: Path = directory) -> str:
            return _path_reference(
                value,
                working_directory=current,
                source_root=source_root,
                build_root=build_root,
                toolchain_root=toolchain_root,
            )

        operands = list(tokens[2:])
        search = CoffWeakSearch.NOLIBRARY
        if operands and operands[0].startswith("--search="):
            # The project names the characteristic itself; without it, the
            # script's documented default (NOLIBRARY) applies.
            try:
                search = CoffWeakSearch(operands.pop(0).removeprefix("--search="))
            except ValueError as error:
                raise ProducerGraphError(
                    f"{label} names an unknown search characteristic: {error}"
                ) from error
        if len(operands) < 2:
            raise ProducerGraphError(f"{label} declares no output and alias set")
        script = seat(tokens[1])
        if script != COFF_WEAK_ALIAS_SCRIPT:
            raise ProducerGraphError(
                f"{label} runs an unknown script {script!r}; ReproBit imports only "
                f"{COFF_WEAK_ALIAS_SCRIPT!r}, never running it"
            )
        if seat(operands[0]).casefold() != reference.casefold():
            raise ProducerGraphError(f"{label} writes {operands[0]!r}, not its rule target")
        try:
            declaration = declare_coff_weak_alias(
                tuple(parse_alias_argument(value) for value in operands[1:]),
                search=search,
            )
        except (CoffWeakAliasError, ValueError) as error:
            raise ProducerGraphError(f"{label} declares an invalid alias set: {error}") from error
        if os.path.lexists(path):
            if path.is_symlink() or not path.is_file():
                raise ProducerGraphError(f"{label}: the project's output is redirected: {path}")
            written = path.read_bytes()
            if written != declaration.payload():
                try:
                    detail = f"it declares {read_coff_weak_alias(written)}"
                except CoffWeakAliasError as error:
                    detail = str(error)
                raise ProducerGraphError(
                    f"{label}: the project's build wrote different bytes from ReproBit's "
                    f"producer for the same alias set ({detail})"
                )
        result.append(
            _RawNode(
                role=ProducerRole.COFF_WEAK_ALIAS,
                owner=owner,
                arguments=(),
                outputs=(reference,),
                working_directory=directory,
                coff_weak_alias=declaration,
            )
        )
    return tuple(result)


def _normalize_node(
    node: _RawNode,
    *,
    source_root: Path,
    build_root: Path,
    toolchain_root: Path,
    produced_relatives: frozenset[str],
) -> _RawNode:
    arguments = _normalize_arguments(
        node.arguments,
        working_directory=node.working_directory,
        source_root=source_root,
        build_root=build_root,
        toolchain_root=toolchain_root,
        produced_relatives=produced_relatives,
    )
    inputs = set(node.inputs)
    for argument in arguments:
        plain = argument
        for prefix in ("/DEF:", "-DEF:"):
            if plain.casefold().startswith(prefix.casefold()):
                plain = plain[len(prefix) :]
                break
        if plain.startswith("${SOURCE}/"):
            relative = plain.removeprefix("${SOURCE}/")
            path = source_root.joinpath(*PurePosixPath(relative).parts)
            if path.is_file():
                kind = (
                    "quarantine-archive"
                    if node.role is ProducerRole.LINKER and path.suffix.casefold() == ".lib"
                    else "source"
                )
                inputs.add(graph_reference(kind, relative))
        elif plain.startswith("${BUILD}/"):
            inputs.add(graph_reference("build", plain.removeprefix("${BUILD}/")))
        elif re.fullmatch(r"(?i)[a-z0-9_.+@-]+\.lib", plain):
            inputs.add(graph_reference("system-library", plain))
        elif node.role is ProducerRole.LINKER and plain == argument:
            # A library named by its toolchain path keeps that spelling in
            # argv (LINK searches a name once, so a repeat spelled as a path
            # is searched again) and is the same locked system library.
            try:
                toolchain_library = toolchain_system_library(plain)
            except ValueError as error:
                raise ProducerGraphError(
                    f"CMake target {node.owner!r} links an unsupported toolchain library: {plain!r}"
                ) from error
            if toolchain_library is not None:
                inputs.add(graph_reference("system-library", toolchain_library[1]))
    inputs.difference_update(node.outputs)
    return _RawNode(
        role=node.role,
        owner=node.owner,
        arguments=arguments,
        inputs=tuple(sorted(inputs, key=str.casefold)),
        outputs=tuple(sorted(node.outputs, key=str.casefold)),
        working_directory=node.working_directory,
    )


def _producer_nodes(
    raw_nodes: Sequence[_RawNode],
    *,
    target_outputs: Mapping[str, str],
    directive_inputs: Mapping[str, tuple[str, ...]],
) -> tuple[ProducerNode, ...]:
    output_owner = {
        output.casefold(): index for index, node in enumerate(raw_nodes) for output in node.outputs
    }
    node_ids = [
        f"{node.role.value}.{node.owner}.{index:04d}" for index, node in enumerate(raw_nodes)
    ]
    final_by_output = {
        graph_reference("build", relative): target_id
        for target_id, relative in target_outputs.items()
    }
    matched_targets = {
        final_by_output[output]
        for node in raw_nodes
        for output in node.outputs
        if output in final_by_output
    }
    missing_targets = set(target_outputs) - matched_targets
    if missing_targets:
        expected = ", ".join(
            f"{target_id}=build/{target_outputs[target_id]}"
            for target_id in sorted(missing_targets, key=str.casefold)
        )
        observed = ", ".join(
            output
            for node in raw_nodes
            if node.role is ProducerRole.LINKER
            for output in node.outputs
        )
        raise ProducerGraphError(
            "terminal target output was not found in CMake linker metadata; "
            f"expected [{expected}], observed [{observed or 'none'}]"
        )
    nodes: list[ProducerNode] = []
    for index, node in enumerate(raw_nodes):
        target_ids = {final_by_output[item] for item in node.outputs if item in final_by_output}
        if len(target_ids) > 1 or (target_ids and node.role is not ProducerRole.LINKER):
            raise ProducerGraphError("terminal target output has an invalid producer role")
        target_id = next(iter(target_ids), None)
        dependencies = {
            node_ids[output_owner[input_ref.casefold()]]
            for input_ref in node.inputs
            if input_ref.casefold() in output_owner
        }
        nodes.append(
            ProducerNode(
                id=node_ids[index],
                role=node.role,
                owner=node.owner,
                target_id=target_id,
                arguments=node.arguments,
                inputs=node.inputs,
                directive_inputs=directive_inputs.get(target_id, ()) if target_id else (),
                outputs=node.outputs,
                depends_on=tuple(sorted(dependencies, key=str.casefold)),
                coff_weak_alias=node.coff_weak_alias,
            )
        )
    terminal_targets = {node.target_id for node in nodes if node.target_id is not None}
    unused_directive_targets = set(directive_inputs) - terminal_targets
    if unused_directive_targets:
        raise ProducerGraphError(
            "directive inputs lack a terminal linker: "
            + ", ".join(sorted(unused_directive_targets, key=str.casefold))
        )
    return tuple(nodes)


def extract_cmake_makefiles_graph(
    *,
    configured_build_root: Path,
    effective_source_root: Path,
    toolchain_root: Path,
    toolchain_lock_digest: Digest,
    path_profile_id: str,
    target_outputs: Mapping[str, str],
    directive_inputs: Mapping[str, Sequence[str]] | None = None,
) -> ProducerGraphDocument:
    """Extract a reviewable graph from one-time CMake configuration metadata.

    This function is intentionally not called by certification.  Its output is
    committed, reviewed, and reloaded as authority on later runs.
    """

    build_root = configured_build_root.resolve(strict=True)
    source_root = effective_source_root.resolve(strict=True)
    toolchain = toolchain_root.resolve(strict=True)
    raw_database = read_compile_database(build_root)
    metadata_reader = MetadataReader()
    normalized_directive_inputs = _normalize_directive_inputs(target_outputs, directive_inputs)
    raw_nodes = (
        *_compiler_nodes(
            raw_database,
            build_root=build_root,
            source_root=source_root,
            toolchain_root=toolchain,
        ),
        *_resource_nodes(
            build_root=build_root,
            source_root=source_root,
            toolchain_root=toolchain,
            reader=metadata_reader,
        ),
        *_link_nodes(
            build_root=build_root,
            source_root=source_root,
            toolchain_root=toolchain,
            reader=metadata_reader,
        ),
    )
    produced_relatives = frozenset(
        output.removeprefix("build/").casefold() for node in raw_nodes for output in node.outputs
    )
    normalized_nodes = tuple(
        _normalize_node(
            node,
            source_root=source_root,
            build_root=build_root,
            toolchain_root=toolchain,
            produced_relatives=produced_relatives,
        )
        for node in raw_nodes
    )
    normalized_nodes = (
        *normalized_nodes,
        *_coff_weak_alias_nodes(
            normalized_nodes,
            build_root=build_root,
            source_root=source_root,
            toolchain_root=toolchain,
            reader=metadata_reader,
        ),
    )
    nodes = _producer_nodes(
        normalized_nodes,
        target_outputs=target_outputs,
        directive_inputs=normalized_directive_inputs,
    )
    return ProducerGraphDocument(
        schema_version=3,
        toolchain_lock_digest=toolchain_lock_digest,
        path_profile_id=path_profile_id,
        extractor="cmake-makefiles-v1",
        nodes=tuple(sorted(nodes, key=lambda item: item.id.casefold())),
    )


__all__ = ["extract_cmake_makefiles_graph"]
