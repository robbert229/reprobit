"""ReproBit's in-run COFF weak-alias producer, its graph node and its CMake import."""

from __future__ import annotations

import json
import os
import re
import shutil
import struct
import subprocess
from pathlib import Path

import pytest

from reprobit.coff_weak_alias import (
    CoffWeakAlias,
    CoffWeakAliasDeclaration,
    CoffWeakAliasError,
    CoffWeakSearch,
    declare_coff_weak_alias,
    parse_alias_argument,
    read_coff_weak_alias,
    synthesize_coff_weak_alias,
)
from reprobit.model import Digest
from reprobit.producer_graph import (
    ProducerGraphDocument,
    ProducerGraphError,
    ProducerNode,
    ProducerRole,
    producer_graph_digest,
    read_producer_graph,
    write_producer_graph,
)
from reprobit.producer_graph_cmake import extract_cmake_makefiles_graph
from reprobit.strict_json import canonical_json

LRR_ALIAS = "??3@YAXPAX@Z=_ui_render_record_free"
# lrr's tools/coff_weak_external.py writes exactly these bytes for LRR_ALIAS.
LRR_OBJECT = bytes.fromhex(
    "4c01000000000000140000000300000000000000"  # header: i386, 0 sections, 3 symbols
    "000000000400000000000000000000000200"  # _ui_render_record_free: external
    "00000000"
    "1b000000"
    "00000000"
    "0000"
    "0000"
    "6901"  # ??3@YAXPAX@Z: weak, 1 aux
    "00000000"
    "01000000"
    "00000000000000000000"  # aux: default #0, NOLIBRARY
    "28000000"  # string table size
    "5f75695f72656e6465725f7265636f72645f6672656500"  # _ui_render_record_free
    "3f3f3340594158504158405a00"  # ??3@YAXPAX@Z
)
LRR_DIGEST = "5ea526af80116b76acbdb05326c0dd9b4de2417819aa8e184b85a0b0117af14f"


def _aliases(*values: str) -> tuple[CoffWeakAlias, ...]:
    return tuple(parse_alias_argument(value) for value in values)


def test_lrr_operator_delete_alias_has_its_exact_bytes() -> None:
    payload = synthesize_coff_weak_alias(_aliases(LRR_ALIAS))

    assert payload == LRR_OBJECT
    assert len(payload) == 114
    assert Digest.from_bytes(payload).value == LRR_DIGEST
    declaration = declare_coff_weak_alias(_aliases(LRR_ALIAS))
    assert declaration.output_digest.value == LRR_DIGEST
    assert declaration.output_size == 114
    assert declaration.payload() == LRR_OBJECT
    assert read_coff_weak_alias(LRR_OBJECT) == (
        CoffWeakSearch.NOLIBRARY,
        _aliases(LRR_ALIAS),
    )


def test_layout_shares_defaults_and_keeps_short_names_inline() -> None:
    aliases = _aliases("_a=_target", "_long_weak_name=_target", "_b=_other")
    payload = synthesize_coff_weak_alias(aliases)

    machine, sections, timestamp, pointer, count, optional, flags = struct.unpack_from(
        "<HHIIIHH", payload
    )
    assert (machine, sections, timestamp, pointer, optional, flags) == (0x14C, 0, 0, 20, 0, 0)
    assert count == 2 + 3 * 2  # two distinct defaults, then a symbol and aux per alias

    def symbol(index: int) -> tuple[bytes, int, int, int, int, int]:
        return struct.unpack_from("<8sIhHBB", payload, 20 + index * 18)

    assert symbol(0) == (b"_target\0", 0, 0, 0, 2, 0)
    assert symbol(1) == (b"_other\0\0", 0, 0, 0, 2, 0)
    assert symbol(2) == (b"_a\0\0\0\0\0\0", 0, 0, 0, 105, 1)
    assert struct.unpack_from("<II10s", payload, 20 + 3 * 18) == (0, 1, bytes(10))
    long_name = symbol(4)
    assert long_name[0] == struct.pack("<II", 0, 4) and long_name[4:] == (105, 1)
    assert struct.unpack_from("<II", payload, 20 + 7 * 18)[0] == 1  # _b defaults to _other
    strings = payload[20 + count * 18 :]
    assert strings == struct.pack("<I", 4 + 16) + b"_long_weak_name\0"
    assert read_coff_weak_alias(payload) == (CoffWeakSearch.NOLIBRARY, aliases)


@pytest.mark.parametrize(
    ("values", "message"),
    [
        (("_a=_b", "_a=_c"), "more than once"),
        (("_a=_b", "_b=_c"), "also defaults"),
        ((), "no aliases"),
    ],
)
def test_alias_sets_that_would_be_ambiguous_are_refused(
    values: tuple[str, ...], message: str
) -> None:
    with pytest.raises(CoffWeakAliasError, match=message):
        synthesize_coff_weak_alias(_aliases(*values))


@pytest.mark.parametrize(
    "value",
    ["_a", "=_b", "_a=", "_a=_b=_c", "_a b=_c", "_a=é", "_a=_a", "_a=\x01"],
)
def test_unparsable_alias_arguments_are_refused(value: str) -> None:
    with pytest.raises(CoffWeakAliasError):
        parse_alias_argument(value)


@pytest.mark.parametrize(
    ("search", "characteristic"),
    [(CoffWeakSearch.NOLIBRARY, 1), (CoffWeakSearch.LIBRARY, 2), (CoffWeakSearch.ALIAS, 3)],
)
def test_each_search_characteristic_is_written_into_every_auxiliary_record(
    search: CoffWeakSearch, characteristic: int
) -> None:
    aliases = _aliases("_a=_x", "_b=_x")
    payload = synthesize_coff_weak_alias(aliases, search=search)

    assert [struct.unpack_from("<I", payload, 20 + index * 18 + 4)[0] for index in (2, 4)] == [
        characteristic,
        characteristic,
    ]
    assert read_coff_weak_alias(payload) == (search, aliases)
    assert declare_coff_weak_alias(aliases, search=search).payload() == payload


def test_unknown_search_characteristics_are_refused() -> None:
    data = declare_coff_weak_alias(_aliases(LRR_ALIAS)).model_dump(mode="json")
    for search in ("anti-dependency", "4", ""):
        with pytest.raises(ValueError):
            CoffWeakAliasDeclaration.model_validate_json(json.dumps({**data, "search": search}))
    unknown = bytearray(LRR_OBJECT)
    struct.pack_into("<I", unknown, 20 + 2 * 18 + 4, 4)
    with pytest.raises(CoffWeakAliasError, match="search characteristic"):
        read_coff_weak_alias(bytes(unknown))
    mixed = bytearray(synthesize_coff_weak_alias(_aliases("_a=_x", "_b=_x")))
    struct.pack_into("<I", mixed, 20 + 4 * 18 + 4, 3)
    with pytest.raises(CoffWeakAliasError, match="search characteristic"):
        read_coff_weak_alias(bytes(mixed))


def test_declaration_pin_must_be_the_bytes_this_producer_writes() -> None:
    data = declare_coff_weak_alias(_aliases(LRR_ALIAS)).model_dump(mode="json")
    assert CoffWeakAliasDeclaration.model_validate_json(json.dumps(data)).output_size == 114
    with pytest.raises(ValueError, match="pin differs"):
        CoffWeakAliasDeclaration.model_validate_json(
            json.dumps({**data, "output_digest": {"algorithm": "sha256", "value": "0" * 64}})
        )
    with pytest.raises(ValueError, match="pin differs"):
        CoffWeakAliasDeclaration.model_validate_json(json.dumps({**data, "output_size": 115}))


@pytest.mark.parametrize(
    "mutate",
    [
        lambda data: struct.pack_into("<I", data, 4, 1),  # timestamp
        lambda data: struct.pack_into("<I", data, 20 + 8, 1),  # default symbol value
        lambda data: data.extend(b"\0"),  # trailing byte
        lambda data: struct.pack_into("<I", data, 20 + 3 * 18 - 4, 0x28),  # aux tail
    ],
)
def test_reader_accepts_only_the_canonical_layout(mutate: object) -> None:
    data = bytearray(LRR_OBJECT)
    mutate(data)  # type: ignore[operator]
    with pytest.raises(CoffWeakAliasError):
        read_coff_weak_alias(bytes(data))


def _weak_node(**overrides: object) -> ProducerNode:
    fields: dict[str, object] = {
        "id": "coff-weak-alias.app.0002",
        "role": ProducerRole.COFF_WEAK_ALIAS,
        "owner": "app",
        "arguments": (),
        "outputs": ("build/weak.obj",),
        "coff_weak_alias": declare_coff_weak_alias(_aliases(LRR_ALIAS)),
    }
    fields.update(overrides)
    return ProducerNode.model_validate(fields)


def _linker(*, depends_on: tuple[str, ...]) -> ProducerNode:
    return ProducerNode(
        id="linker.app.0001",
        role=ProducerRole.LINKER,
        owner="app",
        target_id="app",
        arguments=("/OUT:APP.EXE", "${BUILD}/main.obj", "${BUILD}/weak.obj"),
        inputs=("build/main.obj", "build/weak.obj"),
        outputs=("build/APP.EXE",),
        depends_on=depends_on,
    )


def _compiler() -> ProducerNode:
    return ProducerNode(
        id="compiler.app.0000",
        role=ProducerRole.COMPILER,
        owner="app",
        arguments=("/c", "/Fomain.obj", "${SOURCE}/main.c"),
        inputs=("source/main.c",),
        outputs=("build/main.obj",),
    )


def test_graph_node_carries_the_whole_declaration_and_round_trips(tmp_path: Path) -> None:
    graph = ProducerGraphDocument(
        schema_version=3,
        toolchain_lock_digest=Digest(value="1" * 64),
        path_profile_id="stable",
        extractor="cmake-makefiles-v1",
        nodes=(
            _weak_node(),
            _compiler(),
            _linker(depends_on=("coff-weak-alias.app.0002", "compiler.app.0000")),
        ),
    )
    destination = tmp_path / "producer-graph.json"
    write_producer_graph(destination, graph)
    assert read_producer_graph(destination) == graph
    document = json.loads(destination.read_text(encoding="utf-8"))
    weak = next(node for node in document["nodes"] if node["role"] == "coff-weak-alias")
    assert weak["arguments"] == []
    assert weak["coff_weak_alias"]["output_digest"]["value"] == LRR_DIGEST
    assert weak["coff_weak_alias"]["aliases"] == [
        {"weak": "??3@YAXPAX@Z", "default": "_ui_render_record_free"}
    ]
    # Nodes without a declaration serialize as before, so existing graph
    # digests do not move.
    assert "coff_weak_alias" not in canonical_json(_compiler()).decode()


def test_linker_needs_a_dependency_on_the_weak_alias_node() -> None:
    with pytest.raises(ValueError, match="without a direct dependency"):
        ProducerGraphDocument(
            schema_version=3,
            toolchain_lock_digest=Digest(value="1" * 64),
            path_profile_id="stable",
            extractor="cmake-makefiles-v1",
            nodes=(_weak_node(), _compiler(), _linker(depends_on=("compiler.app.0000",))),
        )
    with pytest.raises(ValueError, match="unproduced build input"):
        ProducerGraphDocument(
            schema_version=3,
            toolchain_lock_digest=Digest(value="1" * 64),
            path_profile_id="stable",
            extractor="cmake-makefiles-v1",
            nodes=(_compiler(), _linker(depends_on=("compiler.app.0000",))),
        )


@pytest.mark.parametrize(
    ("overrides", "message"),
    [
        ({"coff_weak_alias": None}, "require their alias declaration"),
        ({"arguments": ("/x",)}, "take no argv"),
        ({"inputs": ("source/main.c",)}, "take no argv"),
        ({"depends_on": ("compiler.app.0000",)}, "take no argv"),
        ({"outputs": ("build/weak.lib",)}, "exactly one .obj"),
        ({"outputs": ("build/a.obj", "build/b.obj")}, "exactly one .obj"),
        ({"target_id": "app"}, "terminal linker"),
    ],
)
def test_weak_alias_node_shape_is_closed(overrides: dict[str, object], message: str) -> None:
    with pytest.raises(ValueError, match=message):
        _weak_node(**overrides)


def test_only_weak_alias_nodes_carry_a_declaration() -> None:
    with pytest.raises(ValueError, match="only coff-weak-alias nodes"):
        ProducerNode(
            id="compiler.app.0000",
            role=ProducerRole.COMPILER,
            owner="app",
            arguments=("/c", "${SOURCE}/main.c"),
            inputs=("source/main.c",),
            outputs=("build/main.obj",),
            coff_weak_alias=declare_coff_weak_alias(_aliases(LRR_ALIAS)),
        )
    with pytest.raises(ValueError, match="require argv"):
        ProducerNode(
            id="compiler.app.0000",
            role=ProducerRole.COMPILER,
            owner="app",
            arguments=(),
            inputs=("source/main.c",),
            outputs=("build/main.obj",),
        )


_PROGRESS_ECHO = (
    '\t@$(CMAKE_COMMAND) -E cmake_echo_color "--switch=$(COLOR)" --blue --bold '
    "--progress-dir={build}/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "
    '"Generating weak_operator_delete.obj"'
)


def _weak_alias_project(
    tmp_path: Path,
    *,
    command: str | None = None,
    extra_recipe: tuple[str, ...] = (),
) -> tuple[Path, Path, Path]:
    """A configured Unix Makefiles tree shaped like lrr's matching build."""

    source = tmp_path / "effective"
    build = tmp_path / "configured"
    toolchain = tmp_path / "toolchain"
    for path in (
        source / "src/main.c",
        toolchain / "wine/x86/cl",
        toolchain / "wine/x86/link",
    ):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("fixture\n", encoding="utf-8")
    script = source / "tools/coff_weak_external.py"
    script.parent.mkdir(parents=True)
    marker = tmp_path / "script-ran"
    # Were the import ever to run the project's script, this marker would appear.
    script.write_text(
        f"from pathlib import Path\nPath({str(marker)!r}).write_text('ran')\n", encoding="utf-8"
    )
    object_output = "CMakeFiles/program.dir/src/main.c.obj"
    build.mkdir()
    (build / "compile_commands.json").write_text(
        json.dumps(
            [
                {
                    "directory": str(build),
                    "file": str(source / "src/main.c"),
                    "command": " ".join(
                        (
                            f"{toolchain.as_posix()}/wine/x86/cl",
                            "/nologo",
                            f"/Fo{object_output}",
                            f"/Fd{object_output}.pdb",
                            "-c",
                            f"{source.as_posix()}/src/main.c",
                        )
                    ),
                }
            ]
        ),
        encoding="utf-8",
    )
    program = build / "CMakeFiles/program.dir"
    program.mkdir(parents=True)
    weak = build / "weak_operator_delete.obj"
    recipe = command or (f"\t/usr/bin/python3 {script.as_posix()} {weak.as_posix()} {LRR_ALIAS}")
    (program / "build.make").write_text(
        "\n".join(
            (
                "# CMAKE generated file: DO NOT EDIT!",
                f"{object_output}: CMakeFiles/program.dir/flags.make",
                f"{object_output}: {source.as_posix()}/src/main.c",
                f"\t{toolchain.as_posix()}/wine/x86/cl /nologo -c {source.as_posix()}/src/main.c",
                "",
                f"weak_operator_delete.obj: {script.as_posix()}",
                _PROGRESS_ECHO.format(build=build.as_posix()),
                recipe,
                *extra_recipe,
                "",
                "program: weak_operator_delete.obj",
                "",
            )
        ),
        encoding="utf-8",
    )
    (program / "link.txt").write_text(
        f"{toolchain.as_posix()}/wine/x86/link /nologo {object_output} "
        "weak_operator_delete.obj kernel32.lib /out:LegoRR.exe",
        encoding="utf-8",
    )
    return source, build, toolchain


def _extract(source: Path, build: Path, toolchain: Path) -> ProducerGraphDocument:
    return extract_cmake_makefiles_graph(
        configured_build_root=build,
        effective_source_root=source,
        toolchain_root=toolchain,
        toolchain_lock_digest=Digest(value="4" * 64),
        path_profile_id="stable",
        target_outputs={"program": "LegoRR.exe"},
    )


def test_import_maps_lrrs_custom_command_to_the_weak_alias_producer(tmp_path: Path) -> None:
    source, build, toolchain = _weak_alias_project(tmp_path)
    graph = _extract(source, build, toolchain)

    weak = [node for node in graph.nodes if node.role is ProducerRole.COFF_WEAK_ALIAS]
    assert len(weak) == 1
    (node,) = weak
    assert node.id == "coff-weak-alias.program.0002"
    assert node.owner == "program"
    assert node.arguments == () and node.inputs == ()
    assert node.outputs == ("build/weak_operator_delete.obj",)
    assert node.coff_weak_alias == declare_coff_weak_alias(_aliases(LRR_ALIAS))
    linker = next(item for item in graph.nodes if item.role is ProducerRole.LINKER)
    assert "build/weak_operator_delete.obj" in linker.inputs
    assert "${BUILD}/weak_operator_delete.obj" in linker.arguments
    assert node.id in linker.depends_on
    assert not (tmp_path / "script-ran").exists()
    destination = tmp_path / "graph.json"
    write_producer_graph(destination, graph)
    assert producer_graph_digest(read_producer_graph(destination)) == producer_graph_digest(graph)


def test_import_reads_a_declared_search_characteristic(tmp_path: Path) -> None:
    script = (tmp_path / "effective/tools/coff_weak_external.py").as_posix()
    weak = (tmp_path / "configured/weak_operator_delete.obj").as_posix()
    source, build, toolchain = _weak_alias_project(
        tmp_path, command=f"\t/usr/bin/python3 {script} --search=alias {weak} {LRR_ALIAS}"
    )

    graph = _extract(source, build, toolchain)

    (node,) = (item for item in graph.nodes if item.role is ProducerRole.COFF_WEAK_ALIAS)
    assert node.coff_weak_alias == declare_coff_weak_alias(
        _aliases(LRR_ALIAS), search=CoffWeakSearch.ALIAS
    )


def test_import_accepts_the_projects_own_output_when_it_is_the_same(tmp_path: Path) -> None:
    source, build, toolchain = _weak_alias_project(tmp_path)
    (build / "weak_operator_delete.obj").write_bytes(LRR_OBJECT)

    graph = _extract(source, build, toolchain)

    assert any(node.role is ProducerRole.COFF_WEAK_ALIAS for node in graph.nodes)


def test_import_refuses_a_project_output_that_differs_from_reprobits(tmp_path: Path) -> None:
    source, build, toolchain = _weak_alias_project(tmp_path)
    (build / "weak_operator_delete.obj").write_bytes(
        synthesize_coff_weak_alias(_aliases("??3@YAXPAX@Z=_free"))
    )

    with pytest.raises(ProducerGraphError, match=r"wrote different bytes.*_free"):
        _extract(source, build, toolchain)


@pytest.mark.parametrize(
    ("command", "extra", "message"),
    [
        (
            "\t/usr/bin/python3 {source}/tools/other_tool.py {build}/weak_operator_delete.obj "
            + LRR_ALIAS,
            (),
            "unknown script 'source/tools/other_tool.py'",
        ),
        (
            "\t/usr/bin/python3 {source}/tools/coff_weak_external.py "
            "{build}/weak_operator_delete.obj ??3@YAXPAX@Z",
            (),
            "invalid alias set.*not one WEAK=DEFAULT",
        ),
        (
            "\t/usr/bin/python3 {source}/tools/coff_weak_external.py "
            "{build}/weak_operator_delete.obj _a=_b _a=_c",
            (),
            "invalid alias set.*more than once",
        ),
        (
            "\t/usr/bin/python3 {source}/tools/coff_weak_external.py "
            "{build}/weak_operator_delete.obj _a=_a",
            (),
            "invalid alias set.*names itself",
        ),
        (
            "\t/usr/bin/python3 {source}/tools/coff_weak_external.py "
            "{build}/other.obj " + LRR_ALIAS,
            (),
            "not its rule target",
        ),
        (
            "\t/usr/bin/python3 {source}/tools/coff_weak_external.py --search=lazy "
            "{build}/weak_operator_delete.obj " + LRR_ALIAS,
            (),
            "unknown search characteristic",
        ),
        (
            "\t/usr/bin/perl {source}/tools/coff_weak_external.py "
            "{build}/weak_operator_delete.obj " + LRR_ALIAS,
            (),
            "not an importable command",
        ),
        (
            "\t/usr/bin/python3 {source}/tools/coff_weak_external.py "
            "{build}/weak_operator_delete.obj " + LRR_ALIAS,
            ("\ttouch {build}/weak_operator_delete.obj",),
            "must be one command, found 2",
        ),
        (
            "\t/usr/bin/python3 {source}/tools/coff_weak_external.py "
            "{build}/weak_operator_delete.obj $(ALIASES)",
            (),
            "make or shell expansion",
        ),
    ],
)
def test_import_refuses_any_other_custom_command(
    tmp_path: Path, command: str, extra: tuple[str, ...], message: str
) -> None:
    source = (tmp_path / "effective").as_posix()
    build = (tmp_path / "configured").as_posix()
    source_root, build_root, toolchain = _weak_alias_project(
        tmp_path,
        command=command.format(source=source, build=build),
        extra_recipe=tuple(line.format(source=source, build=build) for line in extra),
    )

    with pytest.raises(ProducerGraphError, match=message):
        _extract(source_root, build_root, toolchain)
    assert not (tmp_path / "script-ran").exists()


def test_an_object_without_a_custom_command_still_lacks_ancestry(tmp_path: Path) -> None:
    source, build, toolchain = _weak_alias_project(tmp_path)
    makefile = build / "CMakeFiles/program.dir/build.make"
    text = makefile.read_text(encoding="utf-8")
    makefile.write_text(text.replace("weak_operator_delete.obj:", "unrelated.obj:"), "utf-8")

    with pytest.raises(ValueError, match="unproduced build input"):
        _extract(source, build, toolchain)


def _installed_msvc50_root() -> Path | None:
    configured = os.environ.get("REPROBIT_MSVC_5_0_RTM_ROOT")
    return Path(configured) if configured else None


@pytest.mark.msvc50
@pytest.mark.skipif(shutil.which("wine") is None, reason="requires Wine")
def test_link_50_resolves_weak_externals_by_characteristic_and_link_order(
    tmp_path: Path,
) -> None:
    """What a real LINK 5.0 does with each search characteristic.

    ``use.obj`` calls ``alias_fn``; ``tgt.obj`` defines ``target_fn``; the weak
    object makes ``_alias_fn`` default to ``_target_fn``; ``decoy.lib`` holds a
    member that defines ``alias_fn`` (and ``decoy_marker``); ``code.lib`` holds
    ``use.obj``, so its reference arrives from a library member, as lrr's do.
    """

    root = _installed_msvc50_root()
    if root is None:
        pytest.skip("requires an authenticated installation in REPROBIT_MSVC_5_0_RTM_ROOT")
    sources = {
        "use.c": "int alias_fn(int);\nint entry(void) { return alias_fn(1); }\n",
        "tgt.c": "int target_fn(int x) { return x + 41; }\n",
        "decoy.c": "int decoy_marker;\nint alias_fn(int x) { return x + decoy_marker; }\n",
    }
    for name, text in sources.items():
        (tmp_path / name).write_text(text, encoding="ascii")
    for search in CoffWeakSearch:
        (tmp_path / f"weak_{search.value}.obj").write_bytes(
            synthesize_coff_weak_alias(_aliases("_alias_fn=_target_fn"), search=search)
        )
    environment = dict(
        os.environ,
        WINEPREFIX=str(tmp_path / "prefix"),
        WINEDEBUG="-all",
        WINEDLLOVERRIDES="mscoree,mshtml=",
    )

    def run(*argv: object) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            ["wine", *map(str, argv)],
            cwd=tmp_path,
            env=environment,
            capture_output=True,
            text=True,
            timeout=300,
            check=False,
        )

    for unit in sources:
        compiled = run(root / "bin" / "cl.exe", "/nologo", "/c", "/O2", unit)
        assert compiled.returncode == 0, compiled.stdout + compiled.stderr
    for library, member in (("decoy.lib", "decoy.obj"), ("code.lib", "use.obj")):
        archived = run(root / "bin" / "lib.exe", "/nologo", f"/out:{library}", member)
        assert archived.returncode == 0, archived.stdout + archived.stderr
    links = 0

    def link(*inputs: str) -> tuple[int, str, str]:
        nonlocal links
        links += 1
        name = f"probe{links}"
        linked = run(
            root / "bin" / "link.exe",
            "/NOLOGO",
            "/NODEFAULTLIB",
            "/ENTRY:entry",
            "/SUBSYSTEM:CONSOLE",
            *inputs,
            f"/MAP:{name}.map",
            f"/OUT:{name}.exe",
        )
        listing = tmp_path / f"{name}.map"
        text = listing.read_text(encoding="latin-1") if listing.is_file() else ""
        return linked.returncode, linked.stdout + linked.stderr, text

    def owner(listing: str, symbol: str) -> tuple[str, str] | None:
        match = re.search(
            rf"^\s*\S+\s+{re.escape(symbol)}\s+([0-9a-f]{{8}})\s+f?\s*(\S+)\s*$",
            listing,
            re.M,
        )
        return (match.group(1), match.group(2)) if match else None

    def resolves_to_default(*inputs: str) -> bool:
        status, output, listing = link(*inputs)
        assert status == 0, output
        if owner(listing, "_alias_fn") == owner(listing, "_target_fn") is not None:
            assert owner(listing, "_decoy_marker") is None
            return True
        assert owner(listing, "_alias_fn") is not None
        assert owner(listing, "_alias_fn")[1] == "decoy:decoy.obj"  # type: ignore[index]
        return False

    # ALIAS: the default, whether the reference is a plain object or a library member.
    assert resolves_to_default("use.obj", "tgt.obj", "weak_alias.obj", "decoy.lib")
    assert resolves_to_default(
        "/INCLUDE:_entry", "tgt.obj", "weak_alias.obj", "code.lib", "decoy.lib"
    )
    # NOLIBRARY, lrr's arrangement: the reference comes from a library member.
    assert resolves_to_default(
        "/INCLUDE:_entry", "tgt.obj", "weak_nolibrary.obj", "code.lib", "decoy.lib"
    )
    # NOLIBRARY with the reference in a plain object: LINK searches the libraries...
    assert not resolves_to_default("use.obj", "tgt.obj", "weak_nolibrary.obj", "decoy.lib")
    # ...and, finding no definition, leaves it unresolved rather than use the default.
    status, output, _listing = link("use.obj", "tgt.obj", "weak_nolibrary.obj")
    assert status != 0 and "LNK2001" in output and "_alias_fn" in output
    # LIBRARY in lrr's arrangement pulls the library member.
    assert not resolves_to_default(
        "/INCLUDE:_entry", "tgt.obj", "weak_library.obj", "code.lib", "decoy.lib"
    )


def _weak_alias_audit_issues(
    *,
    payload: bytes = LRR_OBJECT,
    producer_step: str = "coff-weak-alias.app.0002",
    cold: bool = True,
    parent_path: str = "reprobit/producer-graph.json",
    graph_declares: bool = True,
) -> set[str]:
    """Run only the auditor's weak-alias check over one synthetic run."""

    from types import SimpleNamespace
    from typing import cast

    from reprobit.evidence_audit import EvidenceAuditor
    from reprobit.execution import BuildExecutionReceipt, FileReceipt
    from reprobit.model import Artifact, ArtifactKind, ArtifactOrigin, ProvenanceKind
    from reprobit.model import ProvenanceNode as Node
    from reprobit.schema import ProjectBundle

    graph_artifact = Artifact(
        id="artifact.graph",
        kind=ArtifactKind.SOURCE,
        logical_path=parent_path,
        digest=Digest.from_bytes(b"graph"),
        size=5,
        origin=ArtifactOrigin.FRESH_SEED,
        receipt_path="/run/project/reprobit/producer-graph.json",
    )
    weak_artifact = Artifact(
        id="artifact.weak",
        kind=ArtifactKind.OBJECT,
        logical_path="build/weak.obj",
        digest=Digest.from_bytes(payload),
        size=len(payload),
        origin=ArtifactOrigin.FRESH_SEED,
        inputs=(graph_artifact.id,),
        receipt_path="/run/build/weak.obj",
    )
    nodes = {
        "provenance.graph": Node(
            id="provenance.graph",
            kind=ProvenanceKind.SOURCE,
            operation="sealed_source",
            origin=ArtifactOrigin.FRESH_SEED,
            artifact_id=graph_artifact.id,
        ),
        "provenance.weak": Node(
            id="provenance.weak",
            kind=ProvenanceKind.PRODUCER,
            operation="coff_weak_alias",
            origin=ArtifactOrigin.FRESH_SEED,
            parents=("provenance.graph",),
            artifact_id=weak_artifact.id,
        ),
    }
    build = BuildExecutionReceipt(
        cold=cold,
        inputs=(),
        outputs=(
            FileReceipt(
                Path("/run/build/weak.obj"),
                Digest.from_bytes(payload),
                len(payload),
                fresh=True,
                producer_step=producer_step,
            ),
        ),
        steps=(),
    )
    graph = SimpleNamespace(nodes=(_weak_node(),) if graph_declares else ())
    bundle = SimpleNamespace(
        producer_graph=graph,
        spec=SimpleNamespace(layout=SimpleNamespace(producer_graph="reprobit/producer-graph.json")),
    )
    issues: set[str] = set()
    EvidenceAuditor._validate_coff_weak_alias_objects(
        cast(ProjectBundle, bundle),
        build,
        {item.id: item for item in (graph_artifact, weak_artifact)},
        nodes,
        lambda _claim, code, _message: issues.add(code),
    )
    return issues


def test_auditor_admits_the_declared_bytes_as_a_cold_output_of_their_node() -> None:
    assert _weak_alias_audit_issues() == set()


@pytest.mark.parametrize(
    ("overrides", "code"),
    [
        ({"payload": synthesize_coff_weak_alias(_aliases("_a=_b"))}, "weak-alias-content"),
        ({"graph_declares": False}, "weak-alias-content"),
        ({"producer_step": "compiler.app.0000"}, "weak-alias-receipt"),
        ({"cold": False}, "weak-alias-receipt"),
        ({"parent_path": "src/other.json"}, "weak-alias-provenance"),
    ],
)
def test_auditor_refuses_weak_alias_objects_it_cannot_re_derive(
    overrides: dict[str, object], code: str
) -> None:
    assert code in _weak_alias_audit_issues(**overrides)  # type: ignore[arg-type]
