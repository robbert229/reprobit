"""The MSVC 5.0 LINK runtime staged on the toolchain's own MSVCRT 5.00."""

from __future__ import annotations

import hashlib
import os
import shutil
import struct
import subprocess
from pathlib import Path
from types import MappingProxyType, SimpleNamespace
from typing import cast

import pytest

from reprobit import classic_incremental_keys, classic_runtime_preparation
from reprobit import msvc50_link_runtime as link_runtime
from reprobit.classic_project import ClassicProjectError
from reprobit.msvc50_authorities import (
    MSVC50_FILE_AUTHORITIES,
    MSVC50_NATIVE_CRT_LINK_AUTHORITIES,
    Msvc50FileAuthority,
)
from reprobit.msvc50_link_runtime import (
    STAGED_DIRECTORY,
    STAGED_LINKER,
    STAGED_SOURCES,
    Msvc50LinkRuntimeError,
    authenticated_link_runtime,
    derive_link_runtime,
    link_runtime_material,
    patch_crt_import,
    stage_link_runtime,
)
from reprobit.producer_graph import ProducerRole
from reprobit.schema import ProjectBundle

_SECTION_RVA = 0x1000
_SECTION_OFFSET = 0x200
_SECTION_SIZE = 0x400


def _pe_with_imports(dll_names: tuple[bytes, ...], *, extra: bytes = b"") -> bytes:
    """Build a minimal PE32 image whose import directory names ``dll_names``."""

    section = bytearray(_SECTION_SIZE)
    names_at = 0x100
    for index, name in enumerate(dll_names):
        name_rva = _SECTION_RVA + names_at
        struct.pack_into(
            "<IIIII",
            section,
            index * 20,
            _SECTION_RVA + 0x300,  # OriginalFirstThunk (unused by the patcher)
            0,
            0,
            name_rva,
            _SECTION_RVA + 0x380,
        )
        section[names_at : names_at + len(name) + 1] = name + b"\0"
        names_at += len(name) + 1
    section[0x280 : 0x280 + len(extra)] = extra

    image = bytearray(_SECTION_OFFSET)
    image[0:2] = b"MZ"
    struct.pack_into("<I", image, 0x3C, 0x40)
    image[0x40:0x44] = b"PE\0\0"
    struct.pack_into("<HHIIIHH", image, 0x44, 0x014C, 1, 0, 0, 0, 224, 0x0102)
    optional = 0x58
    struct.pack_into("<H", image, optional, 0x010B)
    struct.pack_into("<I", image, optional + 92, 16)
    struct.pack_into("<II", image, optional + 96 + 8, _SECTION_RVA, 20 * (len(dll_names) + 1))
    table = optional + 224
    struct.pack_into(
        "<8sIIIIIIHHI",
        image,
        table,
        b".idata",
        _SECTION_SIZE,
        _SECTION_RVA,
        _SECTION_SIZE,
        _SECTION_OFFSET,
        0,
        0,
        0,
        0,
        0xC0000040,
    )
    return bytes(image) + bytes(section)


def test_patch_renames_the_one_crt_import_in_place() -> None:
    image = _pe_with_imports((b"KERNEL32.dll", b"MSVCRT.dll"))
    patched = patch_crt_import(image)

    assert len(patched) == len(image)
    assert patched.count(b"MSVCR5.dll\0") == 1
    assert b"MSVCRT.dll" not in patched
    differing = [index for index, (a, b) in enumerate(zip(image, patched, strict=True)) if a != b]
    assert len(differing) == 1  # only "T" -> "5"
    assert [name for name, _ in link_runtime._import_name_offsets(patched)] == [
        b"KERNEL32.dll",
        b"MSVCR5.dll",
    ]


@pytest.mark.parametrize("spelling", (b"msvcrt.dll", b"MSVCRT.DLL", b"MsVcRt.Dll"))
def test_patch_matches_the_crt_name_case_insensitively(spelling: bytes) -> None:
    patched = patch_crt_import(_pe_with_imports((spelling, b"KERNEL32.dll")))

    assert [name for name, _ in link_runtime._import_name_offsets(patched)] == [
        b"MSVCR5.dll",
        b"KERNEL32.dll",
    ]


def test_patch_refuses_an_image_without_the_crt_import() -> None:
    with pytest.raises(Msvc50LinkRuntimeError, match="found 0"):
        patch_crt_import(_pe_with_imports((b"KERNEL32.dll",)))


def test_patch_refuses_a_second_occurrence_of_the_crt_name() -> None:
    image = _pe_with_imports((b"MSVCRT.dll", b"KERNEL32.dll"), extra=b"msvcrt.dll\0")

    with pytest.raises(Msvc50LinkRuntimeError, match="found 2"):
        patch_crt_import(image)


def test_patch_refuses_two_crt_import_descriptors() -> None:
    with pytest.raises(Msvc50LinkRuntimeError, match="found 2"):
        patch_crt_import(_pe_with_imports((b"MSVCRT.dll", b"msvcrt.dll")))


def test_patch_refuses_a_crt_name_that_is_not_an_import() -> None:
    image = _pe_with_imports((b"KERNEL32.dll",), extra=b"MSVCRT.dll\0")

    with pytest.raises(Msvc50LinkRuntimeError, match="not exactly one import descriptor"):
        patch_crt_import(image)


def test_patch_refuses_a_non_pe_payload() -> None:
    with pytest.raises(Msvc50LinkRuntimeError, match="not a readable PE32"):
        patch_crt_import(b"MZ" + b"\0" * 62 + b"MSVCRT.dll\0")


def _synthetic_toolchain() -> dict[str, bytes]:
    return {
        "bin/link.exe": _pe_with_imports((b"MSDIS100.DLL", b"mspdb50.dll", b"MSVCRT.dll")),
        "bin/mspdb50.dll": _pe_with_imports((b"MSVCRT.dll", b"KERNEL32.dll")),
        "bin/msdis100.dll": _pe_with_imports((b"MSVCP50.dll", b"MSVCRT.dll")),
        "bin/msvcp50.dll": _pe_with_imports((b"MSVCRT.dll", b"KERNEL32.dll")),
        "bin/msvcrt.dll": b"Microsoft C runtime 5.00 stand-in",
    }


def _authority(payload: bytes) -> Msvc50FileAuthority:
    return Msvc50FileAuthority(len(payload), hashlib.sha256(payload).hexdigest())


def _reviewed_outputs(files: dict[str, bytes]) -> dict[str, Msvc50FileAuthority]:
    return {
        name: _authority(payload)
        for name, payload in derive_link_runtime(files.__getitem__).items()
    }


@pytest.fixture
def synthetic_profile(monkeypatch: pytest.MonkeyPatch) -> dict[str, bytes]:
    """Review a synthetic toolchain as profile ``synthetic`` for the staging code."""

    files = _synthetic_toolchain()
    monkeypatch.setattr(
        link_runtime,
        "MSVC50_FILE_AUTHORITIES",
        {"synthetic": {path: _authority(payload) for path, payload in files.items()}},
    )
    monkeypatch.setattr(
        link_runtime,
        "MSVC50_NATIVE_CRT_LINK_AUTHORITIES",
        {"synthetic": _reviewed_outputs(files)},
    )
    return files


def test_derivation_renames_imports_and_copies_the_runtime() -> None:
    files = _synthetic_toolchain()
    staged = derive_link_runtime(files.__getitem__)

    assert (
        set(staged)
        == set(STAGED_SOURCES)
        == {
            "link.exe",
            "mspdb50.dll",
            "msdis100.dll",
            "msvcp50.dll",
            "MSVCR5.dll",
        }
    )
    assert staged["MSVCR5.dll"] == files["bin/msvcrt.dll"]
    for name in ("link.exe", "mspdb50.dll", "msdis100.dll", "msvcp50.dll"):
        assert staged[name] == patch_crt_import(files[f"bin/{name}"])
        assert len(staged[name]) == len(files[f"bin/{name}"])


def test_authenticated_derivation_refuses_unreviewed_inputs(
    synthetic_profile: dict[str, bytes],
) -> None:
    tampered = dict(synthetic_profile, **{"bin/msvcrt.dll": b"Wine's builtin msvcrt"})

    with pytest.raises(Msvc50LinkRuntimeError, match=r"bin/msvcrt\.dll differs"):
        authenticated_link_runtime("synthetic", tampered.__getitem__)
    with pytest.raises(Msvc50LinkRuntimeError, match="no reviewed"):
        authenticated_link_runtime("msvc_4_2", synthetic_profile.__getitem__)


def test_authenticated_derivation_refuses_an_unreviewed_output(
    synthetic_profile: dict[str, bytes],
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    outputs = _reviewed_outputs(synthetic_profile)
    outputs["link.exe"] = _authority(synthetic_profile["bin/link.exe"])  # unpatched bytes
    monkeypatch.setattr(link_runtime, "MSVC50_NATIVE_CRT_LINK_AUTHORITIES", {"synthetic": outputs})

    with pytest.raises(Msvc50LinkRuntimeError, match=r"staged link\.exe differs"):
        authenticated_link_runtime("synthetic", synthetic_profile.__getitem__)


def _projected_toolchain(root: Path, files: dict[str, bytes]) -> Path:
    for relative, payload in files.items():
        path = root.joinpath(*relative.split("/"))
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(payload)
    return root


def test_staging_is_deterministic_and_verified(
    tmp_path: Path,
    synthetic_profile: dict[str, bytes],
) -> None:
    first_root = _projected_toolchain(tmp_path / "first", synthetic_profile)
    second_root = _projected_toolchain(tmp_path / "second", synthetic_profile)
    before = {path: path.read_bytes() for path in first_root.rglob("*") if path.is_file()}

    first = stage_link_runtime(first_root, "synthetic")
    second = stage_link_runtime(second_root, "synthetic")

    expected = _reviewed_outputs(synthetic_profile)
    assert [path.name for path in first] == sorted(expected, key=str.casefold)
    assert [path.read_bytes() for path in first] == [path.read_bytes() for path in second]
    for path in first:
        assert path.parent == first_root.resolve() / STAGED_DIRECTORY
        assert _authority(path.read_bytes()) == expected[path.name]
    # The toolchain files the staging read are untouched.
    for path, payload in before.items():
        assert path.read_bytes() == payload
    # A second staging into the same projection is refused, never merged.
    with pytest.raises(Msvc50LinkRuntimeError, match="already exists"):
        stage_link_runtime(first_root, "synthetic")


def test_staging_refuses_a_projection_without_a_derivation_input(
    tmp_path: Path,
    synthetic_profile: dict[str, bytes],
) -> None:
    files = dict(synthetic_profile)
    del files["bin/msdis100.dll"]
    root = _projected_toolchain(tmp_path / "toolchain", files)

    with pytest.raises(Msvc50LinkRuntimeError, match=r"bin/msdis100\.dll is not readable"):
        stage_link_runtime(root, "synthetic")
    assert not (root / STAGED_DIRECTORY).exists()


def _bundle(profile: str) -> ProjectBundle:
    return cast(
        ProjectBundle,
        SimpleNamespace(spec=SimpleNamespace(toolchain=SimpleNamespace(profile=profile))),
    )


_ROLE_RELATIVES = MappingProxyType(
    {
        ProducerRole.COMPILER: "bin/cl.exe",
        ProducerRole.RESOURCE: "bin/rc.exe",
        ProducerRole.LIBRARIAN: "bin/lib.exe",
        ProducerRole.LINKER: "bin/link.exe",
    }
)


def test_classic_runs_link_from_the_staged_copy(
    tmp_path: Path,
    synthetic_profile: dict[str, bytes],
) -> None:
    root = _projected_toolchain(tmp_path / "toolchain", synthetic_profile)

    relatives, staged = classic_runtime_preparation._stage_profile_linker(
        _bundle("synthetic"), root, _ROLE_RELATIVES
    )

    assert relatives[ProducerRole.LINKER] == STAGED_LINKER == f"{STAGED_DIRECTORY}/link.exe"
    # cl, rc and lib keep running from the toolchain itself.
    for role in (ProducerRole.COMPILER, ProducerRole.RESOURCE, ProducerRole.LIBRARIAN):
        assert relatives[role] == _ROLE_RELATIVES[role]
    linker = root.joinpath(*STAGED_LINKER.split("/"))
    assert linker.resolve() in staged
    assert linker.read_bytes() == patch_crt_import(synthetic_profile["bin/link.exe"])


def test_classic_leaves_other_profiles_link_alone(tmp_path: Path) -> None:
    relatives, staged = classic_runtime_preparation._stage_profile_linker(
        _bundle("msvc_4_2"), tmp_path, _ROLE_RELATIVES
    )

    assert relatives is _ROLE_RELATIVES
    assert staged == ()
    assert not (tmp_path / STAGED_DIRECTORY).exists()


def test_classic_staging_failure_is_a_project_error(
    tmp_path: Path,
    synthetic_profile: dict[str, bytes],
) -> None:
    root = _projected_toolchain(
        tmp_path / "toolchain", dict(synthetic_profile, **{"bin/link.exe": b"not LINK"})
    )

    with pytest.raises(ClassicProjectError, match="native-CRT LINK runtime"):
        classic_runtime_preparation._stage_profile_linker(
            _bundle("synthetic"), root, _ROLE_RELATIVES
        )


def test_only_link_roles_bind_the_staged_runtime_in_cache_keys() -> None:
    assert {"linker", "analysis-link"} == classic_incremental_keys._LINK_RUNTIME_ROLES
    material = link_runtime_material("msvc_5_0_rtm")
    assert isinstance(material, dict)
    assert material["scheme"] == "msvc50-native-crt-link-v1"
    assert material["linker"] == STAGED_LINKER
    assert link_runtime_material("msvc_4_2") is None


@pytest.mark.parametrize("profile_identifier", sorted(MSVC50_NATIVE_CRT_LINK_AUTHORITIES))
def test_reviewed_derivations_are_consistent_with_their_inputs(profile_identifier: str) -> None:
    inputs = MSVC50_FILE_AUTHORITIES[profile_identifier]
    outputs = MSVC50_NATIVE_CRT_LINK_AUTHORITIES[profile_identifier]

    assert set(outputs) == set(STAGED_SOURCES)
    for name, (source, patched) in STAGED_SOURCES.items():
        assert outputs[name].size == inputs[source].size
        if patched:
            assert outputs[name].sha256 != inputs[source].sha256
        else:
            assert outputs[name] == inputs[source]


def _installed_roots() -> list[tuple[str, Path]]:
    roots = []
    for profile_identifier in sorted(MSVC50_NATIVE_CRT_LINK_AUTHORITIES):
        variable = f"REPROBIT_{profile_identifier.upper()}_ROOT"
        configured = os.environ.get(variable)
        if configured:
            roots.append((profile_identifier, Path(configured)))
    return roots


@pytest.mark.msvc50
@pytest.mark.parametrize(("profile_identifier", "root"), _installed_roots() or [(None, None)])
def test_installed_toolchain_derives_its_reviewed_link_runtime(
    tmp_path: Path,
    profile_identifier: str | None,
    root: Path | None,
) -> None:
    if profile_identifier is None or root is None:
        pytest.skip("requires an authenticated installation in REPROBIT_MSVC_5_0_*_ROOT")
    projection = tmp_path / "toolchain"
    for _name, (source, _patched) in STAGED_SOURCES.items():
        target = projection.joinpath(*source.split("/"))
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(root.joinpath(*source.split("/")).read_bytes())

    staged = stage_link_runtime(projection, profile_identifier)

    assert len(staged) == len(STAGED_SOURCES)


# Every d3drm.lib export with its stdcall argument size.  Fewer than eight
# equal keys sort identically under both runtimes (Microsoft's shortsort and
# Wine's small_sort are the same selection sort); from there on Microsoft's
# qsort moves its pivot to the front and Wine's does not.
_D3DRM_IMPORTS = (
    ("Direct3DRMCreate", 4),
    ("D3DRMVectorRandom", 4),
    ("D3DRMVectorNormalize", 4),
    ("D3DRMColorGetAlpha", 4),
    ("D3DRMColorGetBlue", 4),
    ("D3DRMColorGetGreen", 4),
    ("D3DRMColorGetRed", 4),
    ("D3DRMCreateColorRGB", 12),
    ("D3DRMCreateColorRGBA", 16),
    ("D3DRMMatrixFromQuaternion", 8),
    ("D3DRMQuaternionFromRotation", 12),
    ("D3DRMQuaternionMultiply", 12),
    ("D3DRMQuaternionSlerp", 16),
    ("D3DRMVectorAdd", 12),
    ("D3DRMVectorCrossProduct", 12),
    ("D3DRMVectorDotProduct", 8),
    ("D3DRMVectorModulus", 4),
    ("D3DRMVectorReflect", 12),
    ("D3DRMVectorRotate", 16),
    ("D3DRMVectorScale", 12),
    ("D3DRMVectorSubtract", 12),
)


@pytest.mark.msvc50
@pytest.mark.skipif(shutil.which("wine") is None, reason="requires Wine")
@pytest.mark.parametrize(("profile_identifier", "root"), _installed_roots() or [(None, None)])
def test_staged_link_orders_equal_imports_with_microsofts_qsort(
    tmp_path: Path,
    profile_identifier: str | None,
    root: Path | None,
) -> None:
    if profile_identifier is None or root is None:
        pytest.skip("requires an authenticated installation in REPROBIT_MSVC_5_0_*_ROOT")
    from reprobit.classic.pe_imports import _PE32Imports

    declarations = []
    calls = []
    for name, size in _D3DRM_IMPORTS:
        arguments = size // 4
        declarations.append(
            f"__declspec(dllimport) int __stdcall {name}({', '.join(['int'] * arguments)});"
        )
        calls.append(f"r += {name}({', '.join(['0'] * arguments)});")
    (tmp_path / "probe.c").write_text(
        "\n".join(declarations)
        + "\nint entry(void) { int r = 0; "
        + " ".join(calls)
        + " return r; }\n"
    )
    projection = tmp_path / "toolchain"
    for _name, (source, _patched) in STAGED_SOURCES.items():
        target = projection.joinpath(*source.split("/"))
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(root.joinpath(*source.split("/")), target)
    stage_link_runtime(projection, profile_identifier)
    environment = dict(
        os.environ,
        WINEPREFIX=str(tmp_path / "prefix"),
        WINEDEBUG="-all",
        WINEDLLOVERRIDES="mscoree,mshtml=",
        LIB="z:" + str(root / "lib").replace("/", "\\"),
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

    compiled = run(root / "bin" / "cl.exe", "/nologo", "/c", "/O2", "probe.c")
    assert compiled.returncode == 0, compiled.stdout + compiled.stderr
    common = ("/NOLOGO", "/NODEFAULTLIB", "/ENTRY:entry", "/SUBSYSTEM:CONSOLE", "probe.obj")
    staged_linker = projection.joinpath(*STAGED_LINKER.split("/"))
    for linker, output in ((root / "bin" / "link.exe", "wine.exe"), (staged_linker, "native.exe")):
        linked = run(linker, *common, "d3drm.lib", f"/OUT:{output}")
        assert linked.returncode == 0, linked.stdout + linked.stderr

    def slots(name: str) -> list[object]:
        (descriptor,) = _PE32Imports((tmp_path / name).read_bytes()).imports
        assert descriptor.dll == "d3drm.dll"
        return [entry.identity[1] for entry in descriptor.entries]

    wine_order = slots("wine.exe")
    native_order = slots("native.exe")
    assert sorted(map(str, wine_order)) == sorted(name for name, _ in _D3DRM_IMPORTS)
    assert sorted(map(str, native_order)) == sorted(map(str, wine_order))
    assert native_order != wine_order
    # The staged LINK really binds the renamed runtime: without it, it cannot start.
    (staged_linker.parent / "MSVCR5.dll").unlink()
    assert run(staged_linker, *common, "d3drm.lib", "/OUT:missing.exe").returncode != 0
