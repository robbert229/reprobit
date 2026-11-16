"""Run MSVC 5.0's LINK.EXE on the toolchain's own MSVCRT 5.00.

LINK 5.0 builds each DLL's import address table by sorting the loaded
import-library members with the C runtime's ``qsort``, keyed on the DLL name
alone.  Imports of one DLL compare equal, so their slot order is whatever
that ``qsort`` leaves.  Under Wine, ``link.exe``'s ``MSVCRT.dll`` resolves to
Wine's builtin, whose ``qsort`` permutes equal keys differently from
Microsoft's MSVCRT 5.00, so a Wine link cannot give the IAT a link on Windows
gives.  Wine itself needs its builtin ``msvcrt`` (its own DLLs import it), so
a ``WINEDLLOVERRIDES`` entry cannot force the native one.

Instead every build stages a private copy of LINK: ``link.exe`` and the
toolchain DLLs it loads that import the C runtime (``mspdb50.dll``,
``msdis100.dll`` and, through the latter, ``msvcp50.dll``) have their one
``MSVCRT.dll`` import name rewritten to the same-length ``MSVCR5.dll``, and
the toolchain's ``msvcrt.dll`` is copied beside them under that name.  The
loader searches the executable's directory first and Wine has no builtin
called ``MSVCR5``, so LINK and its DLLs bind to Microsoft's 5.00 runtime
while Wine keeps its own.

The staged bytes are a pure function of the authenticated toolchain files:
each input must equal its reviewed profile authority, and each output must
equal the reviewed derived authority in
:data:`reprobit.msvc50_authorities.MSVC50_NATIVE_CRT_LINK_AUTHORITIES`, which
``scripts/audit_msvc50_authorities.py`` recomputes from the pinned upstream
revisions.  Nothing is written to the installed toolchain.
"""

from __future__ import annotations

import hashlib
import struct
from collections.abc import Callable, Iterable, Mapping
from pathlib import Path, PurePosixPath
from types import MappingProxyType

from reprobit.binary import ByteIdentityError
from reprobit.msvc50_authorities import (
    MSVC50_FILE_AUTHORITIES,
    MSVC50_NATIVE_CRT_LINK_AUTHORITIES,
    Msvc50FileAuthority,
)
from reprobit.pe32 import parse_pe32_headers
from reprobit.strict_json import JsonValue

CRT_IMPORT_NAME = b"MSVCRT.dll"
STAGED_CRT_NAME = b"MSVCR5.dll"
if len(CRT_IMPORT_NAME) != len(STAGED_CRT_NAME):  # pragma: no cover - module invariant
    raise AssertionError("the staged C runtime name must keep the import name's length")

# Toolchain-relative directory of the staged set inside a run's projected
# toolchain.  It is never created in an installed toolchain.
STAGED_DIRECTORY = "reprobit-native-crt-link"

# Staged file name -> the authenticated toolchain file it derives from, and
# whether its C runtime import is renamed.  link.exe loads mspdb50.dll and
# msdis100.dll; msdis100.dll loads msvcp50.dll.  Each imports MSVCRT.dll.
STAGED_SOURCES: Mapping[str, tuple[str, bool]] = MappingProxyType(
    {
        "link.exe": ("bin/link.exe", True),
        "mspdb50.dll": ("bin/mspdb50.dll", True),
        "msdis100.dll": ("bin/msdis100.dll", True),
        "msvcp50.dll": ("bin/msvcp50.dll", True),
        STAGED_CRT_NAME.decode("ascii"): ("bin/msvcrt.dll", False),
    }
)
STAGED_LINKER = f"{STAGED_DIRECTORY}/link.exe"
DERIVATION_SCHEME = "msvc50-native-crt-link-v1"


class Msvc50LinkRuntimeError(ValueError):
    """The staged LINK runtime cannot be derived soundly."""


def applies_to_profile(profile_identifier: str) -> bool:
    """Return whether the profile's LINK runs through the staged runtime."""

    return profile_identifier in MSVC50_NATIVE_CRT_LINK_AUTHORITIES


def _import_name_offsets(image: bytes) -> tuple[tuple[bytes, int], ...]:
    """Return each import descriptor's DLL name and its file offset."""

    try:
        headers = parse_pe32_headers(image, minimum_optional_size=144)
        rva, size = headers.data_directory(1, "import directory")
        if rva == 0 or size < 20:
            raise Msvc50LinkRuntimeError("image has no import directory")
        offset = headers.rva_to_offset(rva, 20, context="import directory")
        names: list[tuple[bytes, int]] = []
        while True:
            if offset + 20 > len(image):
                raise Msvc50LinkRuntimeError("import directory runs past the file")
            descriptor = struct.unpack_from("<IIIII", image, offset)
            if not any(descriptor):
                return tuple(names)
            name_offset = headers.rva_to_offset(descriptor[3], 1, context="import DLL name")
            end = image.find(b"\0", name_offset)
            if end < 0:
                raise Msvc50LinkRuntimeError("import DLL name is not NUL-terminated")
            names.append((image[name_offset:end], name_offset))
            offset += 20
    except ByteIdentityError as exc:
        raise Msvc50LinkRuntimeError(f"image is not a readable PE32 file: {exc}") from exc


def patch_crt_import(image: bytes) -> bytes:
    """Rename the image's one ``MSVCRT.dll`` import to ``MSVCR5.dll``.

    The name is matched case-insensitively as a NUL-terminated string.  It
    must occur exactly once in the file, and that occurrence must be the name
    of exactly one import descriptor; anything else is refused rather than
    guessed at.
    """

    needle = CRT_IMPORT_NAME.lower() + b"\0"
    lowered = image.lower()
    occurrences: list[int] = []
    start = 0
    while (index := lowered.find(needle, start)) >= 0:
        occurrences.append(index)
        start = index + 1
    if len(occurrences) != 1:
        raise Msvc50LinkRuntimeError(
            f"expected exactly one {CRT_IMPORT_NAME.decode()} name, found {len(occurrences)}"
        )
    descriptors = [
        offset
        for name, offset in _import_name_offsets(image)
        if name.lower() == CRT_IMPORT_NAME.lower()
    ]
    if descriptors != occurrences:
        raise Msvc50LinkRuntimeError(
            f"the {CRT_IMPORT_NAME.decode()} name is not exactly one import descriptor's name"
        )
    (offset,) = occurrences
    return image[:offset] + STAGED_CRT_NAME + image[offset + len(STAGED_CRT_NAME) :]


def _authority(payload: bytes) -> Msvc50FileAuthority:
    return Msvc50FileAuthority(len(payload), hashlib.sha256(payload).hexdigest())


def derive_link_runtime(read_toolchain_file: Callable[[str], bytes]) -> dict[str, bytes]:
    """Derive the staged set from toolchain files (no authentication)."""

    staged: dict[str, bytes] = {}
    for name, (source, patched) in STAGED_SOURCES.items():
        payload = read_toolchain_file(source)
        try:
            staged[name] = patch_crt_import(payload) if patched else payload
        except Msvc50LinkRuntimeError as exc:
            raise Msvc50LinkRuntimeError(f"{source}: {exc}") from exc
    return staged


def authenticated_link_runtime(
    profile_identifier: str,
    read_toolchain_file: Callable[[str], bytes],
) -> dict[str, bytes]:
    """Derive the staged set and require reviewed input and output bytes."""

    inputs = MSVC50_FILE_AUTHORITIES.get(profile_identifier)
    outputs = MSVC50_NATIVE_CRT_LINK_AUTHORITIES.get(profile_identifier)
    if inputs is None or outputs is None:
        raise Msvc50LinkRuntimeError(
            f"profile {profile_identifier!r} has no reviewed native-CRT LINK runtime"
        )

    def read_authenticated(relative: str) -> bytes:
        payload = read_toolchain_file(relative)
        expected = inputs.get(relative)
        if expected is None or _authority(payload) != expected:
            raise Msvc50LinkRuntimeError(
                f"{relative} differs from the reviewed {profile_identifier} authority"
            )
        return payload

    staged = derive_link_runtime(read_authenticated)
    if set(staged) != set(outputs):
        raise Msvc50LinkRuntimeError("reviewed native-CRT LINK runtime names drifted")
    for name, payload in staged.items():
        received = _authority(payload)
        if received != outputs[name]:
            raise Msvc50LinkRuntimeError(
                f"staged {name} differs from its reviewed derivation: "
                f"expected {outputs[name].size}/{outputs[name].sha256}, "
                f"received {received.size}/{received.sha256}"
            )
    return staged


def stage_link_runtime(
    toolchain_root: Path,
    profile_identifier: str,
    *,
    read_toolchain_file: Callable[[str], bytes] | None = None,
    publish: Callable[[Path, str, bytes], object] | None = None,
) -> tuple[Path, ...]:
    """Publish the authenticated staged set beneath a run's toolchain copy.

    ``toolchain_root`` is a run-private projection of the locked toolchain;
    the staged directory must not exist yet.  Returns the published paths in
    staged-name order.
    """

    from reprobit.secure_path_contracts import SecurePathError
    from reprobit.secure_paths import atomic_publish_new_relative, read_relative_file

    root = toolchain_root.resolve(strict=True)

    def read_default(relative: str) -> bytes:
        try:
            payload, _snapshot = read_relative_file(root, relative)
        except (OSError, SecurePathError) as exc:
            raise Msvc50LinkRuntimeError(
                f"{relative} is not readable in the locked toolchain; the toolchain lock "
                f"must admit it as a tool or runtime file: {exc}"
            ) from exc
        return payload

    def publish_default(base: Path, relative: str, payload: bytes) -> object:
        return atomic_publish_new_relative(base, relative, payload)

    reader = read_default if read_toolchain_file is None else read_toolchain_file
    writer = publish_default if publish is None else publish
    staged = authenticated_link_runtime(profile_identifier, reader)
    directory = root / STAGED_DIRECTORY
    if directory.exists() or directory.is_symlink():
        raise Msvc50LinkRuntimeError(f"staged LINK runtime already exists: {directory}")
    directory.mkdir()
    published: list[Path] = []
    for name in sorted(staged, key=str.casefold):
        relative = PurePosixPath(STAGED_DIRECTORY, name).as_posix()
        writer(root, relative, staged[name])
        published.append(directory / name)
    return tuple(published)


def locked_link_runtime_authorities(
    profile_identifier: str,
    locked_files: Iterable[tuple[str, str, int | None]],
) -> Mapping[str, Msvc50FileAuthority]:
    """Return the staged files a toolchain lock authenticates, by relative path.

    ``locked_files`` holds each locked tool or runtime file as
    ``(relative path, sha256, size)``.  The staged set is authenticated only
    when every derivation input is locked with its reviewed profile bytes;
    then each staged file is admitted at its staged path with its reviewed
    derived digest.  Otherwise nothing is admitted.  Keys are case-folded.
    """

    inputs = MSVC50_FILE_AUTHORITIES.get(profile_identifier)
    outputs = MSVC50_NATIVE_CRT_LINK_AUTHORITIES.get(profile_identifier)
    if inputs is None or outputs is None:
        return MappingProxyType({})
    locked: dict[str, list[tuple[str, int | None]]] = {}
    for relative, digest, size in locked_files:
        locked.setdefault(relative.casefold(), []).append((digest, size))
    for source, _patched in STAGED_SOURCES.values():
        expected = inputs.get(source)
        entries = locked.get(source.casefold(), [])
        if (
            expected is None
            or len(entries) != 1
            or entries[0][0] != expected.sha256
            or entries[0][1] not in (None, expected.size)
        ):
            return MappingProxyType({})
    return MappingProxyType(
        {
            PurePosixPath(STAGED_DIRECTORY, name).as_posix().casefold(): authority
            for name, authority in outputs.items()
        }
    )


def link_runtime_material(profile_identifier: str) -> JsonValue:
    """Describe the staged LINK runtime for cache-key material."""

    outputs = MSVC50_NATIVE_CRT_LINK_AUTHORITIES.get(profile_identifier)
    if outputs is None:
        return None
    return {
        "scheme": DERIVATION_SCHEME,
        "linker": STAGED_LINKER,
        "files": [
            {"name": name, "size": outputs[name].size, "sha256": outputs[name].sha256}
            for name in sorted(outputs, key=str.casefold)
        ],
    }


__all__ = [
    "CRT_IMPORT_NAME",
    "DERIVATION_SCHEME",
    "STAGED_CRT_NAME",
    "STAGED_DIRECTORY",
    "STAGED_LINKER",
    "STAGED_SOURCES",
    "Msvc50LinkRuntimeError",
    "applies_to_profile",
    "authenticated_link_runtime",
    "derive_link_runtime",
    "link_runtime_material",
    "locked_link_runtime_authorities",
    "patch_crt_import",
    "stage_link_runtime",
]
