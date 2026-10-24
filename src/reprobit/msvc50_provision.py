"""Provision the finite MSVC 5.0 authorities used by ReproBit.

The compiler payload remains external to ReproBit.  This module checks out the
one immutable Archaic MSVC revision recorded on a 5.0 profile, copies only the
admitted files and input trees, authenticates the result against the reviewed
authorities in :mod:`reprobit.msvc50_authorities`, and publishes atomically.
It intentionally does not cache or redistribute the Microsoft payload.

Unlike MSVC 4.2, no 5.0 release needs a binary patch, and the cross-host
Wine transports are not provisioned here yet (see the platform notes); native
Windows installs and project locks are complete with what this module builds.
"""

from __future__ import annotations

import shutil
import tempfile
from collections.abc import Mapping
from pathlib import Path

from reprobit.msvc42_provision import (
    FileAuthority,
    ProgressCallback,
    ProvisionError,
    TreeAuthority,
    _checkout,
    _copy_file,
    _copy_tree,
    _emit,
    _require_file,
)
from reprobit.msvc50_authorities import (
    MSVC50_CMAKE_FRONTEND_AUTHORITIES,
    MSVC50_FILE_AUTHORITIES,
    MSVC50_TREE_AUTHORITIES,
    Msvc50FileAuthority,
)
from reprobit.toolchains import (
    MSVC_50_RTM,
    MSVC_50_SP1,
    MSVC_50_SP2,
    MSVC_50_SP3,
    ToolchainProfile,
    portable_tree_receipt,
    profile,
)

MSVC_50_PROFILES = (MSVC_50_RTM, MSVC_50_SP1, MSVC_50_SP2, MSVC_50_SP3)

# Installed bin runtime DLLs whose bytes live under a different repo path.
# Every released tree carries the runtimes in redist/; the provisioner places
# them into bin/ so the tools can load them at startup on modern Windows.
_RUNTIME_PLACEMENT = {
    "bin/msvcrt.dll": "redist/msvcrt.dll",
    "bin/msvcp50.dll": "redist/msvcp50.dll",
}


def _file_table(
    table: Mapping[str, Msvc50FileAuthority],
) -> dict[str, FileAuthority]:
    return {
        relative: FileAuthority(authority.size, authority.sha256)
        for relative, authority in table.items()
    }


def _file_authorities(identifier: str) -> Mapping[str, FileAuthority]:
    return _file_table(MSVC50_FILE_AUTHORITIES[identifier])


def _tree_authorities(identifier: str) -> Mapping[str, TreeAuthority]:
    return {
        relative: TreeAuthority(
            authority.entries,
            authority.max_depth,
            authority.membership_sha256,
            authority.content_sha256,
        )
        for relative, authority in MSVC50_TREE_AUTHORITIES[identifier].items()
    }


def _cmake_frontend_authorities(identifier: str) -> Mapping[str, FileAuthority]:
    return _file_table(MSVC50_CMAKE_FRONTEND_AUTHORITIES[identifier])


def verify_msvc50(root: Path, profile_identifier: str) -> None:
    """Authenticate an existing MSVC 5.0 installation against its profile."""
    requested_root = root.expanduser()
    if requested_root.is_symlink() or not requested_root.is_dir():
        raise ProvisionError(
            f"toolchain root is absent, not a directory, or redirected: {requested_root}"
        )
    admitted_root = requested_root.resolve(strict=True)
    for relative, authority in _file_authorities(profile_identifier).items():
        _require_file(admitted_root.joinpath(*relative.split("/")), authority)
    for relative, authority in _cmake_frontend_authorities(profile_identifier).items():
        _require_file(admitted_root.joinpath(*relative.split("/")), authority)
    for relative, tree_authority in _tree_authorities(profile_identifier).items():
        tree = admitted_root.joinpath(*relative.split("/"))
        if tree.is_symlink() or not tree.is_dir():
            raise ProvisionError(f"toolchain tree is absent or redirected: {tree}")
        receipt = portable_tree_receipt(tree, relative)
        received = TreeAuthority(
            receipt.entry_count,
            receipt.max_depth,
            receipt.membership_sha256,
            receipt.content_sha256,
        )
        if received != tree_authority:
            raise ProvisionError(
                f"portable tree authority differs for {relative}: "
                f"expected {tree_authority!r}, received {received!r}"
            )


def _reject_unadmitted(root: Path, profile_identifier: str) -> None:
    """Reject a destination that carries files the profile does not admit.

    A published payload holds exactly the admitted files and trees, so calling
    an existing destination "exact" is only honest when nothing else sits in
    it.  Input trees need no scan because portable tree receipts already hash
    their membership.
    """
    admitted = set(_file_authorities(profile_identifier))
    admitted.update(_cmake_frontend_authorities(profile_identifier))
    tree_roots = tuple(f"{relative}/" for relative in _tree_authorities(profile_identifier))
    extras = []
    for path in sorted(root.rglob("*")):
        if not path.is_file():
            continue
        relative = path.relative_to(root).as_posix()
        if relative not in admitted and not relative.startswith(tree_roots):
            extras.append(relative)
    if extras:
        shown = ", ".join(extras[:5])
        if len(extras) > 5:
            shown += f", and {len(extras) - 5} more"
        raise ProvisionError(f"destination holds files not admitted by the profile: {shown}")


def _cone_paths(installation_profile: ToolchainProfile) -> tuple[str, ...]:
    roots = {relative.split("/", 1)[0] for relative in installation_profile.sources[0].paths}
    roots.update(repo_path.split("/", 1)[0] for repo_path in _RUNTIME_PLACEMENT.values())
    return tuple(sorted(roots))


def provision_msvc50(
    destination: Path,
    profile_identifier: str,
    progress: ProgressCallback | None = None,
) -> Path:
    """Fetch, authenticate, and publish one exact MSVC 5.0 installation."""
    requested_destination = destination.expanduser()
    if requested_destination.is_symlink():
        raise ProvisionError(
            f"toolchain destination must not be a redirected path: {requested_destination}"
        )
    destination = requested_destination.resolve(strict=False)
    if destination == Path(destination.anchor):
        raise ProvisionError("toolchain destination must not be a filesystem root")
    if destination.exists() or destination.is_symlink():
        _emit(progress, f"verifying existing destination {destination}")
        _reject_unadmitted(destination, profile_identifier)
        verify_msvc50(destination, profile_identifier)
        _emit(progress, "existing toolchain is exact; no download needed")
        return destination

    installation_profile = profile(profile_identifier)
    source = installation_profile.sources[0]
    repository_name = source.repository.rsplit("/", 1)[-1].removesuffix(".git")
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(prefix=".reprobit-msvc50-", dir=destination.parent)).resolve(
        strict=True
    )
    try:
        checkout = temporary / repository_name
        payload = temporary / "payload"
        payload.mkdir()
        _emit(progress, f"fetching {repository_name}@{source.revision[:12]}")
        _checkout(checkout, source.repository, source.revision, _cone_paths(installation_profile))
        for relative in _file_authorities(profile_identifier):
            if relative in _RUNTIME_PLACEMENT:
                continue
            _copy_file(checkout, payload, relative)
        for relative in _cmake_frontend_authorities(profile_identifier):
            _copy_file(checkout, payload, relative)
        for relative in _tree_authorities(profile_identifier):
            _copy_tree(checkout, payload, relative)
        for installed, repo_path in _RUNTIME_PLACEMENT.items():
            _copy_file(checkout, payload, repo_path)
            (payload / repo_path).replace(payload / installed)
        redist = payload / "redist"
        if redist.is_dir() and not any(redist.iterdir()):
            redist.rmdir()
        _emit(progress, "authenticating files and portable input trees")
        verify_msvc50(payload, profile_identifier)
        payload.replace(destination)
        _emit(progress, f"published exact toolchain at {destination}")
        return destination
    finally:
        shutil.rmtree(temporary, ignore_errors=True)


__all__ = [
    "MSVC_50_PROFILES",
    "provision_msvc50",
    "verify_msvc50",
]
