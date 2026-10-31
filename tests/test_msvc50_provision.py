"""Fabricated-upstream tests for the MSVC 5.0 provisioner.

The pinned upstream bytes cannot be invented offline, so the checkout step is
replaced by a fabricated tree and every authority accessor is monkeypatched to
the fabricated bytes. This mirrors how the MSVC 4.2 provisioner exercises its
verify path against invented authorities.
"""

from __future__ import annotations

import hashlib
import os
import shutil
from pathlib import Path

import pytest

from reprobit import msvc50_provision
from reprobit.msvc42_provision import FileAuthority, ProvisionError, TreeAuthority
from reprobit.msvc50_authorities import (
    MSVC50_CMAKE_FRONTEND_AUTHORITIES,
    MSVC50_FILE_AUTHORITIES,
    MSVC50_TREE_AUTHORITIES,
)
from reprobit.toolchains import portable_tree_receipt

SP3 = "msvc_5_0_sp3"
NOT_ADMITTED = "bin/psapi_extra.dll"


def _repo_path(installed: str) -> str:
    """Fabricated upstream mirrors the real layout: runtimes live in redist/."""
    return msvc50_provision._RUNTIME_PLACEMENT.get(installed, installed)


def _fabricate_upstream(root: Path, identifier: str = SP3) -> None:
    for relative in MSVC50_FILE_AUTHORITIES[identifier]:
        path = root.joinpath(*_repo_path(relative).split("/"))
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"fabricated:" + relative.encode("ascii"))
    for relative in MSVC50_CMAKE_FRONTEND_AUTHORITIES[identifier]:
        path = root.joinpath(*relative.split("/"))
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"fabricated:" + relative.encode("ascii"))
    for relative in MSVC50_TREE_AUTHORITIES[identifier]:
        tree = root / relative
        tree.mkdir(parents=True, exist_ok=True)
        (tree / "fixture.h").write_text(relative, encoding="utf-8")
    extra = root / NOT_ADMITTED
    extra.parent.mkdir(parents=True, exist_ok=True)
    extra.write_bytes(b"not admitted by the profile")


def _install_fake_checkout(
    monkeypatch: pytest.MonkeyPatch,
    fabricated: Path,
) -> dict[str, int]:
    state = {"fetches": 0}

    def checkout(repository: Path, _url: str, _revision: str, _paths: tuple[str, ...]) -> None:
        state["fetches"] += 1
        shutil.copytree(fabricated, repository)

    monkeypatch.setattr(msvc50_provision, "_checkout", checkout)
    return state


def _install_fake_authorities(monkeypatch: pytest.MonkeyPatch, fabricated: Path) -> None:
    def file_table(relative: str) -> FileAuthority:
        path = fabricated.joinpath(*_repo_path(relative).split("/"))
        return FileAuthority(path.stat().st_size, hashlib.sha256(path.read_bytes()).hexdigest())

    def file_authorities(identifier: str) -> dict[str, FileAuthority]:
        return {relative: file_table(relative) for relative in MSVC50_FILE_AUTHORITIES[identifier]}

    def frontend_authorities(identifier: str) -> dict[str, FileAuthority]:
        return {
            relative: file_table(relative)
            for relative in MSVC50_CMAKE_FRONTEND_AUTHORITIES[identifier]
        }

    def tree_authorities(identifier: str) -> dict[str, TreeAuthority]:
        receipts = {}
        for relative in MSVC50_TREE_AUTHORITIES[identifier]:
            receipt = portable_tree_receipt(fabricated / relative, relative)
            receipts[relative] = TreeAuthority(
                receipt.entry_count,
                receipt.max_depth,
                receipt.membership_sha256,
                receipt.content_sha256,
            )
        return receipts

    monkeypatch.setattr(msvc50_provision, "_file_authorities", file_authorities)
    monkeypatch.setattr(msvc50_provision, "_tree_authorities", tree_authorities)
    monkeypatch.setattr(msvc50_provision, "_cmake_frontend_authorities", frontend_authorities)


@pytest.fixture
def fabricated(tmp_path: Path) -> Path:
    root = tmp_path / "fabricated-upstream"
    _fabricate_upstream(root)
    return root


def test_provision_fetches_authenticates_and_publishes_exactly(
    tmp_path: Path,
    fabricated: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = _install_fake_checkout(monkeypatch, fabricated)
    _install_fake_authorities(monkeypatch, fabricated)
    destination = tmp_path / "toolchain"
    messages: list[str] = []

    result = msvc50_provision.provision_msvc50(destination, SP3, progress=messages.append)

    assert result == destination
    assert state == {"fetches": 1}
    assert any(message.startswith("fetching msvc500sp3@") for message in messages)
    assert messages[-1].startswith("published exact toolchain at")
    msvc50_provision.verify_msvc50(destination, SP3)


@pytest.mark.parametrize("identifier", ("msvc_5_0_rtm", "msvc_5_0_sp1", "msvc_5_0_sp2"))
def test_remaining_releases_provision_exactly(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
    identifier: str,
) -> None:
    fabricated = tmp_path / "fabricated-upstream"
    _fabricate_upstream(fabricated, identifier)
    state = _install_fake_checkout(monkeypatch, fabricated)
    _install_fake_authorities(monkeypatch, fabricated)
    destination = tmp_path / identifier

    result = msvc50_provision.provision_msvc50(destination, identifier)

    assert result == destination
    assert state == {"fetches": 1}
    msvc50_provision.verify_msvc50(destination, identifier)
    assert not (destination / NOT_ADMITTED).exists(), "undeclared upstream file was admitted"
    for relative in MSVC50_FILE_AUTHORITIES[SP3]:
        assert destination.joinpath(*relative.split("/")).is_file()


def test_rerun_authenticates_without_another_fetch(
    tmp_path: Path,
    fabricated: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = _install_fake_checkout(monkeypatch, fabricated)
    _install_fake_authorities(monkeypatch, fabricated)
    destination = tmp_path / "toolchain"
    msvc50_provision.provision_msvc50(destination, SP3)
    messages: list[str] = []

    result = msvc50_provision.provision_msvc50(destination, SP3, progress=messages.append)

    assert result == destination
    assert state == {"fetches": 1}
    assert messages == [
        f"verifying existing destination {destination}",
        "existing toolchain is exact; no download needed",
    ]


def test_existing_inexact_destination_never_downloads(
    tmp_path: Path,
    fabricated: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = _install_fake_checkout(monkeypatch, fabricated)
    _install_fake_authorities(monkeypatch, fabricated)
    destination = tmp_path / "toolchain"
    msvc50_provision.provision_msvc50(destination, SP3)
    compiler = destination / "bin/link.exe"
    compiler.write_bytes(b"mutated")

    with pytest.raises(ProvisionError, match="file authority differs"):
        msvc50_provision.provision_msvc50(destination, SP3)
    assert state == {"fetches": 1}


def test_rerun_refuses_a_polluted_destination_without_downloading(
    tmp_path: Path,
    fabricated: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    state = _install_fake_checkout(monkeypatch, fabricated)
    _install_fake_authorities(monkeypatch, fabricated)
    destination = tmp_path / "toolchain"
    msvc50_provision.provision_msvc50(destination, SP3)
    (destination / NOT_ADMITTED).write_bytes(b"pollution that the fetch path would have stripped")

    with pytest.raises(ProvisionError, match=r"not admitted by the profile: bin/psapi_extra\.dll"):
        msvc50_provision.provision_msvc50(destination, SP3)
    assert state == {"fetches": 1}
    assert (destination / NOT_ADMITTED).is_file(), "the polluted file must not be touched"


def test_verify_requires_every_declared_file(tmp_path: Path) -> None:
    with pytest.raises(ProvisionError, match="absent or redirected"):
        msvc50_provision.verify_msvc50(tmp_path, SP3)


def test_verify_rejects_tree_mutation(
    tmp_path: Path,
    fabricated: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    _install_fake_authorities(monkeypatch, fabricated)
    installed = tmp_path / "installed"
    shutil.copytree(fabricated, installed)
    for installed_path, repo_path in msvc50_provision._RUNTIME_PLACEMENT.items():
        source = installed.joinpath(*repo_path.split("/"))
        destination = installed.joinpath(*installed_path.split("/"))
        destination.parent.mkdir(parents=True, exist_ok=True)
        source.replace(destination)
    msvc50_provision._install_transport_assets(installed)
    shutil.rmtree(installed / "atl/include")

    with pytest.raises(ProvisionError, match="absent or redirected"):
        msvc50_provision.verify_msvc50(installed, SP3)
    (installed / "atl/include").mkdir(parents=True, exist_ok=True)
    (fabricated / "atl/include/extra.h").write_text("later", encoding="utf-8")
    _install_fake_authorities(monkeypatch, fabricated)

    with pytest.raises(ProvisionError, match="portable tree authority differs"):
        msvc50_provision.verify_msvc50(installed, SP3)


@pytest.mark.skipif(os.name != "posix", reason="portable symlink creation")
def test_provision_rejects_redirected_destination(tmp_path: Path) -> None:
    real = tmp_path / "real"
    real.mkdir()
    redirected = tmp_path / "redirected"
    redirected.symlink_to(real, target_is_directory=True)

    with pytest.raises(ProvisionError, match="redirected path"):
        msvc50_provision.provision_msvc50(redirected, SP3)


@pytest.mark.parametrize(
    ("relative", "authority"),
    msvc50_provision._PROVISIONED_TRANSPORT_FILES.items(),
)
def test_packaged_transport_assets_match_fixed_authority(
    relative: str,
    authority: FileAuthority,
) -> None:
    source = msvc50_provision._transport_asset(relative, authority)

    assert source.stat().st_size == authority.size
    assert hashlib.sha256(source.read_bytes()).hexdigest() == authority.sha256
    assert b"Permission to use, copy, modify" in source.read_bytes()


def test_missing_packaged_transport_is_a_provision_error(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    def missing(_name: str) -> Path:
        raise FileNotFoundError("simulated missing wheel asset")

    monkeypatch.setattr(msvc50_provision, "runtime_asset_directory", missing)

    with pytest.raises(ProvisionError, match="missing wheel asset"):
        msvc50_provision._transport_asset(
            "wine/x86/cl", msvc50_provision._TRANSPORT_FILES["wine/x86/cl"]
        )


def test_transport_install_is_exact_regular_and_non_overwriting(tmp_path: Path) -> None:
    msvc50_provision._install_transport_assets(tmp_path)

    for relative, authority in msvc50_provision._PROVISIONED_TRANSPORT_FILES.items():
        installed = tmp_path.joinpath(*relative.split("/"))
        assert installed.is_file()
        assert not installed.is_symlink()
        assert installed.stat().st_size == authority.size
        assert hashlib.sha256(installed.read_bytes()).hexdigest() == authority.sha256
        if os.name == "posix":
            assert os.access(installed, os.X_OK)

    with pytest.raises(ProvisionError, match="already exists"):
        msvc50_provision._install_transport_assets(tmp_path)


def test_complete_verification_requires_cross_host_transport(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(msvc50_provision, "_file_authorities", lambda identifier: {})
    monkeypatch.setattr(msvc50_provision, "_tree_authorities", lambda identifier: {})
    monkeypatch.setattr(msvc50_provision, "_cmake_frontend_authorities", lambda identifier: {})

    with pytest.raises(ProvisionError, match="absent or redirected"):
        msvc50_provision.verify_msvc50(tmp_path, SP3)

    msvc50_provision._install_transport_assets(tmp_path)
    msvc50_provision.verify_msvc50(tmp_path, SP3)


def test_complete_verification_rejects_transport_mutation(
    tmp_path: Path,
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    monkeypatch.setattr(msvc50_provision, "_file_authorities", lambda identifier: {})
    monkeypatch.setattr(msvc50_provision, "_tree_authorities", lambda identifier: {})
    monkeypatch.setattr(msvc50_provision, "_cmake_frontend_authorities", lambda identifier: {})
    msvc50_provision._install_transport_assets(tmp_path)
    transport = tmp_path / "wine" / "x86" / "wine-msvc.sh"
    transport.write_bytes(transport.read_bytes() + b"\n")

    with pytest.raises(ProvisionError, match="file authority differs"):
        msvc50_provision.verify_msvc50(tmp_path, SP3)
