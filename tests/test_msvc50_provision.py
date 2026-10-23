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


def _fabricate_upstream(root: Path) -> None:
    for relative in MSVC50_FILE_AUTHORITIES[SP3]:
        path = root.joinpath(*_repo_path(relative).split("/"))
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"fabricated:" + relative.encode("ascii"))
    for relative in MSVC50_CMAKE_FRONTEND_AUTHORITIES[SP3]:
        path = root.joinpath(*relative.split("/"))
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(b"fabricated:" + relative.encode("ascii"))
    for relative in MSVC50_TREE_AUTHORITIES[SP3]:
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
