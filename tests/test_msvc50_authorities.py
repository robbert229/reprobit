"""Tests for the committed MSVC 5.0 byte authorities.

Offline tests cross-check the authority tables against the toolchain profiles.
A network-gated test re-audits the pinned upstream revisions; it is skipped
unless REPROBIT_MSVC_5_0_UPSTREAM_ROOT names a directory holding the four pinned
checkouts (see scripts/audit_msvc50_authorities.py for the fetch recipe).
"""

from __future__ import annotations

import os
import re
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "src"))

from reprobit.msvc50_authorities import (
    MSVC50_CMAKE_FRONTEND_AUTHORITIES,
    MSVC50_FILE_AUTHORITIES,
    MSVC50_TREE_AUTHORITIES,
    Msvc50FileAuthority,
    Msvc50TreeAuthority,
)
from reprobit.toolchains import (
    MSVC_50_RTM,
    MSVC_50_SP1,
    MSVC_50_SP2,
    MSVC_50_SP3,
    profile,
)

PROFILES = (MSVC_50_RTM, MSVC_50_SP1, MSVC_50_SP2, MSVC_50_SP3)
SHA256 = re.compile(r"^[0-9a-f]{64}$")


def test_every_profile_has_authorities_for_every_declared_file() -> None:
    for identifier in PROFILES:
        toolchain_profile = profile(identifier)
        expected = set(toolchain_profile.required_producers) | set(
            toolchain_profile.required_runtime_files
        )
        assert set(MSVC50_FILE_AUTHORITIES[identifier]) == expected, identifier


def test_every_profile_has_authorities_for_every_declared_tree() -> None:
    for identifier in PROFILES:
        toolchain_profile = profile(identifier)
        expected = set(toolchain_profile.include_roots) | set(toolchain_profile.library_roots)
        assert set(MSVC50_TREE_AUTHORITIES[identifier]) == expected, identifier


def test_every_profile_ships_an_audited_cmake_frontend() -> None:
    for identifier in PROFILES:
        assert set(MSVC50_CMAKE_FRONTEND_AUTHORITIES[identifier]) == {"bin/nmake.exe"}, identifier


def test_authorities_are_reviewed_shapes() -> None:
    for identifier in PROFILES:
        for relative, authority in MSVC50_FILE_AUTHORITIES[identifier].items():
            assert isinstance(authority, Msvc50FileAuthority), f"{identifier}:{relative}"
            assert authority.size > 0, f"{identifier}:{relative}"
            assert SHA256.match(authority.sha256), f"{identifier}:{relative}"
        for relative, tree in MSVC50_TREE_AUTHORITIES[identifier].items():
            assert isinstance(tree, Msvc50TreeAuthority), f"{identifier}:{relative}"
            assert tree.entries > 0, f"{identifier}:{relative}"
            assert tree.max_depth >= 0, f"{identifier}:{relative}"
            assert SHA256.match(tree.membership_sha256), f"{identifier}:{relative}"
            assert SHA256.match(tree.content_sha256), f"{identifier}:{relative}"


def test_releases_are_not_all_one_collapsed_revision() -> None:
    tables = [
        {
            relative: authority.sha256
            for relative, authority in MSVC50_FILE_AUTHORITIES[identifier].items()
        }
        for identifier in PROFILES
    ]
    assert tables[0] != tables[-1], "RTM and SP3 authorities collapsed"


def test_sp2_content_is_reviewed_equal_to_sp1() -> None:
    # Audited 2026-10-22: the pinned SP2 revision differs from SP1 only in
    # README.md, so every admitted compiler file is byte-identical between
    # them. If upstream ever changes SP2, regenerate with the audit script and
    # this review note moves (or the equality fails, which is the point).
    sp1 = MSVC50_FILE_AUTHORITIES[MSVC_50_SP1]
    sp2 = MSVC50_FILE_AUTHORITIES[MSVC_50_SP2]
    assert {path: authority.sha256 for path, authority in sp1.items()} == {
        path: authority.sha256 for path, authority in sp2.items()
    }


@pytest.mark.skipif(
    "REPROBIT_MSVC_5_0_UPSTREAM_ROOT" not in os.environ,
    reason="set REPROBIT_MSVC_5_0_UPSTREAM_ROOT to re-audit pinned MSVC 5.0 upstreams",
)
def test_committed_authorities_match_pinned_upstreams() -> None:
    root = os.environ["REPROBIT_MSVC_5_0_UPSTREAM_ROOT"]
    script = Path(__file__).resolve().parents[1] / "scripts" / "audit_msvc50_authorities.py"
    result = subprocess.run(
        (sys.executable, str(script), "--checkouts-root", root),
        check=False,
        capture_output=True,
        text=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
