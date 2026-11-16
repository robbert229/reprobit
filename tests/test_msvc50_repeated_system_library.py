"""LINK 5.0 searches a repeated system library again only under a distinct spelling."""

from __future__ import annotations

import os
import re
import shutil
import subprocess
from pathlib import Path

import pytest

from reprobit.producer_graph import (
    ProducerNode,
    ProducerRole,
    linker_library_sequence,
    materialize_argument,
)

_ROOT = os.environ.get("REPROBIT_MSVC_5_0_RTM_ROOT", "")
_WRAPPERS = Path(_ROOT) / "wine" / "x86" if _ROOT else Path()

pytestmark = [
    pytest.mark.msvc50,
    pytest.mark.skipif(
        not _ROOT
        or not (_WRAPPERS / "link").is_file()
        or (shutil.which("wine") is None and shutil.which("wine64") is None),
        reason="requires REPROBIT_MSVC_5_0_RTM_ROOT with its Wine wrappers",
    ),
]

_MAIN = """\
__declspec(dllimport) unsigned long __stdcall GetTickCount(void);
int helper(void);
int main(void) { return (int)GetTickCount() + helper(); }
"""
_HELPER = """\
__declspec(dllimport) unsigned long __stdcall GetCurrentProcessId(void);
__declspec(dllimport) int __stdcall MessageBeep(unsigned int);
int helper(void) { return (int)GetCurrentProcessId() + MessageBeep(0); }
"""


def _tool(name: str, *arguments: str, cwd: Path) -> str:
    completed = subprocess.run(
        (str(_WRAPPERS / name), *arguments),
        cwd=cwd,
        check=False,
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr
    return completed.stdout + completed.stderr


def _searched(verbose: str) -> list[str]:
    """Return the library names LINK searched, in order, each with its first import."""

    result: list[str] = []
    library: str | None = None
    for line in verbose.splitlines():
        searched = re.match(r"\s+Searching (.+):$", line)
        if searched is not None:
            library = re.split(r"[\\/]", searched.group(1))[-1].casefold()
            continue
        found = re.match(r"\s+Found __imp__(\w+)@", line)
        if found is not None and library is not None:
            result.append(f"{library}:{found.group(1)}")
            library = None
    return result


def test_toolchain_path_repeat_is_searched_where_it_is_listed(tmp_path: Path) -> None:
    (tmp_path / "main.c").write_text(_MAIN, encoding="ascii")
    (tmp_path / "helper.c").write_text(_HELPER, encoding="ascii")
    _tool("cl", "/nologo", "/c", "main.c", "helper.c", cwd=tmp_path)
    _tool("lib", "/nologo", "/out:helper.lib", "helper.obj", cwd=tmp_path)

    def link(repeat: str, output: str) -> list[str]:
        node = ProducerNode(
            id="linker.probe",
            role=ProducerRole.LINKER,
            owner="probe",
            target_id="probe",
            arguments=(
                "/nologo",
                "/verbose",
                "/nodefaultlib",
                "/entry:main",
                "${BUILD}/main.obj",
                "kernel32.lib",
                "${BUILD}/helper.lib",
                repeat,
                "user32.lib",
                f"/out:${{BUILD}}/{output}",
            ),
            inputs=(
                "build/helper.lib",
                "build/main.obj",
                "system-library/kernel32.lib",
                "system-library/user32.lib",
            ),
            outputs=(f"build/{output}",),
        )
        assert linker_library_sequence(node) == (
            "system-library/kernel32.lib",
            "build/helper.lib",
            "system-library/kernel32.lib",
            "system-library/user32.lib",
        )
        arguments = tuple(
            materialize_argument(
                value,
                source_root="Z:" + tmp_path.as_posix(),
                build_root="Z:" + tmp_path.as_posix(),
                toolchain_root="Z:" + Path(_ROOT).as_posix(),
            )
            for value in node.arguments
        )
        return _searched(_tool("link", *arguments, cwd=tmp_path))

    # A bare repeat is the same name: LINK skips it and finds kernel32's
    # second import only in its next pass, after user32.lib.
    assert link("kernel32.lib", "bare.exe") == [
        "kernel32.lib:GetTickCount",
        "user32.lib:MessageBeep",
        "kernel32.lib:GetCurrentProcessId",
    ]
    # The toolchain path is a distinct name, searched where it is listed.
    assert link("${TOOLCHAIN}/lib/kernel32.lib", "path.exe") == [
        "kernel32.lib:GetTickCount",
        "kernel32.lib:GetCurrentProcessId",
        "user32.lib:MessageBeep",
    ]
