from __future__ import annotations

import pytest

from reprobit.classic.arguments import lex_compile_arguments


def _command(*options: str) -> list[str]:
    return [
        "CL.EXE",
        "/nologo",
        *options,
        "/Zi",
        "/FoR:\\build\\unit.obj",
        "/FdR:\\build\\unit.obj.pdb",
        "-c",
        "R:\\source\\unit.c",
    ]


@pytest.mark.parametrize("option", ("/ML", "-ML", "/Zl", "-Zl"))
def test_msvc5_runtime_and_default_library_options_are_admitted(option: str) -> None:
    # /ML is MSVC 5.0's single-threaded static runtime (the default it states
    # explicitly); /Zl omits default-library names from the object.
    parsed = lex_compile_arguments(_command("/O2", option))

    assert parsed["errors"] == []
    assert {"role": "flag", "token": option} in [
        {"role": role["role"], "token": role["token"]} for role in parsed["roles"]
    ]


@pytest.mark.parametrize("option", ("/ml", "/ZL", "/Zl-"))
def test_misspelled_runtime_and_default_library_options_stay_rejected(option: str) -> None:
    parsed = lex_compile_arguments(_command(option))

    assert any(option in error for error in parsed["errors"])
