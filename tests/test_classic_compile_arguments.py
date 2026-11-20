from __future__ import annotations

import pytest

from reprobit.binary import ByteIdentityError
from reprobit.classic.arguments import (
    compile_writes_pdb,
    lex_compile_arguments,
    validate_compile_arguments,
)


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


def _command_with_debug(*debug: str) -> list[str]:
    return [
        "CL.EXE",
        "/nologo",
        "/O2",
        *debug,
        "/FoR:\\build\\unit.obj",
        "/FdR:\\build\\unit.obj.pdb",
        "-c",
        "R:\\source\\unit.c",
    ]


@pytest.mark.parametrize("debug", ((), ("/Zi",), ("-Zi",)))
def test_a_compile_has_zero_or_one_debug_format(debug: tuple[str, ...]) -> None:
    # Without /Zi the compiler writes no PDB, but CMake still emits /Fd, so
    # the argv keeps its exact /Fo /Fd -c source tail either way.
    command = _command_with_debug(*debug)
    parsed = validate_compile_arguments(command)

    assert parsed["debug_format"] == (debug[0] if debug else None)
    assert parsed["Fd"][1] == "R:\\build\\unit.obj.pdb"
    assert compile_writes_pdb(command) is bool(debug)


@pytest.mark.parametrize("debug", (("/Zi", "/Zi"), ("/Zi", "-Zi")))
def test_a_repeated_debug_format_is_refused(debug: tuple[str, ...]) -> None:
    with pytest.raises(ByteIdentityError, match="at most one exact /Zi or -Zi, found 2"):
        validate_compile_arguments(_command_with_debug(*debug))


@pytest.mark.parametrize("debug", ("/Z7", "/Zd", "/zi", "/ZI"))
def test_other_debug_formats_stay_unsupported(debug: str) -> None:
    # /Z7 keeps its types in the object and /Zd writes line numbers only;
    # neither is modelled, so neither is admitted.
    parsed = lex_compile_arguments(_command_with_debug(debug))

    assert parsed["errors"]


def test_without_debug_information_the_pdb_option_is_still_required() -> None:
    command = [token for token in _command_with_debug() if not token.startswith("/Fd")]

    with pytest.raises(ByteIdentityError, match="expected one exact /Fd, found 0"):
        validate_compile_arguments(command)
