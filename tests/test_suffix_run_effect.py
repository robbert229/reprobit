"""An extern run after a unit's final line, compiled by MSVC 5.0.

MSVC 5.0 numbers the back end's inline temporaries after the unit's last
declaration, so a run of inert ``extern int`` declarations after the final
line changes the code of a function whose inlined helpers keep a temporary,
and only that function.  These tests compile a small unit with and without
such a run and check what `reprobit.suffix_run_effect` and the build make of
the two objects.
"""

from __future__ import annotations

import os
import shutil
import subprocess
from pathlib import Path
from types import SimpleNamespace
from typing import Any, cast

import pytest

from reprobit.classic.semantic_contracts import (
    _CLASSIC_SEMANTIC_ISSUER,
    _ClassicDonorSemanticMaterial,
)
from reprobit.classic_donors import DonorCompileRequest, prepare_donor_compile_request
from reprobit.classic_orchestration import (
    ClassicPreparedDonor,
    ClassicPreparedUnit,
    _require_suffix_run_effects,
    compose_classic_unit,
)
from reprobit.classic_project import ClassicProjectError
from reprobit.coff_format import CoffObject
from reprobit.discovery_authoring import AuthoredClassicRecord, build_extern_run_donor
from reprobit.discovery_grind import measured_changed_functions
from reprobit.model import Digest
from reprobit.schema import ClassicTranslationUnitPlan
from reprobit.suffix_run_effect import (
    SuffixRunEffectError,
    require_suffix_run_effect,
    suffix_run_changed_functions,
)

_ROOT = os.environ.get("REPROBIT_MSVC_5_0_RTM_ROOT", "")
_CL = Path(_ROOT) / "wine" / "x86" / "cl" if _ROOT else Path()

pytestmark = [
    pytest.mark.msvc50,
    pytest.mark.skipif(
        not _ROOT
        or not _CL.is_file()
        or (shutil.which("wine") is None and shutil.which("wine64") is None),
        reason="requires REPROBIT_MSVC_5_0_RTM_ROOT with its Wine wrappers",
    ),
]

# norm_all inlines norm3 four times, each keeping a temporary; plain_sum keeps
# none.  510 declarations after the final line move the temporaries'
# numbering far enough to change norm_all's code (508 do not).
_UNIT = b"""\
#include <math.h>
typedef struct { float x, y, z; } V3;
static __inline float dot3(V3* a, V3* b) { return a->x * b->x + a->y * b->y + a->z * b->z; }
static __inline float len3(V3* v) { return (float)sqrt(dot3(v, v)); }
static __inline V3* scale3(V3* r, V3* a, float f)
{
    r->x = a->x * f;
    r->y = a->y * f;
    r->z = a->z * f;
    return r;
}
static __inline V3* norm3(V3* r) { return scale3(r, r, 1.0f / len3(r)); }
void norm_all(V3* a, V3* b, V3* c, V3* d, int n)
{
    int i;
    for (i = 0; i < n; i++) {
        norm3(&a[i]);
        norm3(&b[i]);
        norm3(&c[i]);
        norm3(&d[i]);
    }
}
int plain_sum(int* p, int n)
{
    int i, s = 0;
    for (i = 0; i < n; i++) s += p[i];
    return s;
}
"""
_SOURCE = "src/unit.c"
_RUN = 510
_PLAN = ClassicTranslationUnitPlan(
    id="tu.unit",
    target_id="program",
    build_target="program",
    source=_SOURCE,
    source_digest=Digest.from_bytes(_UNIT),
)


def _donor(changed_functions: tuple[str, ...], count: int = _RUN) -> AuthoredClassicRecord:
    return build_extern_run_donor(
        target_id="program",
        translation_unit_id="tu.unit",
        build_target="program",
        header_prefix="ReproBitPad",
        header_count=count,
        seat_prefix="ReproBitPadSeat",
        seat_count=0,
        width=3,
        header_placement="suffix",
        changed_functions=changed_functions,
    )


def _request(record: AuthoredClassicRecord) -> DonorCompileRequest:
    return prepare_donor_compile_request(
        record.intervention,
        source_path=_SOURCE,
        clean_source=_UNIT,
        effective_source=_UNIT,
        receipts=[record.receipt],
    )


# /O2 implies /Gy; its other parts leave every function in one plain .text section.
_GY = ("/O2", "/Gy")
_PLAIN_TEXT = ("/Og", "/Oi", "/Ot", "/Oy", "/Ob1", "/Gs")


def _compile(directory: Path, name: str, source: bytes, *arguments: str) -> bytes:
    directory.mkdir(parents=True, exist_ok=True)
    (directory / f"{name}.c").write_bytes(source)
    completed = subprocess.run(
        (str(_CL), "/nologo", "/c", "/Zi", *arguments, f"{name}.c", f"/Fd{name}.pdb"),
        cwd=directory,
        check=False,
        capture_output=True,
        text=True,
        timeout=300,
    )
    assert completed.returncode == 0, completed.stdout + completed.stderr
    return (directory / f"{name}.obj").read_bytes()


@pytest.fixture(scope="module")
def objects(tmp_path_factory: pytest.TempPathFactory) -> tuple[bytes, bytes, frozenset[str]]:
    """The unit's seed compile and its suffix donor's compile, and the run's names."""

    arguments = _GY
    directory = tmp_path_factory.mktemp("suffix")
    donor = _request(_donor(("_norm_all",)))
    rendered = donor.logical_outputs[_SOURCE]
    assert rendered.startswith(_UNIT)
    assert rendered.endswith(b"extern int ReproBitPad509;\n")
    return (
        _compile(directory, "seed", _UNIT, *arguments),
        _compile(directory, "donor", rendered, *arguments),
        donor.carrier_identifiers,
    )


def test_a_suffix_run_changes_one_functions_code_and_leaves_the_other_identical(
    objects: tuple[bytes, bytes, frozenset[str]],
) -> None:
    seed, donor, identifiers = objects

    assert suffix_run_changed_functions(seed, donor) == ("_norm_all",)
    require_suffix_run_effect(
        seed, donor, changed_functions=("_norm_all",), carrier_identifiers=identifiers
    )
    # The run adds no code or data: no symbol of the donor is one of its names.
    assert not any("ReproBitPad" in symbol["name"] for symbol in CoffObject(donor).symbols.values())


def test_a_unit_compiled_without_gy_cannot_be_checked(tmp_path: Path) -> None:
    # Without /Gy a run of 600 changes norm_all (520 to 999 do).
    rendered = _request(_donor(("_norm_all",), count=600)).logical_outputs[_SOURCE]

    seed = _compile(tmp_path, "seed", _UNIT, *_PLAIN_TEXT)
    donor = _compile(tmp_path, "donor", rendered, *_PLAIN_TEXT)

    # Both functions share one plain .text section: plain_sum cannot be read alone.
    with pytest.raises(SuffixRunEffectError, match="does not begin its own section"):
        suffix_run_changed_functions(seed, donor)


def test_a_shorter_suffix_run_changes_nothing(tmp_path: Path) -> None:
    rendered = _request(_donor((), count=508)).logical_outputs[_SOURCE]

    seed = _compile(tmp_path, "seed", _UNIT, *_GY)
    donor = _compile(tmp_path, "donor", rendered, *_GY)

    # The run still renumbers norm_all's temporaries ($T200 against $T708):
    # the same code with the same statics in the same places.
    assert suffix_run_changed_functions(seed, donor) == ()


@pytest.mark.parametrize(
    ("stated", "message"),
    [
        ((), "does not list: '_norm_all'"),
        (("_plain_sum",), "does not list: '_norm_all'"),
        (("_norm_all", "_plain_sum"), "leaves byte-identical: '_plain_sum'"),
    ],
)
def test_a_statement_other_than_the_changed_functions_is_refused(
    objects: tuple[bytes, bytes, frozenset[str]], stated: tuple[str, ...], message: str
) -> None:
    seed, donor, identifiers = objects

    with pytest.raises(SuffixRunEffectError, match=message):
        require_suffix_run_effect(
            seed, donor, changed_functions=stated, carrier_identifiers=identifiers
        )


def test_grind_measures_the_functions_a_suffix_run_changes(
    objects: tuple[bytes, bytes, frozenset[str]],
) -> None:
    seed, donor, _identifiers = objects
    probe = _donor(())

    assert measured_changed_functions(probe, seed_object=seed, donor_object=donor) == ("_norm_all",)


def _unit(record: AuthoredClassicRecord) -> ClassicPreparedUnit:
    return ClassicPreparedUnit(
        _PLAN,
        (ClassicPreparedDonor(record.intervention, _request(record)),),
        (),
        (),
        (),
        (record.receipt,),
    )


def _material(record: AuthoredClassicRecord, donor_object: bytes) -> Any:
    return _ClassicDonorSemanticMaterial(
        intervention=record.intervention,
        donor_object=donor_object,
        source_inputs={},
        compiler_statement={"schema": 1},
        _issuer=_CLASSIC_SEMANTIC_ISSUER,
    )


def test_the_build_admits_a_suffix_run_that_states_what_it_changes(
    objects: tuple[bytes, bytes, frozenset[str]],
) -> None:
    seed, donor, _identifiers = objects
    record = _donor(("_norm_all",))

    _require_suffix_run_effects(_unit(record), seed, {record.intervention.id: donor})


def test_the_build_refuses_a_suffix_run_that_changes_an_unlisted_function(
    objects: tuple[bytes, bytes, frozenset[str]],
) -> None:
    seed, donor, _identifiers = objects
    record = _donor(())

    with pytest.raises(ClassicProjectError, match="does not list: '_norm_all'"):
        compose_classic_unit(
            _unit(record),
            seed_object=seed,
            donor_materials={record.intervention.id: _material(record, donor)},
            seed_source=_UNIT,
        )


def test_the_build_refuses_a_suffix_run_whose_objects_it_cannot_read(
    objects: tuple[bytes, bytes, frozenset[str]],
) -> None:
    seed, _donor_object, _identifiers = objects
    record = _donor(("_norm_all",))

    with pytest.raises(ClassicProjectError, match="cannot be read"):
        _require_suffix_run_effects(_unit(record), seed, {record.intervention.id: b"not an object"})


def test_the_build_leaves_other_extern_run_placements_alone() -> None:
    record = build_extern_run_donor(
        target_id="program",
        translation_unit_id="tu.unit",
        build_target="program",
        header_prefix="ReproBitPad",
        header_count=3,
        seat_prefix="ReproBitPadSeat",
        seat_count=0,
        width=3,
    )
    unit = ClassicPreparedUnit(
        _PLAN,
        (
            ClassicPreparedDonor(
                record.intervention,
                cast(Any, SimpleNamespace(carrier_identifiers=frozenset())),
            ),
        ),
        (),
        (),
        (),
        (record.receipt,),
    )

    _require_suffix_run_effects(unit, b"", {record.intervention.id: b""})
