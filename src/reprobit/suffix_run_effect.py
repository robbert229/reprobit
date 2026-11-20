"""What an extern run after a unit's final line changes: the functions whose code differs.

MSVC 5.0 numbers the back end's inline temporaries after the unit's last
declaration.  A run of inert ``extern int`` declarations after the unit's
final line (an extern-run pair whose header run is a suffix) precedes no
front-end symbol of the unit, yet it moves that numbering, so it may change
the code of any function -- and of more than the one a grind targets.

Such a record therefore states the functions it changes
(``changed_functions``), and this module checks the statement against two
fresh objects: the unit compiled without the run (the seed) and with it (the
donor).  Both objects must define the same functions, each readable one by
one: each function begins its own COMDAT section, as ``/Gy`` writes it (a
function in a plain ``.text`` section cannot be read alone and is refused).
A function keeps its code when its body is byte-identical to the seed's and
its relocations are the seed's record by record: the same offset, kind, width
and addend, the same target symbol and the same target section.  The one name that
may differ is a counter-numbered file static's serial (``$T200`` against
``$T708``: the run renumbers the temporaries it precedes), the relation
`reprobit.coff_format.require_mosaic_relocation_compatibility` admits for two
compiles of one unit whose declaration counts differ; such a static still has
the same section, value, type and storage.  The stated functions must be
exactly those whose code differs: every other function is byte-identical to
the seed's once linked.  A run declaration names no symbol of the donor
object, so the run adds no code or data.  An object that cannot be read
function by function is refused.
"""

from __future__ import annotations

import re
from collections.abc import Collection
from dataclasses import dataclass

from reprobit.binary import ByteIdentityError
from reprobit.coff_format import (
    CoffObject,
    CoffSection,
    coff_body,
    require_mosaic_relocation_compatibility,
)

_FUNCTION_TYPE = 0x20
_FUNCTION_STORAGE = (2, 3)
_IMAGE_SCN_CNT_CODE = 0x20
_NAME_TOKEN = re.compile(r"[A-Za-z0-9_]+")


class SuffixRunEffectError(ValueError):
    """A suffix extern run's effect cannot be checked, or differs from its statement."""


@dataclass(frozen=True, slots=True)
class _Functions:
    coff: CoffObject
    sections: dict[str, CoffSection]


def _functions(data: bytes, label: str) -> _Functions:
    """Every function the object defines, by name, with its section."""

    try:
        coff = CoffObject(data)
        sections: dict[str, CoffSection] = {}
        for symbol in coff.symbols.values():
            if (
                symbol["type"] != _FUNCTION_TYPE
                or symbol["storage"] not in _FUNCTION_STORAGE
                or symbol["section"] <= 0
            ):
                continue
            name = str(symbol["name"])
            if symbol["section"] > len(coff.sections) or symbol["value"] != 0:
                raise SuffixRunEffectError(
                    f"the {label} object's function {name!r} does not begin its own section"
                )
            section = coff.sections[symbol["section"] - 1]
            if not section["characteristics"] & _IMAGE_SCN_CNT_CODE or not section["raw_size"]:
                raise SuffixRunEffectError(
                    f"the {label} object's function {name!r} lies outside a code section"
                )
            if name in sections:
                raise SuffixRunEffectError(f"the {label} object defines {name!r} twice")
            sections[name] = section
    except SuffixRunEffectError:
        raise
    except (ByteIdentityError, KeyError, UnicodeError, ValueError) as exc:
        raise SuffixRunEffectError(
            f"the {label} object cannot be read function by function: {exc}"
        ) from exc
    if not sections:
        raise SuffixRunEffectError(f"the {label} object defines no function")
    return _Functions(coff, sections)


def _same_code(seed: _Functions, donor: _Functions, name: str) -> bool:
    seed_section = seed.sections[name]
    donor_section = donor.sections[name]
    if coff_body(seed.coff, seed_section) != coff_body(donor.coff, donor_section):
        return False
    try:
        require_mosaic_relocation_compatibility(
            seed.coff,
            seed_section,
            donor.coff,
            donor_section,
            f"function {name!r}",
            static_serials=True,
        )
    except ByteIdentityError:
        return False
    return True


def suffix_run_changed_functions(seed_object: bytes, donor_object: bytes) -> tuple[str, ...]:
    """The functions whose code the donor compiles differently from the seed, sorted.

    Raises `SuffixRunEffectError` when either object cannot be read function
    by function or the two define different functions.
    """

    seed = _functions(seed_object, "seed")
    donor = _functions(donor_object, "donor")
    if set(seed.sections) != set(donor.sections):
        added = sorted(set(donor.sections) - set(seed.sections))
        removed = sorted(set(seed.sections) - set(donor.sections))
        raise SuffixRunEffectError(
            f"the suffix run changes which functions the unit defines; added={added[:8]}, "
            f"removed={removed[:8]}"
        )
    return tuple(sorted(name for name in seed.sections if not _same_code(seed, donor, name)))


def _require_no_run_symbol(donor_object: bytes, carrier_identifiers: Collection[str]) -> None:
    identifiers = frozenset(carrier_identifiers)
    if not identifiers:
        raise SuffixRunEffectError("the suffix run names no declarations")
    try:
        coff = CoffObject(donor_object)
    except (ByteIdentityError, KeyError, UnicodeError, ValueError) as exc:
        raise SuffixRunEffectError(f"the donor object cannot be read: {exc}") from exc
    for symbol in coff.symbols.values():
        name = str(symbol["name"])
        if any(
            token in identifiers or token.lstrip("_") in identifiers
            for token in _NAME_TOKEN.findall(name)
        ):
            raise SuffixRunEffectError(
                f"the donor object has a symbol {name!r} for a run declaration; "
                "the run must add no code or data"
            )


def require_suffix_run_effect(
    seed_object: bytes,
    donor_object: bytes,
    *,
    changed_functions: Collection[str],
    carrier_identifiers: Collection[str],
) -> None:
    """Refuse a suffix run whose donor differs from the seed other than as its record states.

    ``changed_functions`` is the record's statement and ``carrier_identifiers``
    the run's declared names.  The statement must name exactly the functions
    whose code differs; every other function must be byte-identical to the
    seed's, and no donor symbol may be one of the run's declarations.
    """

    _require_no_run_symbol(donor_object, carrier_identifiers)
    changed = set(suffix_run_changed_functions(seed_object, donor_object))
    stated = set(changed_functions)
    unlisted = sorted(changed - stated)
    if unlisted:
        raise SuffixRunEffectError(
            "the suffix run changes functions its record does not list: "
            + ", ".join(repr(name) for name in unlisted[:8])
        )
    unchanged = sorted(stated - changed)
    if unchanged:
        raise SuffixRunEffectError(
            "the suffix run's record lists functions it leaves byte-identical: "
            + ", ".join(repr(name) for name in unchanged[:8])
        )


__all__ = [
    "SuffixRunEffectError",
    "require_suffix_run_effect",
    "suffix_run_changed_functions",
]
