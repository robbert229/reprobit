"""The identity of one classic translation unit.

A unit is one compile: its terminal target, the CMake target that compiles
it, its source file and whether the compile has debug information (``/Zi``).
Every record a unit holds -- interventions, expected observations -- was made
by observing that compile's objects, and a compile without ``/Zi`` writes
different objects: no ``.debug$S`` or ``.debug$T``, no type-server PDB.  So
the debug format is part of the identity, and dropping or adding ``/Zi``
gives the unit a new identity under which the old records are never found.

A compile with ``/Zi`` keeps the identity it had before this distinction
existed, so committed projects keep their ids.
"""

from __future__ import annotations

from reprobit.model import Digest
from reprobit.strict_json import canonical_json


def translation_unit_id(
    *,
    target_id: str,
    build_target: str,
    source: str,
    debug_information: bool,
) -> str:
    """Return ``tu.<24 hex>`` for one compile (see the module docstring)."""

    material: dict[str, object] = {
        "schema": 1,
        "target": target_id,
        "build_target": build_target,
        "source": source,
    }
    if not debug_information:
        material["debug_information"] = False
    return f"tu.{Digest.from_bytes(canonical_json(material)).value[:24]}"


def debug_format_phrase(debug_information: bool) -> str:
    """``with /Zi`` or ``without /Zi``, for messages."""

    return "with /Zi" if debug_information else "without /Zi"


__all__ = ["debug_format_phrase", "translation_unit_id"]
