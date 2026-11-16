"""Classic compiler algorithms: SIB base/index operand order."""

from __future__ import annotations

from typing import Any

from reprobit.binary import require

from .foundation import require_payload_free_declaration
from .register_semantics import _IA32_REGISTER_NUMBERS, decode_ia32_bijection_body

SIB_OPERAND_SWAP_KIND = "sib_base_index_swap_v1"
_ESP = _IA32_REGISTER_NUMBERS["esp"]
_EBP = _IA32_REGISTER_NUMBERS["ebp"]


def apply_sib_operand_swaps(
    body: bytes,
    sites: list[dict[str, Any]],
    relocation_offsets: frozenset[int],
    context: str,
    relocations: dict[int, Any] | None = None,
    code_length: int | None = None,
) -> tuple[bytes, dict[str, Any]]:
    """Exchange the base and index registers of declared ``[base + index]`` operands.

    With a scale of one, ``base + index + disp`` is commutative, so an operand
    that names its two registers the other way round addresses the same
    memory (or forms the same ``lea`` value).  The proof admits only that case:
    a SIB byte with scale 1, a real base (not the disp32-only form) and a real
    index, neither of them ESP or EBP (whose role as a base selects SS rather
    than DS), and a SIB byte under no relocation.  Only the SIB byte changes;
    the image is re-decoded to the same instruction grid, opcodes, flow and
    register reads and writes.
    """

    require_payload_free_declaration(sites, f"{context} SIB swap declaration")
    require(bool(sites), f"{context}: no SIB swap is declared")
    body = bytes(body)
    instructions = decode_ia32_bijection_body(body, context, relocations, code_length)
    by_offset = {item["offset"]: item for item in instructions}
    image = bytearray(body)
    proved = []
    previous = -1
    for index, site in enumerate(sites):
        site_context = f"{context} site {index}"
        require(
            isinstance(site, dict)
            and set(site) == {"instruction_offset", "expected_rewritten_offsets"},
            f"{site_context}: declaration keys differ",
        )
        offset = site["instruction_offset"]
        require(
            type(offset) is int and offset > previous and offset in by_offset,
            f"{site_context}: not an instruction boundary, or sites are unsorted",
        )
        previous = offset
        item = by_offset[offset]
        encoding = item["encoding"]
        require(
            encoding is not None and encoding["sib_at"] is not None,
            f"{site_context}: the instruction has no SIB byte",
        )
        sib_at = encoding["sib_at"]
        sib = body[sib_at]
        scale, sib_index, base = sib >> 6, sib >> 3 & 7, sib & 7
        require(scale == 0, f"{site_context}: the index is scaled")
        require(sib_index != _ESP, f"{site_context}: the operand has no index register")
        require(
            not (encoding["mode"] == 0 and base == _EBP),
            f"{site_context}: the operand has no base register (disp32 form)",
        )
        require(
            _ESP not in (base, sib_index) and _EBP not in (base, sib_index),
            f"{site_context}: ESP or EBP selects the stack segment",
        )
        require(base != sib_index, f"{site_context}: base and index are the same register")
        require(sib_at not in relocation_offsets, f"{site_context}: the SIB byte is relocated")
        image[sib_at] = sib_index | base << 3
        require(
            site["expected_rewritten_offsets"] == [sib_at],
            f"{site_context}: the rewritten byte differs from its declaration",
        )
        proved.append({"instruction_offset": offset, "sib_at": sib_at})
    output = bytes(image)
    rewritten = decode_ia32_bijection_body(output, f"{context} image", relocations, code_length)
    require(
        [(item["offset"], item["length"]) for item in rewritten]
        == [(item["offset"], item["length"]) for item in instructions],
        f"{context}: the image changed an instruction boundary",
    )
    for left, right in zip(rewritten, instructions, strict=True):
        require(
            left["opcode"] == right["opcode"]
            and left["flow"] == right["flow"]
            and left["target"] == right["target"]
            and left["reads"] == right["reads"]
            and left["writes"] == right["writes"],
            f"{context}: the image changed the instruction at {right['offset']} beyond its SIB",
        )
    changed = sorted(index for index in range(len(body)) if body[index] != output[index])
    require(
        changed == sorted(site["sib_at"] for site in proved),
        f"{context}: the image changed a byte no site names",
    )
    return output, {"kind": SIB_OPERAND_SWAP_KIND, "sites": proved, "rewritten_offsets": changed}


__all__ = ["SIB_OPERAND_SWAP_KIND", "apply_sib_operand_swaps"]
