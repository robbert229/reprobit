"""The register-bijection table's byte moffs forms (mov al, moffs8 / mov moffs8, al)."""

from __future__ import annotations

import unittest

import reprobit.classic.register_semantics as register_algorithms
import reprobit.classic.scheduling_dependence as scheduling_dependence
from reprobit.binary import ByteIdentityError

RELOCATION = {1: {"width": 4, "target": "_g"}}
EAX = {"eax.l", "eax.h", "eax.u"}


def decode(hex_bytes: str) -> dict:
    return register_algorithms.decode_ia32_bijection_instruction(
        bytes.fromhex(hex_bytes), 0, "decode", RELOCATION
    )


class ByteMoffsFormTests(unittest.TestCase):
    def test_load_byte_reads_and_writes_all_of_eax(self):
        # only AL changes, so the upper bytes must stay live through it
        entry = decode("a000000000")
        self.assertEqual(entry["length"], 5)
        self.assertEqual(set(entry["read_atoms"]), EAX)
        self.assertEqual(set(entry["write_atoms"]), EAX)
        self.assertEqual(set(entry["frozen"]), {"eax"})

    def test_store_byte_reads_eax_and_writes_no_register(self):
        entry = decode("a200000000")
        self.assertEqual(entry["length"], 5)
        self.assertEqual(set(entry["read_atoms"]), EAX)
        self.assertEqual(set(entry["write_atoms"]), set())
        self.assertEqual(set(entry["frozen"]), {"eax"})

    def test_byte_forms_match_the_dword_forms_register_model(self):
        self.assertEqual(decode("a000000000")["frozen"], decode("a100000000")["frozen"])
        self.assertEqual(decode("a200000000")["read_atoms"], decode("a300000000")["read_atoms"])

    def test_the_schedule_table_still_refuses_moffs_forms(self):
        # no memory operand is modelled for moffs, so reordering must stay closed
        for hex_bytes in ("a000000000", "a200000000"):
            with self.assertRaises(ByteIdentityError):
                scheduling_dependence.ia32_schedule_dependence_edges([decode(hex_bytes)], "dag")


if __name__ == "__main__":
    unittest.main()
