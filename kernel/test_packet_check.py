#!/usr/bin/env python3
"""Unit tests for kernel/packet_check.py."""
from pathlib import Path
import json
import tempfile
import unittest

import packet_check


class PacketCheckTests(unittest.TestCase):
    def test_select_and_order_modules_topological(self):
        rows = [
            {"id": "M000002", "packet": "P9999", "module": "Foo.B", "depth": 1, "imports": ["M000001"]},
            {"id": "M000001", "packet": "P9999", "module": "Foo.A", "depth": 0, "imports": []},
            {"id": "M000003", "packet": "P9998", "module": "Other.C", "depth": 0, "imports": []},
        ]
        ordered = packet_check.select_and_order_modules(rows, "P9999")
        self.assertEqual([r["id"] for r in ordered], ["M000001", "M000002"])

    def test_select_rejects_unknown_and_cycles(self):
        rows = [
            {"id": "M000001", "packet": "P9999", "module": "Foo.A", "depth": 1, "imports": ["M000002"]},
            {"id": "M000002", "packet": "P9999", "module": "Foo.B", "depth": 1, "imports": ["M000001"]},
        ]
        with self.assertRaises(packet_check.CheckFailure):
            packet_check.select_and_order_modules(rows, "P0000")
        with self.assertRaises(packet_check.CheckFailure):
            packet_check.select_and_order_modules(rows, "P9999")

    def test_lean_flags_include_fields_heartbeats_override(self):
        normal = packet_check.lean_flags_for_module("CompanionTheory.Foo", 4)
        self.assertNotIn("-DsynthInstance.maxHeartbeats=400000", normal)
        local_f = packet_check.lean_flags_for_module("GroundTheory.LocalFields.Bar", 4)
        global_f = packet_check.lean_flags_for_module("GroundTheory.GlobalFields.Baz", 4)
        self.assertIn("-DsynthInstance.maxHeartbeats=400000", local_f)
        self.assertIn("-DsynthInstance.maxHeartbeats=400000", global_f)

    def test_count_export_records_strict_and_extracts_axioms(self):
        lines = [
            {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"}, "format": {"version": "3.1.0"}}},
            {"in": 1, "str": {"pre": 0, "str": "propext"}},
            {"in": 2, "str": {"pre": 0, "str": "Classical"}},
            {"in": 3, "str": {"pre": 2, "str": "choice"}},
            {"il": 1, "succ": 0},
            {"ie": 0, "sort": 0},
            {"axiom": {"name": 1, "levelParams": [], "type": 0, "isUnsafe": False}},
            {"axiom": {"name": 3, "levelParams": [], "type": 0, "isUnsafe": False}},
            {"thm": {"name": 1, "levelParams": [], "type": 0, "value": 0, "all": [1]}},
            {"def": {"name": 1, "levelParams": [], "type": 0, "value": 0, "hints": "abbrev", "safety": "safe", "all": [1]}},
            {"inductive": {"types": [], "ctors": [], "recs": []}},
        ]
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "sample.ndjson"
            p.write_text("\n".join(json.dumps(x) for x in lines) + "\n", encoding="utf-8")
            res = packet_check.count_export_records(p)
        self.assertEqual(res["total_declarations"], 5)
        self.assertEqual(res["counts"]["axiom"], 2)
        self.assertEqual(res["counts"]["thm"], 1)
        self.assertEqual(res["counts"]["def"], 1)
        self.assertEqual(res["counts"]["inductive"], 1)
        self.assertEqual(res["axioms"], ["propext", "Classical.choice"])

    def test_count_export_records_rejects_unrecognized_single_key(self):
        lines = [
            {"meta": {"format": {"version": "3.1.0"}}},
            {"ax": {"name": 1}},
        ]
        with tempfile.TemporaryDirectory() as tmp:
            p = Path(tmp) / "bad.ndjson"
            p.write_text("\n".join(json.dumps(x) for x in lines) + "\n", encoding="utf-8")
            with self.assertRaises(packet_check.CheckFailure):
                packet_check.count_export_records(p)

    def test_nanoda_config_is_strict(self):
        cfg = packet_check.make_nanoda_config(Path("/tmp/P0001.ndjson"), 4)
        self.assertTrue(cfg["unpermitted_axiom_hard_error"])
        self.assertEqual(cfg["num_threads"], 4)
        self.assertEqual(
            cfg["permitted_axioms"],
            ["propext", "Classical.choice", "Quot.sound", "Lean.trustCompiler"],
        )


if __name__ == "__main__":
    unittest.main()
