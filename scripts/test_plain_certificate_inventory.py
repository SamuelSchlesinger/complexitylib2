"""Regression checks for inventory completeness, snapshot coverage and result accounting."""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

spec = importlib.util.spec_from_file_location(
    "plain_certificate_inventory", Path(__file__).with_name("plain_certificate_inventory.py"))
assert spec and spec.loader
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


def record(name="cert", **kw):
    return {"declaration": {"name": name}, "status": "compared",
            "tidy_holdout": {"status": "success", "heartbeats_raw": 37},
            "plain_holdout": {"status": "failed", "heartbeats_raw": 41}, **kw}


class InventoryTests(unittest.TestCase):
    def test_all_libraries_and_custom_srcdir(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            (root / "lakefile.toml").write_text('''[[lean_lib]]
name = "Complexity"
[[lean_lib]]
name = "ComplexityTests"
[[lean_lib]]
name = "ComplexityAbstracts"
srcDir = "abstracts"
''')
            for name in ["Complexity.lean", "Complexity/A.lean", "ComplexityTests/Captured.lean",
                         "abstracts/ComplexityAbstracts/Bridge.lean"]:
                p = root / name
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text("-- fixture\n")
            sources = runner.discover_sources(root)
            self.assertEqual(set(sources), {"Complexity", "Complexity.A",
                                           "ComplexityTests.Captured", "ComplexityAbstracts.Bridge"})
            with self.assertRaises(FileNotFoundError):
                runner.validate_ileans(root, sources)
            for module in sources:
                p = root / ".lake/build/lib/lean" / Path(*module.split("."))
                p = p.with_suffix(".ilean")
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_text(json.dumps({"version": 5, "module": module}))
            runner.validate_ileans(root, sources)
            p.write_text(json.dumps({"version": 4, "module": module}))
            with self.assertRaisesRegex(ValueError, "unsupported"):
                runner.validate_ileans(root, sources)

    def test_truncation_is_not_coverage(self):
        with self.assertRaisesRegex(ValueError, "truncated"):
            runner.validate_rows([{"inventory_total": 2, "limit": 0}, record()])

    def test_debug_subset_is_explicitly_incomplete(self):
        summary = runner.validate_rows([{"inventory_total": 5, "limit": 1}, record()])
        self.assertFalse(summary["inventory_complete"])
        self.assertEqual(summary["inventory_total"], 5)

    def test_duplicates_cannot_fill_missing_rows(self):
        with self.assertRaisesRegex(ValueError, "duplicate"):
            runner.validate_rows([{"inventory_total": 2, "limit": 0}, record(), record()])

    def test_unsupported_exact_bounds_remain_visible(self):
        row = {"declaration": {"name": "exact"}, "status": "unsupported_tidy",
               "residual_tidy": ["ComputableTidilyInTimeAndSpace"]}
        summary = runner.validate_rows([{"inventory_total": 1, "limit": 0}, row])
        self.assertTrue(summary["inventory_complete"])
        self.assertEqual(summary["statuses"], {"unsupported_tidy": 1})
        self.assertEqual(summary["holdout_pairs"], {})

    def test_registration_does_not_count_as_synthesis(self):
        row = record(plain_registration={"status": "success", "heartbeats_raw": 2})
        summary = runner.validate_rows([{"inventory_total": 1, "limit": 0}, row])
        self.assertEqual(summary["registration_probes"], 1)
        self.assertEqual(summary["holdout_pairs"], {"tidy:success/plain:failed": 1})

    def test_unknown_status_fails_closed(self):
        with self.assertRaises(ValueError):
            runner.validate_rows([{"inventory_total": 1, "limit": 0}, record(status="skipped")])


if __name__ == "__main__":
    unittest.main()
