"""Regression fixtures for generated API documentation coverage (no Lean build)."""

from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import check_docs


class CheckOutputTests(unittest.TestCase):
    # Both names survived in a reused doc-gen4 cache after their sources were removed.
    obsolete_modules = (
        "Complexity.Computability.Circuit.Basic",
        "Complexity.Computability.Machines.Turing.MultiTape.Plumbing.WriteWord",
    )

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.docs = self.root / "docbuild/.lake/build/doc"
        root_patch = patch.object(check_docs, "ROOT", self.root)
        root_patch.start()
        self.addCleanup(root_patch.stop)
        for module in ("Complexity", "Complexity.Current"):
            self.write(self.root / (module.replace(".", "/") + ".lean"))
            self.write(self.page(module))
        for name in ("index.html", "search.html", "search.js", "declaration-data.js",
                     "references.html", "references.bib", "find/index.html"):
            self.write(self.docs / name)
        self.index = {"modules": {"Complexity": {}, "Complexity.Current": {}},
                      "declarations": {}}
        for name in ("Cslib.Complexity.CookLevin.SAT_npComplete",
                     "Cslib.Complexity.NP_eq_PCP_log",
                     "Cslib.Crypto.OneWay.exists_pseudorandomFunction"):
            self.index["declarations"][name] = {"docLink": "./Complexity/Current.html#" + name}
        self.write(self.page("Complexity.Current"), "\n".join(
            f'<div id="{name}"></div>' for name in self.index["declarations"]))

    def write(self, path, text=""):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def page(self, module):
        return self.docs / (module.replace(".", "/") + ".html")

    def check(self):
        self.write(self.docs / "declarations/declaration-data.bmp", json.dumps(self.index))
        with redirect_stdout(io.StringIO()):
            check_docs.check_output()

    def assert_failure(self, message):
        with self.assertRaises(ValueError) as error:
            self.check()
        self.assertEqual(str(error.exception), message)

    def test_current_modules_and_other_roots_pass(self):
        for name in ("Cslib.Extra", "Mathlib.Extra", "ComplexityTests", "ComplexityExtra.Old"):
            self.index["modules"][name] = {}
            self.write(self.page(name))
        self.check()

    def test_obsolete_index_only(self):
        for name in reversed(self.obsolete_modules):
            self.index["modules"][name] = {}
        self.assert_failure("Obsolete modules in search index: " + ", ".join(self.obsolete_modules))

    def test_obsolete_pages_only(self):
        for name in reversed(self.obsolete_modules):
            self.write(self.page(name))
        self.assert_failure("Obsolete module pages: " + ", ".join(self.obsolete_modules))
        for name in self.obsolete_modules:
            self.assertTrue(self.page(name).is_file())

    def test_obsolete_index_and_page(self):
        name = self.obsolete_modules[0]
        self.index["modules"][name] = {}
        self.write(self.page(name))
        self.assert_failure("Obsolete modules in search index: " + name)
        del self.index["modules"][name]
        self.assert_failure("Obsolete module pages: " + name)

    def test_missing_current_module(self):
        del self.index["modules"]["Complexity.Current"]
        self.assert_failure("Missing module in search index: Complexity.Current")

    def test_missing_current_page(self):
        self.page("Complexity.Current").unlink()
        self.assert_failure("Missing module page: Complexity.Current")

    def test_missing_root_module(self):
        del self.index["modules"]["Complexity"]
        self.assert_failure("Missing module in search index: Complexity")

    def test_missing_root_page(self):
        self.page("Complexity").unlink()
        self.assert_failure("Missing module page: Complexity")

    def test_missing_theorem_anchor(self):
        self.write(self.page("Complexity.Current"))
        self.assert_failure("Missing theorem anchor: Cslib.Complexity.CookLevin.SAT_npComplete")


if __name__ == "__main__":
    unittest.main()
