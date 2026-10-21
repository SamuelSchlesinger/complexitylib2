"""Regression fixtures for generated API documentation coverage (no Lean build)."""

from contextlib import closing, redirect_stdout
import io
import json
from pathlib import Path
import sqlite3
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
        self.database = self.docs.parent / "api-docs.db"
        root_patch = patch.object(check_docs, "ROOT", self.root)
        root_patch.start()
        self.addCleanup(root_patch.stop)
        for module in ("Complexity", "Complexity.Current"):
            self.write(self.root / (module.replace(".", "/") + ".lean"))
            self.write(self.page(module))
            self.write(self.module_data(module), "{}")
        with closing(sqlite3.connect(self.database)) as db, db:
            db.execute("CREATE TABLE modules (name TEXT PRIMARY KEY, source_url TEXT)")
            db.executemany("INSERT INTO modules (name) VALUES (?)",
                           [("Complexity",), ("Complexity.Current",)])
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

    def module_data(self, module):
        return self.docs.parent / "doc-data" / f"declaration-data-{module}.bmp"

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
            self.write(self.module_data(name), "{}")
            with closing(sqlite3.connect(self.database)) as db, db:
                db.execute("INSERT INTO modules (name) VALUES (?)", (name,))
        self.check()

    def test_obsolete_intermediate_data_only(self):
        for name in reversed(self.obsolete_modules):
            self.write(self.module_data(name), "{}")
        self.assert_failure("Obsolete modules in per-module declaration data: "
                            + ", ".join(self.obsolete_modules))
        for name in self.obsolete_modules:
            self.assertEqual(self.module_data(name).read_text(), "{}")

    def test_missing_intermediate_data(self):
        for name in ("Complexity", "Complexity.Current"):
            with self.subTest(module=name):
                self.module_data(name).unlink()
                self.assert_failure("Missing modules in per-module declaration data: " + name)
                self.write(self.module_data(name), "{}")

    def test_obsolete_database_modules_only(self):
        with closing(sqlite3.connect(self.database)) as db, db:
            db.executemany("INSERT INTO modules (name) VALUES (?)",
                           [(name,) for name in reversed(self.obsolete_modules)])
        before = self.database.read_bytes()
        self.assert_failure("Obsolete modules in documentation database: "
                            + ", ".join(self.obsolete_modules))
        self.assertEqual(self.database.read_bytes(), before)

    def test_missing_database_modules(self):
        for name in ("Complexity", "Complexity.Current"):
            with self.subTest(module=name):
                with closing(sqlite3.connect(self.database)) as db, db:
                    db.execute("DELETE FROM modules WHERE name = ?", (name,))
                self.assert_failure("Missing modules in documentation database: " + name)
                with closing(sqlite3.connect(self.database)) as db, db:
                    db.execute("INSERT INTO modules (name) VALUES (?)", (name,))

    def test_missing_database_is_not_created(self):
        self.database.unlink()
        self.assert_failure("Missing documentation database: api-docs.db")
        self.assertFalse(self.database.exists())

    def test_invalid_database_fails(self):
        self.database.write_bytes(b"not a database")
        with self.assertRaises(sqlite3.DatabaseError):
            self.check()

    def test_config_only_does_not_inspect_output(self):
        with patch.object(check_docs, "check_config") as config, \
                patch.object(check_docs, "check_output") as output, \
                patch("sys.argv", ["check_docs.py", "--config-only"]), \
                redirect_stdout(io.StringIO()):
            check_docs.main()
        config.assert_called_once_with()
        output.assert_not_called()

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
