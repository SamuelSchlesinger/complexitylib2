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

    def artifact_bytes(self):
        return {str(path.relative_to(self.docs.parent)): path.read_bytes()
                for path in self.docs.parent.rglob("*") if path.is_file()}

    def test_wal_database_does_not_create_sidecars(self):
        with closing(sqlite3.connect(self.database)) as db:
            db.execute("PRAGMA journal_mode=WAL")
        self.check()  # Also writes the fixture's assembled index before the snapshot.
        self.assertFalse(self.database.with_name("api-docs.db-wal").exists())
        self.assertFalse(self.database.with_name("api-docs.db-shm").exists())
        before = self.artifact_bytes()
        self.check()
        self.assertEqual(self.artifact_bytes(), before)

    def test_committed_wal_rows_are_checked_without_mutation(self):
        # Keep a connection open so committed changes remain solely in the WAL.
        with closing(sqlite3.connect(self.database)) as db:
            db.execute("PRAGMA journal_mode=WAL")
            db.execute("PRAGMA wal_autocheckpoint=0")
            self.check()
            db.execute("INSERT INTO modules (name) VALUES ('Complexity.Removed')")
            db.commit()
            before = self.artifact_bytes()
            self.assert_failure("Obsolete modules in documentation database: Complexity.Removed")
            self.assertEqual(self.artifact_bytes(), before)
            db.execute("DELETE FROM modules WHERE name IN ('Complexity.Removed', 'Complexity')")
            db.commit()
            before = self.artifact_bytes()
            self.assert_failure("Missing modules in documentation database: Complexity")
            self.assertEqual(self.artifact_bytes(), before)

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


class CheckMarkdownDocsTests(unittest.TestCase):
    REAL_ROOT = Path(__file__).resolve().parents[1]

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.setup_valid_fixture()

    def write(self, rel_path, text=""):
        path = self.root / rel_path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def setup_valid_fixture(self):
        self.write("Complexity.lean",
                   "public import Complexity.Computability.Valid\n"
                   "public import Complexity.Computability.Sub.PartA\n"
                   "public import Complexity.Computability.Sub.PartB\n")
        self.write("Complexity/Computability/Valid.lean", "-- valid\n")
        self.write("Complexity/Computability/Sub/PartA.lean", "-- part A\n")
        self.write("Complexity/Computability/Sub/PartB.lean", "-- part B\n")
        self.write("README.md",
                   "# Complexitylib\n\n## Build and use\n\nSee [ROADMAP.md](ROADMAP.md).\n")
        self.write("ROADMAP.md",
                   "# Development roadmap\n\n"
                   "## Continuing priorities\n\n"
                   "See [Valid](Complexity/Computability/Valid.lean) and "
                   "[machine milestones](#machine-class-milestones).\n\n"
                   "## Jukna coverage\n\n"
                   "## Machine-class milestones\n\n"
                   "Back to [continuing priorities](#continuing-priorities).\n")
        self.write("AGENTS.md",
                   "# Project Instructions\n\n"
                   "## Working on changes\n\n"
                   "## Review cycle\n\n"
                   "See [CONTRIBUTING.md](CONTRIBUTING.md#ai-assistance-and-review).\n\n"
                   "## Staying current with upstream\n\n"
                   "## Proof hygiene\n\n"
                   "## Human-readable theorem index\n")
        self.write("CONTRIBUTING.md",
                   "# Contributing\n\n"
                   "## AI assistance and review\n\n"
                   "See [AGENTS.md](AGENTS.md#review-cycle) and [README](README.md#build-and-use).\n\n"
                   "## Documentation\n\n"
                   "## Maintaining the theorem index\n\n"
                   "## Upstreaming\n")
        self.write("UPSTREAM.md",
                   "# Upstream integration\n\n"
                   "See [AGENTS.md](AGENTS.md#staying-current-with-upstream), "
                   "`Complexity/Computability/Valid`, and "
                   "`Complexity/Computability/Sub/{PartA,PartB}`.\n"
                   "* **Renamed modules (historical).** `Computability/OldRemoved` became "
                   "`Complexity/Computability/Valid`.\n")
        self.write("paper/README.md",
                   "# Index of proved statements\n\n"
                   "See [ROADMAP.md](../ROADMAP.md) and "
                   "[AGENTS.md](../AGENTS.md#human-readable-theorem-index).\n")

    def test_live_repository_markdown_docs_pass(self):
        check_docs.check_markdown_docs(self.REAL_ROOT)

    def test_valid_fixture_passes(self):
        check_docs.check_markdown_docs(self.root)

    def test_self_test_and_markdown_only_flags_pass(self):
        with redirect_stdout(io.StringIO()):
            check_docs.run_self_test()
        with patch("sys.argv", ["check_docs.py", "--markdown-only"]), \
                redirect_stdout(io.StringIO()):
            check_docs.main()
        with patch("sys.argv", ["check_docs.py", "--self-test"]), \
                redirect_stdout(io.StringIO()):
            check_docs.main()

    def test_broken_local_file_link_fails(self):
        self.write("README.md", "# Complexitylib\n\nSee [Missing](Complexity/Missing.lean).\n")
        with self.assertRaisesRegex(ValueError, "README.md:3: missing link target: Complexity/Missing.lean"):
            check_docs.check_markdown_docs(self.root)

    def test_broken_same_file_heading_anchor_fails(self):
        self.write("ROADMAP.md", "# Development roadmap\n\nSee [bad](#nonexistent-anchor).\n")
        with self.assertRaisesRegex(ValueError, "ROADMAP.md:3: missing heading anchor #nonexistent-anchor"):
            check_docs.check_markdown_docs(self.root)

    def test_broken_cross_file_heading_anchor_fails(self):
        self.write("CONTRIBUTING.md",
                   "# Contributing\n\n## AI assistance and review\n\nSee [bad](AGENTS.md#no-such-heading).\n")
        with self.assertRaisesRegex(ValueError, "CONTRIBUTING.md:5: missing heading anchor #no-such-heading"):
            check_docs.check_markdown_docs(self.root)

    def test_unimported_complexity_module_fails(self):
        self.write("Complexity/Computability/Unimported.lean", "-- unimported\n")
        self.write("ROADMAP.md",
                   "# Development roadmap\n\nSee [Unimported](Complexity/Computability/Unimported.lean).\n")
        with self.assertRaisesRegex(
            ValueError,
            "ROADMAP.md:3: module not imported in Complexity.lean: Complexity.Computability.Unimported",
        ):
            check_docs.check_markdown_docs(self.root)

    def test_missing_backticked_module_in_upstream_fails(self):
        self.write("UPSTREAM.md", "# Upstream integration\n\nSee `Complexity/Computability/MissingMod`.\n")
        with self.assertRaisesRegex(
            ValueError,
            "UPSTREAM.md:3: missing module path: Complexity/Computability/MissingMod",
        ):
            check_docs.check_markdown_docs(self.root)

    def test_historical_renamed_module_exemption_and_active_target_check(self):
        self.write(
            "UPSTREAM.md",
            "# Upstream integration\n\n"
            "* **Renamed modules (historical).** `Computability/OldRemoved` became "
            "`Complexity/Computability/MissingNew`.\n",
        )
        with self.assertRaisesRegex(
            ValueError,
            "UPSTREAM.md:3: missing module path: Complexity/Computability/MissingNew",
        ):
            check_docs.check_markdown_docs(self.root)


if __name__ == "__main__":
    unittest.main()

