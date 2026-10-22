#!/usr/bin/env python3
"""Selection, display-boundary and provenance regressions for formal abstract PDFs."""

import json
from contextlib import chdir
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import build_abstracts as build


SOURCE = """/-! # A checked statement

This is the mathematical introduction.
-/
namespace ComplexityTests.Abstracts.ExampleAbstract
/-- A visible definition. -/
def value : Nat := 0

/-- The selected result. -/
theorem chosen : value = 0 := rfl

/-- A supporting result that is not selected. -/
theorem other : True := by trivial
end ComplexityTests.Abstracts.ExampleAbstract
"""


class BuildAbstractsTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="test-abstract-builder-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        source = self.root / "ComplexityTests/Abstracts/ExampleAbstract.lean"
        source.parent.mkdir(parents=True)
        source.write_text(SOURCE)
        scripts = self.root / "scripts"
        scripts.mkdir()
        for name in ("build_abstracts.py", "abstract_to_tex.py"):
            shutil.copyfile(Path(build.__file__).with_name(name), scripts / name)
        self.entry = {"id": "example", "title": "An example", "summary": "The selected result.",
                      "scope": "No algorithmic claim.",
                      "module": "ComplexityTests.Abstracts.ExampleAbstract",
                      "headline_theorems": ["ComplexityTests.Abstracts.ExampleAbstract.chosen"]}
        self.manifest = self.root / "catalogue.json"
        self.write_manifest([self.entry])

    def write_manifest(self, entries):
        self.manifest.write_text(json.dumps({"title": "Selected abstracts", "entries": entries}))

    def test_selection_rejects_duplicates_and_non_theorem_headlines(self):
        self.assertEqual(build.load_catalogue(self.manifest, self.root), [self.entry])
        self.write_manifest([self.entry, self.entry])
        with self.assertRaisesRegex(ValueError, "duplicate catalogue id"):
            build.load_catalogue(self.manifest, self.root)
        self.entry["headline_theorems"] = [self.entry["module"] + ".value"]
        self.write_manifest([self.entry])
        with self.assertRaisesRegex(ValueError, "not a theorem"):
            build.load_catalogue(self.manifest, self.root)

    def test_missing_or_foreign_headline_is_rejected(self):
        self.entry["headline_theorems"] = [self.entry["module"] + ".missing"]
        self.write_manifest([self.entry])
        with self.assertRaisesRegex(ValueError, "found 0"):
            build.load_catalogue(self.manifest, self.root)
        self.entry["headline_theorems"] = ["Other.Abstract.chosen"]
        self.write_manifest([self.entry])
        with self.assertRaisesRegex(ValueError, "qualified within"):
            build.load_catalogue(self.manifest, self.root)

    def test_display_keeps_definitions_and_selected_statements_without_proofs(self):
        rendered = build.render_entry(self.entry, "owner/repo", "a" * 40, False, self.root)
        self.assertIn(r"\begin{leanbox}", rendered)
        self.assertIn("value", rendered)
        self.assertIn("chosen", rendered)
        self.assertNotIn("supporting result", rendered)
        self.assertNotIn("other", rendered)
        self.assertNotIn("rfl", rendered)
        self.assertIn("a" * 40 + "/ComplexityTests/Abstracts/ExampleAbstract.lean", rendered)
        self.assertIn(r"\textcolor{leanblue}", rendered)

    def test_source_links_pin_the_declaration_line(self):
        line = build.declaration_line(SOURCE, self.entry["headline_theorems"][0])
        self.assertEqual(SOURCE.splitlines()[line - 1], "theorem chosen : value = 0 := rfl")
        self.assertEqual(build.source_url("owner/repo", "a" * 40, "X.lean", line),
                         "https://github.com/owner/repo/blob/" + "a" * 40 + f"/X.lean#L{line}")

    def test_provenance_records_pdf_and_input_digests(self):
        def fake_pdf(tex):
            pdf = tex.with_suffix(".pdf")
            pdf.write_bytes(b"%PDF-fixture")
            return pdf

        with patch.object(build, "git", side_effect=["a" * 40, ""]), \
             patch.object(build.shutil, "which", return_value="latexmk"), \
             patch.object(build, "build_pdf", side_effect=fake_pdf):
            result = build.build(self.manifest, self.root / "build", root=self.root)
        self.assertFalse(result["source_dirty"])
        self.assertEqual(result["documents"][0]["pdf_sha256"],
                         build.digest(self.root / "build/example.pdf"))
        self.assertEqual(result["documents"][0]["source_sha256"],
                         build.digest(self.root / "ComplexityTests/Abstracts/ExampleAbstract.lean"))
        self.assertTrue(result["documents"][0]["headlines"][0]["url"].endswith("#L10"))
        self.assertEqual(len(result["inputs"]), 4)

    def test_relative_manifest_and_output_paths_record_relative_inputs(self):
        def fake_pdf(tex):
            pdf = tex.with_suffix(".pdf")
            pdf.write_bytes(b"%PDF-fixture")
            return pdf

        with chdir(self.root), \
             patch.object(build, "git", side_effect=["a" * 40, ""]), \
             patch.object(build.shutil, "which", return_value="latexmk"), \
             patch.object(build, "build_pdf", side_effect=fake_pdf):
            result = build.build(Path("catalogue.json"), Path("build"), root=self.root)
        self.assertIn({"path": "catalogue.json", "sha256": build.digest(self.manifest)},
                      result["inputs"])
        self.assertTrue((self.root / "build/provenance.json").is_file())

    def test_list_root_is_rejected_consistently(self):
        self.manifest.write_text(json.dumps([self.entry]))
        with self.assertRaisesRegex(ValueError, "title and an entries list"):
            build.load_catalogue(self.manifest, self.root)

    def test_dirty_checkout_cannot_be_published(self):
        with patch.object(build, "git", side_effect=["a" * 40, " M X.lean"]):
            with self.assertRaisesRegex(ValueError, "clean source checkout"):
                build.build(self.manifest, self.root / "build", root=self.root, require_clean=True)

    def test_a_source_change_during_generation_invalidates_provenance(self):
        def changing_pdf(tex):
            pdf = tex.with_suffix(".pdf")
            pdf.write_bytes(b"%PDF-fixture")
            source = self.root / "ComplexityTests/Abstracts/ExampleAbstract.lean"
            source.write_text(source.read_text() + "\n-- changed during generation\n")
            return pdf

        output = self.root / "build"
        output.mkdir()
        (output / "provenance.json").write_text("stale provenance")
        with patch.object(build, "git", side_effect=["a" * 40, ""]), \
             patch.object(build.shutil, "which", return_value="latexmk"), \
             patch.object(build, "build_pdf", side_effect=changing_pdf):
            with self.assertRaisesRegex(ValueError, "Source changed during PDF generation"):
                build.build(self.manifest, output, root=self.root)
        self.assertFalse((output / "provenance.json").exists())

    def test_explicit_support_is_rendered_without_promoting_it_to_a_headline(self):
        self.entry["supporting_theorems"] = [self.entry["module"] + ".other"]
        self.write_manifest([self.entry])
        build.load_catalogue(self.manifest, self.root)
        rendered = build.render_entry(self.entry, "owner/repo", "a" * 40, False, self.root)
        self.assertIn("supporting result", rendered)
        self.assertIn("other", rendered)
        self.assertEqual(len(self.entry["headline_theorems"]), 1)

    @unittest.skipUnless(shutil.which("latexmk") and shutil.which("pdftotext")
                         and shutil.which("kpsewhich"), "TeX/Poppler not installed")
    def test_styled_pdfs_build_with_source_pinned_hyperlinks(self):
        for package in ("libertine.sty", "newtxmath.sty", "zi4.sty", "tcolorbox.sty"):
            if subprocess.run(["kpsewhich", package], capture_output=True).returncode:
                self.skipTest(f"TeX package missing: {package}")
        with patch.object(build, "git", side_effect=["a" * 40, ""]):
            result = build.build(self.manifest, self.root / "build", root=self.root,
                                 require_clean=True)
        self.assertEqual(len(result["documents"]), 1)
        self.assertIn("Selected abstracts", (self.root / "build/catalogue.tex").read_text())
        if shutil.which("pdfinfo"):
            links = subprocess.check_output(
                ["pdfinfo", "-url", str(self.root / "build/example.pdf")], text=True)
            self.assertIn("/blob/" + "a" * 40 +
                          "/ComplexityTests/Abstracts/ExampleAbstract.lean#L10", links)


if __name__ == "__main__":
    unittest.main()
