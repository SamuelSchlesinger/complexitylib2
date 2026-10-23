#!/usr/bin/env python3
"""Unit and pdflatex integration tests for scripts/abstract_to_tex.py."""

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import xml.etree.ElementTree as ET

import abstract_to_tex


ROOT = Path(__file__).resolve().parents[1]
ABSTRACTS_DIR = ROOT / "abstracts/ComplexityAbstracts"


class AbstractToTexTests(unittest.TestCase):
    def test_all_abstracts_render_markdown_and_tex(self):
        expected_theorems = {
            "CookLevinAbstract.lean": [
                "theorem sat_npComplete : NPComplete encCNF SAT",
                "theorem unsat_coNPComplete : coNPComplete encCNF UNSAT",
                "theorem exactThreeSAT_npComplete : NPComplete encCNF ExactThreeSAT",
            ],
            "TQBFAbstract.lean": [
                "inductive Formula where",
                "theorem tqbf_pspaceComplete : PSPACEComplete encQBF TQBF",
            ],
            "SubsetSumAbstract.lean": [
                "def SubsetSum : Set (List ℕ × ℕ) :=",
                "theorem subsetSum_npComplete : NPComplete encSubsetSum SubsetSum",
            ],
        }
        paths = sorted(ABSTRACTS_DIR.glob("*Abstract.lean"))
        self.assertTrue(set(expected_theorems).issubset({path.name for path in paths}),
                        f"Expected abstract sources under {ABSTRACTS_DIR}")
        for path in paths:
            filename = path.name
            snippets = expected_theorems.get(filename, [])
            title, intro, sections = abstract_to_tex.parse_abstract(path.read_text())
            md = abstract_to_tex.render_markdown(title, intro, sections)
            tex = abstract_to_tex.render_tex(title, intro, sections)

            for snippet in snippets:
                self.assertIn(snippet, md, f"Missing {snippet!r} in Markdown for {filename}")

            # Verify proof bodies and #check_abstract command are stripped from code blocks
            self.assertNotIn("#check_abstract ComplexityTests", md)
            self.assertNotIn("abstract audit passed", md)
            self.assertNotIn("guard_msgs", md)
            self.assertNotIn("check\\_abstract ComplexityTests", tex)
            self.assertNotIn("Bridge.", md.split("## Main result")[-1])

            # Verify LaTeX output contains only ASCII characters (safe for pdflatex T1 fontenc)
            non_ascii = [ch for ch in tex if ord(ch) >= 128]
            self.assertEqual(
                non_ascii,
                [],
                f"Unescaped non-ASCII characters in TeX output for {filename}: {set(non_ascii)}",
            )

    def test_strip_theorem_proof_preserves_named_arguments(self):
        sample = (
            "theorem foo (x : ℕ) :\n"
            "    Bar (V := ℕ) x :=\n"
            "  Bridge.foo x"
        )
        self.assertEqual(
            abstract_to_tex.clean_code_for_display(sample),
            "theorem foo (x : ℕ) :\n    Bar (V := ℕ) x",
        )
        prose = "Check `x ** y` and **bold** text."
        self.assertEqual(
            abstract_to_tex.escape_tex_prose(prose),
            r"Check \texttt{x ** y} and \textbf{bold} text.",
        )

    def test_only_injectivity_helpers_are_elided(self):
        sample = (
            "def encX : X → List Bool := f\n\n"
            "theorem encX_injective : Function.Injective encX :=\n  Bridge.encX_injective\n\n"
            "theorem other_fact : P :=\n  Bridge.other_fact\n\n"
            "theorem misnamed_injective : Q :=\n  Bridge.misnamed_injective"
        )
        self.assertEqual(
            abstract_to_tex.clean_code_for_display(sample),
            "def encX : X → List Bool := f\n\ntheorem other_fact : P\n\n"
            "theorem misnamed_injective : Q",
        )

    def test_reference_bullets_cannot_become_tex_item_labels(self):
        rendered = "\n".join(abstract_to_tex.render_tex_intro(
            "## References\n\n* [S. Arora, B. Barak, *Computational Complexity*][AroraBarak09]"
        ))
        self.assertIn(r"\item{} S. Arora, B. Barak,", rendered)
        self.assertIn(r"\emph{Computational Complexity}", rendered)
        self.assertIn(r"{\footnotesize (AroraBarak09)}", rendered)

    def test_wrapped_reference_stays_in_its_list_item(self):
        rendered = "\n".join(abstract_to_tex.render_tex_intro(
            "## References\n\n* [S. A. Cook, R. A. Reckhow, *The relative efficiency of\n"
            "  propositional proof systems*][CookReckhow1979]\n\n"
            "* [A. Haken, *The intractability of resolution*][Haken1985]\n"
        ))
        self.assertIn(r"\emph{The relative efficiency of propositional proof systems}", rendered)
        self.assertEqual(rendered.count(r"\begin{itemize}"), 1)
        self.assertEqual(rendered.count(r"\item{}"), 2)

    def test_section_heading_and_machine_name_can_wrap(self):
        machine = "Turing.MultiTapeTM.ComputableInTimeAndSpaceOfLength"
        rendered = abstract_to_tex.render_tex("Title", "", [{
            "kind": "section",
            "doc": f"## Polynomial-time computability, NP, coNP, and completeness\n\n"
                   f"In upstream `Cslib`, `{machine}` means a halting machine.",
            "code": "",
        }])
        self.assertIn("\\subsubsection*{Polynomial-time computability, NP, coNP, "
                      "and completeness}\n\nIn upstream", rendered)
        self.assertIn(r"Turing.\allowbreak{}Multi\allowbreak{}Tape\allowbreak{}TM.\allowbreak{}"
                      r"Computable\allowbreak{}In\allowbreak{}Time", rendered)
        self.assertNotIn(r"\paragraph{", rendered)

    def test_catalogue_symbols_and_author_names_are_pdflatex_safe(self):
        sample = "∏ ∑ ⊥ ⊤ χ π ρ μ ν ι ℓ ∞ ⨅ ⨆ ≃ Σ ⦃x⦄ ⌈x⌉₊ x₀ x₁ x₂ xₖ f⁻¹ x² x³ x⁵ x⁹ ∑ˢ ⋃ ⊂ ·"
        rendered = abstract_to_tex.escape_tex_code_line(sample)
        self.assertTrue(rendered.isascii())
        for command in (r"\prod", r"\sum", r"\bot", r"\top", r"\chi", r"\infty"):
            self.assertIn(command, rendered)
        self.assertEqual(abstract_to_tex.escape_tex_prose("Håstad, Erdős, Bonami–Beckner"),
                         r"H\r{a}stad, Erd\H{o}s, Bonami--Beckner")
        self.assertEqual(abstract_to_tex.escape_tex_prose("2^(n/24), {0,1}, $5 and ~n"),
                         r"2\textasciicircum{}(n/24), \{0,1\}, \$5 and \textasciitilde{}n")

    def test_named_axiom_audits_are_stripped(self):
        sample = (
            "/-! # Title\n\nIntro.\n-/\n\nnamespace Foo\n\n"
            "/-- A result. -/\ntheorem result : True := by trivial\n\n"
            "/-- info: 'Foo.result' does not depend on any axioms -/\n"
            "#guard_msgs in\n#print axioms result\n\nend Foo\n"
        )
        title, intro, sections = abstract_to_tex.parse_abstract(sample)
        self.assertEqual(len(sections), 1)
        rendered = abstract_to_tex.render_markdown(title, intro, sections)
        self.assertIn("theorem result : True", rendered)
        self.assertNotIn("axioms", rendered)
        self.assertNotIn("guard_msgs", rendered)

    def test_guarded_audit_is_stripped(self):
        sample = (
            "/-! # Title\n\nIntro.\n-/\n\n"
            "namespace Foo\n\n"
            "/-- A definition. -/\ndef x : Nat := 0\n\n"
            "/--\ninfo: abstract audit passed for `Foo`: 1 root\ndeclarations, 0 dependencies"
            " checked\n-/\n#guard_msgs (whitespace := lax) in\n#check_abstract Foo\n\n"
            "end Foo\n"
        )
        _, _, sections = abstract_to_tex.parse_abstract(sample)
        self.assertEqual(len(sections), 1)
        self.assertEqual(sections[0]["code"], "def x : Nat := 0")

    def test_guarded_multiline_allowlist_is_stripped(self):
        sample = (
            "/-! # Title\n\nIntro.\n-/\n\n"
            "namespace Foo\n\n"
            "/-- A definition. -/\ndef x : Nat := 0\n\n"
            "/-- info: audit passed -/\n#guard_msgs in\n"
            "#check_abstract Foo allowing [\n"
            "  Complexity.First,\n  Complexity.Second\n]\n\n"
            "end Foo\n"
        )
        title, intro, sections = abstract_to_tex.parse_abstract(sample)
        self.assertEqual(len(sections), 1)
        self.assertEqual(sections[0]["code"], "def x : Nat := 0")
        for rendered in (
            abstract_to_tex.render_markdown(title, intro, sections),
            abstract_to_tex.render_tex(title, intro, sections),
        ):
            self.assertNotIn("Complexity.First", rendered)
            self.assertNotIn("Complexity.Second", rendered)
            self.assertNotIn("audit passed", rendered)

    @unittest.skipUnless(shutil.which("pdflatex"), "pdflatex not installed")
    def test_pdflatex_compiles_rendered_abstracts(self):
        tex_bodies = []
        for path in sorted(ABSTRACTS_DIR.glob("*Abstract.lean")):
            title, intro, sections = abstract_to_tex.parse_abstract(path.read_text())
            tex_bodies.append(abstract_to_tex.render_tex(title, intro, sections))

        document = "\n".join([
            r"\documentclass[11pt]{article}",
            r"\usepackage[T1]{fontenc}",
            r"\usepackage{lmodern}",
            r"\usepackage[margin=1in]{geometry}",
            r"\usepackage{microtype,amsmath,amssymb,xcolor,enumitem,titlesec}",
            r"\setlength{\parindent}{0pt}",
            r"\setlength{\parskip}{0.45em}",
            r"\begin{document}",
            r"\section{Formal Abstracts}",
            *tex_bodies,
            r"\end{document}",
            "",
        ])
        with tempfile.TemporaryDirectory(prefix="test-abstract-tex-") as tmpdir:
            tmp = Path(tmpdir)
            tex_file = tmp / "abstracts.tex"
            tex_file.write_text(document)
            proc = subprocess.run(
                ["pdflatex", "-interaction=nonstopmode", "-halt-on-error", "abstracts.tex"],
                cwd=tmp,
                capture_output=True,
                text=True,
                errors="replace",  # TeX may log accented author names in its legacy font encoding.
                check=False,
            )
            self.assertEqual(
                proc.returncode,
                0,
                f"pdflatex failed:\n{proc.stdout[-2000:]}\n{proc.stderr[-2000:]}",
            )
            self.assertTrue((tmp / "abstracts.pdf").is_file())
            if shutil.which("pdftotext"):
                # Compilation succeeds even when bibliography labels and long identifiers
                # extend off the page. Check the actual glyph positions as well.
                bbox_file = tmp / "abstracts.html"
                subprocess.run(
                    ["pdftotext", "-bbox", str(tmp / "abstracts.pdf"), str(bbox_file)],
                    capture_output=True,
                    text=True,
                    check=True,
                )
                root = ET.parse(bbox_file).getroot()
                for page in root.findall(".//{*}page"):
                    page_width = float(page.attrib["width"])
                    for word in page.findall(".//{*}word"):
                        self.assertGreaterEqual(float(word.attrib["xMin"]), 36,
                                                f"Text clips the left margin: {word.text!r}")
                        self.assertLessEqual(float(word.attrib["xMax"]), page_width - 36,
                                             f"Text clips the right margin: {word.text!r}")


if __name__ == "__main__":
    unittest.main()
