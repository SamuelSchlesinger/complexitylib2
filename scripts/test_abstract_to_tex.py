#!/usr/bin/env python3
"""Unit and pdflatex integration tests for scripts/abstract_to_tex.py."""

from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import abstract_to_tex


ROOT = Path(__file__).resolve().parents[1]
ABSTRACTS_DIR = ROOT / "ComplexityTests/Abstracts"


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
                "theorem subsetSum_npComplete :",
            ],
        }
        for filename, snippets in expected_theorems.items():
            path = ABSTRACTS_DIR / filename
            title, intro, sections = abstract_to_tex.parse_abstract(path.read_text())
            md = abstract_to_tex.render_markdown(title, intro, sections)
            tex = abstract_to_tex.render_tex(title, intro, sections)

            for snippet in snippets:
                self.assertIn(snippet, md, f"Missing {snippet!r} in Markdown for {filename}")

            # Verify proof bodies and #check_abstract command are stripped from code blocks
            self.assertNotIn("#check_abstract ComplexityTests", md)
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
                check=False,
            )
            self.assertEqual(
                proc.returncode,
                0,
                f"pdflatex failed:\n{proc.stdout[-2000:]}\n{proc.stderr[-2000:]}",
            )
            self.assertTrue((tmp / "abstracts.pdf").is_file())


if __name__ == "__main__":
    unittest.main()
