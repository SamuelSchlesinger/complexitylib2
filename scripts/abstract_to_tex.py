#!/usr/bin/env python3
"""Render a Complexitylib *Abstract.lean file into Markdown or pdflatex-ready LaTeX."""

import argparse
from pathlib import Path
import re
import sys


UNICODE_TO_TEX_MATH = {
    "ℕ": r"\mathbb{N}",
    "ℤ": r"\mathbb{Z}",
    "ℚ": r"\mathbb{Q}",
    "ℝ": r"\mathbb{R}",
    "↪": r"\hookrightarrow",
    "→": r"\to",
    "↦": r"\mapsto",
    "←": r"\leftarrow",
    "↔": r"\leftrightarrow",
    "∃": r"\exists",
    "∀": r"\forall",
    "∈": r"\in",
    "∉": r"\notin",
    "⊆": r"\subseteq",
    "∅": r"\emptyset",
    "∪": r"\cup",
    "∩": r"\cap",
    "¬": r"\neg",
    "∧": r"\land",
    "∨": r"\lor",
    "≤": r"\le",
    "≥": r"\ge",
    "≠": r"\ne",
    "×": r"\times",
    "∘": r"\circ",
    "ᶜ": r"^{\mathsf{c}}",
    "⟨": r"\langle",
    "⟩": r"\rangle",
    "α": r"\alpha",
    "β": r"\beta",
    "γ": r"\gamma",
    "δ": r"\delta",
    "ε": r"\varepsilon",
    "σ": r"\sigma",
    "τ": r"\tau",
    "φ": r"\varphi",
    "ψ": r"\psi",
    "…": r"\dots",
}

UNICODE_TO_TEX_TEXT = {
    "–": "--",
    "—": "---",
    "’": "'",
    "“": "``",
    "”": "''",
    **{k: f"${v}$" for k, v in UNICODE_TO_TEX_MATH.items()},
}

TEX_SPECIAL_CODE = {
    "\\": r"\textbackslash{}",
    "{": r"\{",
    "}": r"\}",
    "_": r"\_",
    "^": r"\textasciicircum{}",
    "&": r"\&",
    "#": r"\#",
    "%": r"\%",
    "$": r"\$",
    "~": r"\textasciitilde{}",
}


def parse_abstract(text: str):
    """Extract the title, module introduction, and alternating docstring/code sections."""
    mod_match = re.search(r"/-\!\s*#\s*([^\n]+)\n(.*?)-/", text, re.DOTALL)
    title = mod_match.group(1).strip() if mod_match else "Formal Abstract"
    intro = mod_match.group(2).strip() if mod_match else ""
    body_start = mod_match.end() if mod_match else 0
    body = text[body_start:]
    body = re.sub(r"^\s*namespace\s+[^\n]+\n", "", body, flags=re.MULTILINE)
    body = re.sub(
        r"^\s*#check_abstract\b[^\n]*(?:\[\s*(?:[^\]]*\n)*[^\]]*\])?\n?",
        "",
        body,
        flags=re.MULTILINE,
    )
    body = re.sub(r"^\s*end\s+[^\n]+\n?", "", body, flags=re.MULTILINE)

    sections = []
    pos = 0
    for m in re.finditer(r"(/-\!(.*?)-/|/--(.*?)-/)", body, re.DOTALL):
        code_before = body[pos:m.start()].strip()
        if code_before and sections:
            sections[-1]["code"] += ("\n\n" if sections[-1]["code"] else "") + code_before
        is_section = m.group(1).startswith("/-!")
        doc = (m.group(2) if is_section else m.group(3)).strip()
        sections.append({"kind": "section" if is_section else "decl", "doc": doc, "code": ""})
        pos = m.end()
    trailing = body[pos:].strip()
    if trailing and sections:
        sections[-1]["code"] += ("\n\n" if sections[-1]["code"] else "") + trailing
    return title, intro, sections


def strip_theorem_proof(block: str) -> str:
    """Strip the proof body after the top-level `:=` of a theorem declaration."""
    depth = 0
    i = 0
    while i < len(block) - 1:
        ch = block[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and block[i : i + 2] == ":=":
            return block[:i].rstrip()
        i += 1
    return block.rstrip()


def clean_code_for_display(code: str, is_undocumented_tail: bool = False) -> str:
    """Keep definitions and theorem signatures while eliding proof bodies and helper lemmas."""
    blocks = re.split(r"\n\s*\n", code.strip())
    kept = []
    for idx, block in enumerate(blocks):
        block = block.strip()
        if not block:
            continue
        # Omit undocumented helper theorems that follow a definition block (e.g. injectivity glue)
        if re.match(r"^(?:private\s+)?theorem\s+", block) and (idx > 0 or is_undocumented_tail):
            continue
        if re.match(r"^theorem\s+", block):
            kept.append(strip_theorem_proof(block))
        else:
            # Replace inline proof terms `, by ...⟩` inside structure constructors with `, _⟩`
            cleaned = re.sub(r",\s*by\s+[^⟩]+⟩", ", _⟩", block)
            kept.append(cleaned)
    return "\n\n".join(kept).strip()


def escape_tex_code_line(line: str) -> str:
    """Convert a single line of Lean code into pdflatex-safe monospaced LaTeX."""
    leading = len(line) - len(line.lstrip(" "))
    rest = line[leading:]
    out = [r"\hspace*{" + f"{leading * 0.5:.1f}em" + "}"] if leading else []
    for ch in rest:
        if ch in UNICODE_TO_TEX_MATH:
            out.append(f"${UNICODE_TO_TEX_MATH[ch]}$")
        elif ch in UNICODE_TO_TEX_TEXT:
            out.append(UNICODE_TO_TEX_TEXT[ch])
        elif ch in TEX_SPECIAL_CODE:
            out.append(TEX_SPECIAL_CODE[ch])
        else:
            out.append(ch)
    return "".join(out)


def escape_tex_prose(text: str) -> str:
    """Convert docstring prose (with inline `...` code spans and **bold**) into pdflatex."""
    # Split by inline code spans `...` first so `**` inside code is untouched
    parts = re.split(r"(`[^`]+`)", text)
    rendered = []
    for part in parts:
        if part.startswith("`") and part.endswith("`"):
            inner = part[1:-1]
            escaped = escape_tex_code_line(inner)
            rendered.append(f"\\texttt{{{escaped}}}")
        else:
            out = []
            for ch in part:
                if ch in UNICODE_TO_TEX_TEXT:
                    out.append(UNICODE_TO_TEX_TEXT[ch])
                elif ch in ("_", "#", "&", "%"):
                    out.append("\\" + ch)
                else:
                    out.append(ch)
            escaped_prose = "".join(out)
            escaped_prose = re.sub(r"\*\*([^*]+)\*\*", r"\\textbf{\1}", escaped_prose)
            rendered.append(escaped_prose)
    return "".join(rendered)


def render_tex(title: str, intro: str, sections: list[dict]) -> str:
    lines = [f"\\subsection{{{escape_tex_prose(title)}}}", "", escape_tex_prose(intro), ""]
    for item in sections:
        doc = item["doc"]
        if item["kind"] == "section":
            m = re.match(r"^##\s*([^\n]+)\n?(.*)", doc, re.DOTALL)
            if m:
                heading = escape_tex_prose(m.group(1).strip())
                rest = escape_tex_prose(m.group(2).strip())
                lines.append(f"\\paragraph{{{heading}.}}" + (f" {rest}" if rest else ""))
            else:
                lines.append(escape_tex_prose(doc))
        else:
            lines.append(escape_tex_prose(doc))
        code = clean_code_for_display(item["code"], is_undocumented_tail=(item["kind"] == "section"))
        if code:
            code_lines = [escape_tex_code_line(l) for l in code.splitlines()]
            joined = " \\\\\n".join(l if l else "~" for l in code_lines)
            lines.extend(["\\begin{quote}\\small\\ttfamily\\noindent", joined, "\\end{quote}"])
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def render_markdown(title: str, intro: str, sections: list[dict]) -> str:
    lines = [f"# {title}", "", intro, ""]
    for item in sections:
        lines.append(item["doc"])
        code = clean_code_for_display(item["code"], is_undocumented_tail=(item["kind"] == "section"))
        if code:
            lines.extend(["", "```lean", code, "```"])
        lines.append("")
    return "\n".join(lines).strip() + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("path", type=Path, help="Path to *Abstract.lean file")
    parser.add_argument("--format", choices=("markdown", "tex"), default="markdown")
    args = parser.parse_args()
    title, intro, sections = parse_abstract(args.path.read_text())
    if args.format == "tex":
        sys.stdout.write(render_tex(title, intro, sections))
    else:
        sys.stdout.write(render_markdown(title, intro, sections))


if __name__ == "__main__":
    main()
