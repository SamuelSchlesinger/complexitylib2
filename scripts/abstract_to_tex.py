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
    "∏": r"\prod",
    "∑": r"\sum",
    "⋃": r"\bigcup",
    "⊂": r"\subset",
    "⊥": r"\bot",
    "⊤": r"\top",
    "∞": r"\infty",
    "⨅": r"\inf",
    "⨆": r"\sup",
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
    "⦃": r"\{\!\{",
    "⦄": r"\}\!\}",
    "≃": r"\simeq",
    "⌈": r"\lceil",
    "⌉": r"\rceil",
    "·": r"\cdot",
    "ℓ": r"\ell",
    "Σ": r"\Sigma",
    "α": r"\alpha",
    "β": r"\beta",
    "γ": r"\gamma",
    "δ": r"\delta",
    "ε": r"\varepsilon",
    "σ": r"\sigma",
    "τ": r"\tau",
    "φ": r"\varphi",
    "ψ": r"\psi",
    "χ": r"\chi",
    "π": r"\pi",
    "ρ": r"\rho",
    "μ": r"\mu",
    "ν": r"\nu",
    "ι": r"\iota",
    "⁻": r"^{-}",
    "¹": r"^{1}",
    "²": r"^{2}",
    "³": r"^{3}",
    "⁵": r"^{5}",
    "⁹": r"^{9}",
    "ˢ": r"^{\mathsf{s}}",
    "₀": r"_{0}",
    "₁": r"_{1}",
    "₂": r"_{2}",
    "₊": r"_{+}",
    "ₖ": r"_{k}",
    "…": r"\dots",
}

UNICODE_TO_TEX_TEXT = {
    "–": "--",
    "—": "---",
    "’": "'",
    "“": "``",
    "”": "''",
    "é": r"\'{e}",
    "É": r"\'{E}",
    "ő": r"\H{o}",
    "å": r"\r{a}",
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
    # Drop audit commands together with the `#guard_msgs` docstrings pinning their reports.
    body = re.sub(
        r"/--(?:(?!-/).)*-/\s*#guard_msgs[^\n]*\n"
        r"(?=\s*#(?:check_abstract\b|print\s+axioms\b))",
        "",
        body,
        flags=re.DOTALL,
    )
    body = re.sub(
        r"^\s*#check_abstract\b[^\[\n]*(?:\[[^\]]*\])?[^\n]*\n?",
        "",
        body,
        flags=re.MULTILINE,
    )
    body = re.sub(r"^\s*#print\s+axioms\b[^\n]*\n?", "", body, flags=re.MULTILINE)
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


INJECTIVITY_HELPER_RE = re.compile(
    r"^(?:private\s+)?theorem\s+\S*_injective\s*(?:(?:\{[^}]*\}|\([^)]*\))\s*)*:\s*"
    r"Function\.Injective\b"
)


def clean_code_for_display(code: str, is_undocumented_tail: bool = False) -> str:
    """Keep definitions and theorem signatures while eliding proof bodies.

    The only declarations omitted are undocumented `*_injective` helper theorems that follow a
    definition block or a section docstring: they are the injectivity glue for packaging an
    encoding as an embedding (see the lean-abstract skill). Every other theorem keeps its
    signature.
    """
    blocks = re.split(r"\n\s*\n", code.strip())
    kept = []
    for idx, block in enumerate(blocks):
        block = block.strip()
        if not block:
            continue
        if INJECTIVITY_HELPER_RE.match(block) and (idx > 0 or is_undocumented_tail):
            continue
        if re.match(r"^(?:private\s+)?theorem\s+", block):
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
    for index, ch in enumerate(rest):
        if index and rest[index - 1].islower() and ch.isupper():
            out.append(r"\allowbreak{}")
        if ch in UNICODE_TO_TEX_MATH:
            out.append(f"${UNICODE_TO_TEX_MATH[ch]}$")
        elif ch in UNICODE_TO_TEX_TEXT:
            out.append(UNICODE_TO_TEX_TEXT[ch])
        elif ch in TEX_SPECIAL_CODE:
            out.append(TEX_SPECIAL_CODE[ch])
        else:
            out.append(ch)
        # Keep every visible character while allowing long identifiers to wrap at camel-case
        # boundaries (above) and at qualified-name / snake_case separators.
        if ch in (".", "_"):
            out.append(r"\allowbreak{}")
    return "".join(out)


def escape_tex_prose(text: str) -> str:
    """Convert docstring prose (with inline `...` code spans and **bold**) into pdflatex."""
    # Split by inline code spans `...` first so `**` inside code is untouched
    parts = re.split(r"(`[^`]+`|\[[^\[\]]+\]\[[A-Za-z0-9_:.-]+\])", text)
    rendered = []
    for part in parts:
        reference = re.fullmatch(r"\[([^\[\]]+)\]\[([A-Za-z0-9_:.-]+)\]", part)
        if reference:
            rendered.append(escape_tex_prose(reference.group(1)) +
                            r" {\footnotesize (" + escape_tex_prose(reference.group(2)) + ")}")
        elif part.startswith("`") and part.endswith("`"):
            inner = part[1:-1]
            escaped = escape_tex_code_line(inner)
            rendered.append(f"\\texttt{{{escaped}}}")
        else:
            out = []
            for ch in part:
                if ch in UNICODE_TO_TEX_TEXT:
                    out.append(UNICODE_TO_TEX_TEXT[ch])
                elif ch in TEX_SPECIAL_CODE:
                    out.append(TEX_SPECIAL_CODE[ch])
                else:
                    out.append(ch)
            escaped_prose = "".join(out)
            escaped_prose = re.sub(r"\*\*([^*]+)\*\*", r"\\textbf{\1}", escaped_prose)
            escaped_prose = re.sub(r"\*([^*\s][^*]*)\*", r"\\emph{\1}", escaped_prose)
            escaped_prose = escaped_prose.replace("][", r"]\allowbreak{}[")
            rendered.append(escaped_prose)
    return "".join(rendered)


def render_tex_intro(intro: str) -> list[str]:
    """Render the module docstring, turning `## Heading` lines into paragraphs and `* ` bullet
    lines into an itemized list."""
    lines = []
    in_list = False
    item_parts = []
    for raw in intro.splitlines():
        line = raw.strip()
        if line.startswith("* "):
            if not in_list:
                lines.append("\\begin{itemize}\\raggedright")
                in_list = True
            else:
                lines.append("\\item{} " + escape_tex_prose(" ".join(item_parts)))
            item_parts = [line[2:]]
            continue
        if in_list and line and raw[:1].isspace():
            item_parts.append(line)
            continue
        if in_list and line:
            # The empty group prevents a reference's `[author/title]` from becoming the
            # optional item label. Escape after joining continuations so emphasis survives.
            lines.append("\\item{} " + escape_tex_prose(" ".join(item_parts)))
            lines.append("\\end{itemize}")
            in_list = False
        heading = re.match(r"^##\s*(.+)$", line)
        if heading:
            lines.append(f"\\subsubsection*{{{escape_tex_prose(heading.group(1).strip())}}}")
        else:
            lines.append(escape_tex_prose(line))
    if in_list:
        lines.append("\\item{} " + escape_tex_prose(" ".join(item_parts)))
        lines.append("\\end{itemize}")
    return lines


def render_tex(title: str, intro: str, sections: list[dict]) -> str:
    lines = [f"\\subsection{{{escape_tex_prose(title)}}}", "", *render_tex_intro(intro), ""]
    for item in sections:
        doc = item["doc"]
        if item["kind"] == "section":
            m = re.match(r"^##\s*([^\n]+)\n?(.*)", doc, re.DOTALL)
            if m:
                heading = escape_tex_prose(m.group(1).strip())
                rest = escape_tex_prose(m.group(2).strip())
                lines.append(f"\\subsubsection*{{{heading}}}")
                if rest:
                    lines.extend(["", rest])
            else:
                lines.append(escape_tex_prose(doc))
        else:
            lines.append(escape_tex_prose(doc))
        code = clean_code_for_display(item["code"], is_undocumented_tail=(item["kind"] == "section"))
        if code:
            code_lines = [escape_tex_code_line(l) for l in code.splitlines()]
            joined = " \\\\\n".join(l if l else "~" for l in code_lines)
            lines.extend([
                "\\begin{quote}\\small\\ttfamily\\raggedright\\noindent",
                joined,
                "\\end{quote}",
            ])
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
