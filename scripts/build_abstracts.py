#!/usr/bin/env python3
"""Build individual Lean formal-abstract PDFs and their curated catalogue (Python 3.11+)."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
from urllib.parse import quote
import xml.etree.ElementTree as ET

import abstract_to_tex as render


ROOT = Path(__file__).resolve().parents[1]
STYLE_SOURCE = (
    "https://github.com/edemaine/translation-tiling-paper/blob/"
    "5309313e662377d2efb353acba454859469606bd/paper.texlish"
)
EXTRACTION_SOURCE = (
    "https://github.com/edemaine/translation-tiling-paper/blob/"
    "5309313e662377d2efb353acba454859469606bd/figures/extract_lean_snippets.py"
)
KEYWORDS = {"abbrev", "def", "theorem", "lemma", "inductive", "structure", "where", "fun",
            "noncomputable", "private", "if", "then", "else", "match", "with"}
TYPES = {"Prop", "Type", "Set", "List", "Fin", "Nat", "Bool", "Polynomial", "Finset", "Option"}
TOKEN_RE = re.compile(r"\b(?:" + "|".join(sorted(KEYWORDS | TYPES)) + r")\b")

# Typography, code-box treatment and syntax colors adapted from Erik Demaine and Stefan Langerman's
# translation-tiling-paper, paper.texlish:25-78 at the exact revision linked above.
# This uses no logo or copied mathematical exposition.
PREAMBLE = r"""\documentclass[11pt]{article}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb}
\usepackage{libertine}
\usepackage[libertine]{newtxmath}
\usepackage[scaled=0.96]{zi4}
\usepackage[margin=0.9in]{geometry}
\usepackage{microtype,enumitem,xcolor,tcolorbox,xurl,hyperref,fancyhdr}
\tcbuselibrary{breakable,skins}
\definecolor{leanblue}{RGB}{41,110,166}
\definecolor{leangreen}{RGB}{38,128,89}
\hypersetup{colorlinks=true,urlcolor=leanblue,linkcolor=leanblue}
\newtcolorbox{leanbox}{breakable,enhanced,colback=black!3,colframe=black!45,
  boxrule=0.5pt,arc=2pt,left=7pt,right=7pt,top=5pt,bottom=5pt,
  before skip=7pt,after skip=9pt}
\setlength{\parindent}{0pt}
\setlength{\parskip}{0.45em}
\setlength{\emergencystretch}{2em}
\setlist[itemize]{leftmargin=1.4em,itemsep=2pt,topsep=3pt}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small\textsc{Complexitylib / Formal abstracts}}
\renewcommand{\headrulewidth}{0.3pt}
\setlength{\headheight}{14pt}
\begin{document}
"""


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git(root, *args):
    return subprocess.check_output(["git", *args], cwd=root, text=True).strip()


def module_source_path(module, root=ROOT):
    """Resolve the dedicated abstract library's modules within its configured source root."""
    if not isinstance(module, str) or not re.fullmatch(
            r"ComplexityAbstracts\.[A-Za-z_][A-Za-z0-9_]*", module):
        raise ValueError(f"Not a formal-abstract module: {module}")
    return Path(root).joinpath("abstracts", *module.split(".")).with_suffix(".lean")


def _lean_code(text):
    """Mask comments and strings while preserving source positions and line numbers."""
    result, index, depth = list(text), 0, 0
    while index < len(text):
        if depth:
            if text.startswith("/-", index):
                depth += 1
                width = 2
            elif text.startswith("-/", index):
                depth -= 1
                width = 2
            else:
                width = 1
        elif text.startswith("/-", index):
            depth, width = 1, 2
        elif text.startswith("--", index):
            end = text.find("\n", index)
            width = (len(text) if end < 0 else end) - index
        elif text[index] == "'" and (literal := re.match(r"'(?:\\.|[^'\\\n])'", text[index:])):
            width = len(literal.group())
        elif text[index] == '"' or (text[index] == "r" and re.match(r'r#+"', text[index:])):
            raw = re.match(r'r(#+)"', text[index:])
            if raw:
                close = '"' + raw.group(1)
                end = text.find(close, index + len(raw.group()))
                width = (len(text) if end < 0 else end + len(close)) - index
            else:
                end = index + 1
                while end < len(text):
                    if text[end] == "\\":
                        end += 2
                    elif text[end] == '"':
                        end += 1
                        break
                    else:
                        end += 1
                width = end - index
        else:
            index += 1
            continue
        for offset in range(index, min(index + width, len(text))):
            if text[offset] != "\n":
                result[offset] = " "
        index += width
    return "".join(result)


def _namespace_contexts(text):
    """Track namespace commands (and section scopes) in the abstract's source code."""
    declared, contexts, stack, namespace = set(), {}, [], ""
    for number, line in enumerate(_lean_code(text).splitlines(), 1):
        contexts[number] = namespace
        opening = re.fullmatch(r"\s*namespace\s+([A-Za-z_][A-Za-z0-9_.]*)\s*", line)
        if opening:
            stack.append(namespace)
            namespace = ".".join(filter(None, (namespace, opening.group(1))))
            declared.add(namespace)
        elif re.fullmatch(r"\s*(?:noncomputable\s+)?section(?:\s+\w+)?\s*", line):
            stack.append(namespace)
        elif re.fullmatch(r"\s*end(?:\s+[A-Za-z_][A-Za-z0-9_.]*)?\s*", line):
            if stack:
                namespace = stack.pop()
    return declared, contexts


def declaration_line(text, name):
    """Locate the named source declaration; headline names may be qualified."""
    short = name.rsplit(".", 1)[-1]
    pattern = re.compile(r"^\s*(?:(?:private|noncomputable)\s+)?"
                         r"(?:theorem|lemma|def|abbrev|inductive|structure)\s+"
                         + re.escape(short) + r"(?=[\s:{(])")
    matches = [i for i, line in enumerate(_lean_code(text).splitlines(), 1) if pattern.search(line)]
    if len(matches) != 1:
        raise ValueError(f"Expected exactly one declaration named {name}, found {len(matches)}")
    return matches[0]


def load_catalogue(manifest, root=ROOT):
    data = json.loads(Path(manifest).read_text())
    if not isinstance(data, dict) or not isinstance(data.get("title"), str) or not data["title"].strip():
        raise ValueError("Catalogue needs a title and an entries list")
    entries = data.get("entries")
    if not isinstance(entries, list) or not entries:
        raise ValueError("Catalogue must contain a nonempty entries list")
    seen_ids, seen_headlines = set(), set()
    for entry in entries:
        if not isinstance(entry, dict):
            raise ValueError("Each catalogue entry must be an object")
        for field in ("id", "title", "module", "summary", "scope"):
            if not isinstance(entry.get(field), str) or not entry[field].strip():
                raise ValueError(f"Catalogue entry needs nonempty {field}")
        entry_id = entry["id"]
        if (not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", entry_id)
                or entry_id in seen_ids or entry_id == "catalogue"):
            raise ValueError(f"Invalid or duplicate catalogue id: {entry_id}")
        seen_ids.add(entry_id)
        module = entry["module"]
        source = module_source_path(module, root)
        if not module.endswith("Abstract"):
            raise ValueError(f"Not a formal-abstract module: {module}")
        namespace = entry.get("namespace", module)
        if not isinstance(namespace, str) or not re.fullmatch(
                r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", namespace):
            raise ValueError(f"Invalid abstract namespace: {namespace}")
        text = source.read_text()
        declared, contexts = _namespace_contexts(text)
        if namespace not in declared:
            raise ValueError(f"Abstract namespace {namespace} is not declared in {source}")
        headlines = entry.get("headline_theorems")
        if not isinstance(headlines, list) or not headlines:
            raise ValueError(f"No selected headline theorems in {entry_id}")
        supporting = entry.get("supporting_theorems", [])
        if not isinstance(supporting, list):
            raise ValueError(f"Supporting theorems must be a list in {entry_id}")
        for name in [*headlines, *supporting]:
            if not isinstance(name, str) or not re.fullmatch(
                    re.escape(namespace) + r"\.[A-Za-z_][A-Za-z0-9_']*", name):
                raise ValueError(f"Headline must be qualified within {namespace}: {name}")
            if name in seen_headlines:
                raise ValueError(f"Duplicate selected headline: {name}")
            seen_headlines.add(name)
            line = declaration_line(text, name)
            if contexts[line] != namespace:
                raise ValueError(f"Headline is outside namespace {namespace}: {name}")
            if not re.match(r"\s*(?:theorem|lemma)\s", text.splitlines()[line - 1]):
                raise ValueError(f"Selected headline is not a theorem: {name}")
    return entries


def source_url(repository, sha, relative_path, line=None):
    url = f"https://github.com/{repository}/blob/{sha}/{quote(str(relative_path))}"
    return url + (f"#L{line}" if line else "")


def link(url, label):
    # detokenize preserves source paths/anchors without treating underscores as TeX commands.
    return r"\href{\detokenize{" + url + "}}{" + label + "}"


def highlighted_line(line):
    pieces, start = [], 0
    for token in TOKEN_RE.finditer(line):
        pieces.append(render.escape_tex_code_line(line[start:token.start()]))
        word = token.group()
        color = "leanblue" if word in KEYWORDS else "leangreen"
        escaped = render.escape_tex_code_line(word)
        if word in KEYWORDS:
            escaped = r"\textbf{" + escaped + "}"
        pieces.append(r"\textcolor{" + color + "}{" + escaped + "}")
        start = token.end()
    pieces.append(render.escape_tex_code_line(line[start:]))
    return "".join(pieces)


def render_entry(entry, repository, sha, dirty, root=ROOT):
    source = module_source_path(entry["module"], root)
    text = source.read_text()
    _, intro, sections = render.parse_abstract(text)
    relative = source.relative_to(root)
    title = render.escape_tex_prose(entry["title"])
    url = source_url(repository, sha, relative)
    state = "Working tree based on" if dirty else "Source revision"
    lines = [r"\hypertarget{" + entry["id"] + "}{}", r"\section*{" + title + "}",
             r"{\small\color{black!65} " + state + " " +
             link(f"https://github.com/{repository}/commit/{sha}", r"\texttt{" + sha[:12] + "}") +
             " / " + link(url, "Lean source") + "}"]
    displayed_names = [*entry["headline_theorems"], *entry.get("supporting_theorems", [])]
    lines.append(r"{\small Statements: " + ", ".join(
        link(source_url(repository, sha, relative, declaration_line(text, name)),
             render.escape_tex_prose("`" + name.rsplit(".", 1)[-1] + "`"))
        for name in displayed_names) + "}")
    if dirty:
        lines.append(r"{\small\emph{Local source edits are identified by digests in provenance.json; "
                     "the links show the base revision.}}")
    lines.extend([r"\begin{quote}\small " + render.escape_tex_prose(entry["summary"]) +
                  r"\par\emph{Scope.} " + render.escape_tex_prose(entry["scope"]) +
                  r"\end{quote}", "", *render.render_tex_intro(intro), ""])
    selected = {name.rsplit(".", 1)[-1] for name in displayed_names}
    displayed = set()
    for item in sections:
        code = render.clean_code_for_display(item["code"],
                                             is_undocumented_tail=item["kind"] == "section")
        kept = []
        for block in re.split(r"\n\s*\n", code):
            theorem = re.match(r"(?:private\s+)?(?:theorem|lemma)\s+(\S+)", block)
            if not theorem or theorem.group(1) in selected:
                kept.append(block)
                if theorem:
                    displayed.add(theorem.group(1))
        code = "\n\n".join(kept).strip()
        if item["kind"] == "decl" and item["code"].strip() and not code:
            continue
        doc = item["doc"]
        heading = re.match(r"^##\s*([^\n]+)\n?(.*)", doc, re.DOTALL) if item["kind"] == "section" else None
        if heading:
            lines.extend([r"\subsection*{" + render.escape_tex_prose(heading.group(1).strip()) + "}",
                          render.escape_tex_prose(heading.group(2).strip())])
        else:
            lines.append(render.escape_tex_prose(doc))
        if code:
            code_lines = [highlighted_line(line) or "~" for line in code.splitlines()]
            lines.extend([r"\begin{leanbox}\small\ttfamily\raggedright\noindent",
                          " \\\\\n".join(code_lines), r"\par\end{leanbox}"])
    if displayed != selected:
        raise ValueError(f"Selected statements were not rendered: {sorted(selected - displayed)}")
    return "\n\n".join(lines) + "\n"


def style_credit():
    return (r"\fancyfoot[C]{\parbox[b]{\textwidth}{\centering\fontsize{8}{9.5}\selectfont"
            r"\color{black!60} Theorem and helper proofs are omitted. "
            "Proof-field underscores mark omitted checked terms. Linked sources contain complete "
            "definitions and proofs. Layout adapted from Erik Demaine and Stefan Langerman's " +
            link(STYLE_SOURCE, "paper style") + "; extraction follows their " +
            link(EXTRACTION_SOURCE, "Lean snippet workflow") + r".\par\thepage}}" + "\n")


def document(body):
    return PREAMBLE + style_credit() + body + "\n\\end{document}\n"


def build_pdf(tex_path):
    command = ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
               "-no-shell-escape", tex_path.name]
    result = subprocess.run(command, cwd=tex_path.parent, capture_output=True, text=True,
                            errors="replace")
    if result.returncode:
        raise ValueError(f"PDF build failed for {tex_path.name}:\n{result.stdout[-5000:]}\n"
                         f"{result.stderr[-1000:]}")
    pdf = tex_path.with_suffix(".pdf")
    if not shutil.which("pdftotext"):
        raise ValueError("Poppler's pdftotext is required to check PDF text margins")
    bounds = tex_path.with_suffix(".bbox.html")
    subprocess.run(["pdftotext", "-bbox", str(pdf), str(bounds)], check=True,
                   capture_output=True, text=True)
    pages = ET.parse(bounds).getroot().findall(".//{*}page")
    if not pages:
        raise ValueError(f"No rendered pages in {pdf.name}")
    for number, page in enumerate(pages, 1):
        width, height = float(page.attrib["width"]), float(page.attrib["height"])
        for word in page.findall(".//{*}word"):
            if (float(word.attrib["xMin"]) < 24 or float(word.attrib["xMax"]) > width - 24
                    or float(word.attrib["yMin"]) < 18 or float(word.attrib["yMax"]) > height - 18):
                raise ValueError(f"Text clips page margins in {pdf.name}, page {number}: {word.text!r}")
    return pdf


def build(manifest, output, *, root=ROOT, require_clean=False):
    root = Path(root).resolve()
    manifest, output = Path(manifest).resolve(), Path(output).resolve()
    entries = load_catalogue(manifest, root)
    sha = git(root, "rev-parse", "HEAD")
    dirty = bool(git(root, "status", "--porcelain"))
    if require_clean and dirty:
        raise ValueError("A clean source checkout is required for publication")
    if not shutil.which("latexmk"):
        raise ValueError("latexmk is required (see abstracts/README.md for TeX dependencies)")
    inputs = {Path(manifest), root / "scripts/build_abstracts.py", root / "scripts/abstract_to_tex.py"}
    for entry in entries:
        source = module_source_path(entry["module"], root)
        inputs.add(source)
        bridge = source.with_name(source.name.replace("Abstract.lean", "Bridge.lean"))
        if bridge.is_file():
            inputs.add(bridge)
    input_records = [{"path": str(path.relative_to(root)), "sha256": digest(path)}
                     for path in sorted(inputs)]
    repository = os.environ.get("GITHUB_REPOSITORY", "cslib-community/complexitylib")
    output.mkdir(parents=True, exist_ok=True)
    (output / "provenance.json").unlink(missing_ok=True)
    # Rebuild the explicit selection without retaining retired release PDFs in a reused directory.
    for stale in output.glob("*.pdf"):
        if stale.stem not in {entry["id"] for entry in entries} | {"catalogue"}:
            stale.unlink()
    bodies, documents = [], []
    for entry in entries:
        body = render_entry(entry, repository, sha, dirty, root)
        bodies.append(body)
        tex = output / (entry["id"] + ".tex")
        tex.write_text(document(body))
        pdf = build_pdf(tex)
        source = module_source_path(entry["module"], root)
        text = source.read_text()
        documents.append({
            "id": entry["id"], "title": entry["title"], "pdf": pdf.name,
            "pdf_sha256": digest(pdf), "source": str(source.relative_to(root)),
            "source_sha256": digest(source), "headlines": [
                {"declaration": name, "line": declaration_line(text, name),
                 "url": source_url(repository, sha, source.relative_to(root),
                                   declaration_line(text, name))}
                for name in entry["headline_theorems"]],
            "supporting_statements": [
                {"declaration": name, "line": declaration_line(text, name),
                 "url": source_url(repository, sha, source.relative_to(root),
                                   declaration_line(text, name))}
                for name in entry.get("supporting_theorems", [])],
        })
    manifest_data = json.loads(Path(manifest).read_text())
    catalogue_title = manifest_data.get("title", "Complexitylib / Formal abstracts")
    index = [r"\section*{" + render.escape_tex_prose(catalogue_title) + "}",
             "Selected proved results, with their definitions and formal statements. "
             "Proof bodies are omitted from the display and remain in the linked Lean sources.",
             r"\begin{itemize}\raggedright"]
    for entry in entries:
        index.append(r"\item{} \hyperlink{" + entry["id"] + "}{" +
                     render.escape_tex_prose(entry["title"]) + "}. " +
                     render.escape_tex_prose(entry["summary"]))
    index.extend([r"\end{itemize}", r"\clearpage"])
    catalogue = output / "catalogue.tex"
    catalogue.write_text(document("\n\n".join(index) + "\n\\clearpage\n".join(bodies)))
    catalogue_pdf = build_pdf(catalogue)
    event_path = os.environ.get("GITHUB_EVENT_PATH")
    event = json.loads(Path(event_path).read_text()) if event_path else {}
    pr = event.get("pull_request", {})
    for record in input_records:
        if digest(root / record["path"]) != record["sha256"]:
            raise ValueError(f"Source changed during PDF generation: {record['path']}")
    provenance = {
        "source_sha": sha, "source_dirty": dirty, "repository": repository,
        "event": os.environ.get("GITHUB_EVENT_NAME", "local"), "ref": os.environ.get("GITHUB_REF"),
        "pull_request_number": pr.get("number"),
        "pull_request_head_sha": pr.get("head", {}).get("sha"),
        "pull_request_base_sha": pr.get("base", {}).get("sha"),
        "run_url": (f"https://github.com/{repository}/actions/runs/{os.environ['GITHUB_RUN_ID']}"
                    if os.environ.get("GITHUB_RUN_ID") else None),
        "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "catalogue": {"pdf": "catalogue.pdf", "pdf_sha256": digest(catalogue_pdf)},
        "documents": documents,
        "inputs": input_records,
        "style_sources": [STYLE_SOURCE, EXTRACTION_SOURCE],
    }
    (output / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    print(f"Built {len(documents)} individual PDFs and {catalogue_pdf} from {sha}")
    return provenance


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, default=ROOT / "abstracts/catalogue.json")
    parser.add_argument("--output", type=Path, default=ROOT / "abstracts/build")
    parser.add_argument("--check", action="store_true", help="validate selection without building PDFs")
    parser.add_argument("--require-clean", action="store_true")
    args = parser.parse_args()
    try:
        if args.check:
            entries = load_catalogue(args.manifest)
            print(f"Catalogue selects {len(entries)} abstracts and "
                  f"{sum(len(e['headline_theorems']) for e in entries)} headline theorems.")
        else:
            build(args.manifest, args.output, require_clean=args.require_clean)
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        parser.exit(1, f"Abstract build failed: {error}\n")


if __name__ == "__main__":
    main()
