#!/usr/bin/env python3
"""Check documentation pins, Markdown links/anchors/modules, and generated search coverage (Python 3.11+)."""

import argparse
from contextlib import closing
import html
import json
from pathlib import Path
import re
import shutil
import sqlite3
import tempfile
import tomllib
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]

MARKDOWN_DOCS = (
    "README.md",
    "ROADMAP.md",
    "AGENTS.md",
    "CONTRIBUTING.md",
    "UPSTREAM.md",
    "paper/README.md",
)

COMPLEXITY_TOP_DIRS = (
    "Algorithms",
    "Computability",
    "Crypto",
    "Foundations",
    "Logics",
    "MachineLearning",
    "Probability",
    "Tactic",
)

HISTORICAL_MARKER_RE = re.compile(
    r"(?:\*\*Renamed modules|\(historical\)|\(renamed\)|\(removed\)|"
    r"<!--\s*(?:historical|renamed|removed)\s*-->)",
    re.IGNORECASE,
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def gfm_heading_slug(heading_text):
    text = re.sub(r"(?<!!)\[([^\]]+)\]\([^)]+\)", r"\1", heading_text)
    text = text.replace("`", "")
    text = re.sub(r"(?<!\w)[*_]+|[*_]+(?!\w)", "", text)
    text = text.strip().lower()
    cleaned = "".join(ch for ch in text if ch.isalnum() or ch in "-_ ")
    return cleaned.replace(" ", "-")


def extract_markdown_headings(md_path):
    slugs = set()
    counts = {}
    in_fence = False
    for line in md_path.read_text(encoding="utf-8").splitlines():
        if re.match(r"^\s*(?:```|~~~)", line):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        match = re.match(r"^#{1,6}\s+(.*?)\s*#*$", line)
        if not match:
            continue
        base = gfm_heading_slug(match.group(1))
        if not base:
            continue
        idx = counts.get(base, 0)
        counts[base] = idx + 1
        slugs.add(base if idx == 0 else f"{base}-{idx}")
    return slugs


def parse_imported_modules(lean_root_file, prefix="Complexity"):
    if not lean_root_file.is_file():
        return set()
    pattern = rf"^\s*(?:public\s+)?import\s+({re.escape(prefix)}(?:\.[A-Za-z0-9_']+)+)\s*$"
    return set(re.findall(pattern, lean_root_file.read_text(encoding="utf-8"), re.MULTILINE))


def expand_braces(expr):
    match = re.search(r"\{([^{}]+)\}", expr)
    if not match:
        return [expr]
    prefix = expr[:match.start()]
    suffix = expr[match.end():]
    expanded = []
    for item in match.group(1).split(","):
        expanded.extend(expand_braces(prefix + item.strip() + suffix))
    return expanded


def is_candidate_module_span(span):
    if not span or " " in span or span in ("Complexity/", "Complexity.", ".lean"):
        return False
    if re.match(r"^Complexity(?:\.[A-Z][A-Za-z0-9_']*)+$", span):
        return True
    if "/" not in span:
        return False
    if span.startswith("Complexity/"):
        return len(span) > len("Complexity/")
    first_seg = span.split("/", 1)[0]
    return first_seg in COMPLEXITY_TOP_DIRS


def resolve_complexity_reference(root, raw_ref):
    complexity_dir = root / "Complexity"
    ref = raw_ref.strip()
    if ref.startswith("Complexity.") and "/" not in ref:
        rel = Path(*ref.split(".")[1:]).with_suffix(".lean")
        candidate = complexity_dir / rel
        if candidate.is_file():
            return [candidate]
        return []

    if ref.startswith("Complexity/"):
        ref = ref[len("Complexity/"):]
    ref = ref.rstrip("/")
    if not ref:
        return []

    if ref.endswith(".lean"):
        candidate = complexity_dir / ref
        return [candidate] if candidate.is_file() else []

    file_candidate = complexity_dir / f"{ref}.lean"
    dir_candidate = complexity_dir / ref
    found = []
    if file_candidate.is_file():
        found.append(file_candidate)
    if dir_candidate.is_dir():
        found.extend(sorted(dir_candidate.rglob("*.lean")))
    return found


def check_markdown_docs(root=None):
    root = (root or ROOT).resolve()
    complexity_dir = root / "Complexity"
    tests_dir = root / "ComplexityTests"
    imported_modules = parse_imported_modules(root / "Complexity.lean", "Complexity")
    imported_test_modules = parse_imported_modules(root / "ComplexityTests.lean", "ComplexityTests")
    heading_cache = {}

    def headings_for(path):
        resolved = path.resolve()
        if resolved not in heading_cache:
            heading_cache[resolved] = extract_markdown_headings(resolved)
        return heading_cache[resolved]

    for rel_doc in MARKDOWN_DOCS:
        md_path = root / rel_doc
        require(md_path.is_file(), f"Missing documentation file: {rel_doc}")
        in_fence = False
        for lineno, line in enumerate(md_path.read_text(encoding="utf-8").splitlines(), 1):
            if re.match(r"^\s*(?:```|~~~)", line):
                in_fence = not in_fence
                continue
            if in_fence:
                continue

            for match in re.finditer(r"(?<!!)\[([^\]]+)\]\(([^)]+)\)", line):
                target = match.group(2).strip()
                parts = urlsplit(target)
                if parts.scheme in ("http", "https", "mailto"):
                    continue
                require(parts.scheme == "" and parts.netloc == "",
                        f"{rel_doc}:{lineno}: unsupported link scheme in {target}")
                rel_target = unquote(parts.path)
                fragment = unquote(parts.fragment)
                target_path = (md_path.parent / rel_target).resolve() if rel_target else md_path.resolve()
                require(target_path.is_relative_to(root),
                        f"{rel_doc}:{lineno}: link escapes repository root: {target}")
                require(target_path.exists(),
                        f"{rel_doc}:{lineno}: missing link target: {target}")

                if target_path.is_file() and target_path.suffix == ".lean":
                    if target_path.is_relative_to(complexity_dir):
                        module = ".".join(target_path.relative_to(root).with_suffix("").parts)
                        require(module in imported_modules,
                                f"{rel_doc}:{lineno}: module not imported in Complexity.lean: {module}")
                    elif imported_test_modules and target_path.is_relative_to(tests_dir):
                        module = ".".join(target_path.relative_to(root).with_suffix("").parts)
                        require(module in imported_test_modules,
                                f"{rel_doc}:{lineno}: test module not imported in ComplexityTests.lean: {module}")

                if fragment and target_path.is_file() and target_path.suffix.lower() == ".md":
                    require(fragment in headings_for(target_path),
                            f"{rel_doc}:{lineno}: missing heading anchor #{fragment} in {target}")

            if rel_doc in ("UPSTREAM.md", "ROADMAP.md"):
                line_has_historical_marker = bool(HISTORICAL_MARKER_RE.search(line))
                became_pos = line.find("became ")
                for match in re.finditer(r"`([^`]+)`", line):
                    if line[match.end():].startswith("]("):
                        continue
                    span = " ".join(match.group(1).split())
                    if not is_candidate_module_span(span):
                        continue
                    is_historical_span = line_has_historical_marker and (
                        became_pos == -1 or match.start() < became_pos
                    )
                    for expanded in expand_braces(span):
                        resolved_files = resolve_complexity_reference(root, expanded)
                        if not resolved_files:
                            if is_historical_span:
                                continue
                            raise ValueError(f"{rel_doc}:{lineno}: missing module path: {expanded}")
                        for lean_file in resolved_files:
                            module = ".".join(lean_file.relative_to(root).with_suffix("").parts)
                            require(module in imported_modules,
                                    f"{rel_doc}:{lineno}: module not imported in Complexity.lean: {module}")


def run_self_test():
    check_markdown_docs(ROOT)
    with tempfile.TemporaryDirectory(prefix="check-docs-selftest-") as tmp:
        root = Path(tmp)

        def write(rel_path, content=""):
            path = root / rel_path
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content, encoding="utf-8")

        def setup_valid_fixture():
            write("Complexity.lean", "public import Complexity.Computability.Valid\n")
            write("Complexity/Computability/Valid.lean", "-- valid module\n")
            write("README.md", "# Complexitylib\n\n## Build and use\n\nSee [ROADMAP.md](ROADMAP.md).\n")
            write("ROADMAP.md",
                  "# Development roadmap\n\n"
                  "## Continuing priorities\n\n"
                  "See [Valid](Complexity/Computability/Valid.lean) and "
                  "[machine milestones](#machine-class-milestones).\n\n"
                  "## Jukna coverage\n\n"
                  "## Machine-class milestones\n\n"
                  "Back to [continuing priorities](#continuing-priorities).\n")
            write("AGENTS.md",
                  "# Project Instructions\n\n"
                  "## Working on changes\n\n"
                  "## Review cycle\n\n"
                  "See [CONTRIBUTING.md](CONTRIBUTING.md#ai-assistance-and-review).\n\n"
                  "## Staying current with upstream\n\n"
                  "## Proof hygiene\n\n"
                  "## Human-readable theorem index\n")
            write("CONTRIBUTING.md",
                  "# Contributing\n\n"
                  "## AI assistance and review\n\n"
                  "See [AGENTS.md](AGENTS.md#review-cycle) and [README](README.md#build-and-use).\n\n"
                  "## Documentation\n\n"
                  "## Maintaining the theorem index\n\n"
                  "## Upstreaming\n")
            write("UPSTREAM.md",
                  "# Upstream integration\n\n"
                  "See [AGENTS.md](AGENTS.md#staying-current-with-upstream) and "
                  "`Computability/Valid`.\n"
                  "* **Renamed modules (historical).** `Computability/OldRemoved` became `Computability/Valid`.\n")
            write("paper/README.md",
                  "# Index of proved statements\n\n"
                  "See [ROADMAP.md](../ROADMAP.md) and [AGENTS.md](../AGENTS.md#human-readable-theorem-index).\n")

        setup_valid_fixture()
        check_markdown_docs(root)

        # Negative case 1: broken local file link
        write("README.md", "# Complexitylib\n\nSee [Missing](Complexity/Computability/Missing.lean).\n")
        try:
            check_markdown_docs(root)
        except ValueError as err:
            require("missing link target" in str(err), f"Unexpected error for broken link: {err}")
        else:
            raise AssertionError("Self-test failed: broken file link was not rejected")

        # Negative case 2: broken same-file heading anchor
        setup_valid_fixture()
        write("ROADMAP.md", "# Development roadmap\n\nSee [bad](#nonexistent-anchor).\n")
        try:
            check_markdown_docs(root)
        except ValueError as err:
            require("missing heading anchor #nonexistent-anchor" in str(err),
                    f"Unexpected error for broken same-file anchor: {err}")
        else:
            raise AssertionError("Self-test failed: broken same-file anchor was not rejected")

        # Negative case 3: broken cross-file heading anchor
        setup_valid_fixture()
        write("CONTRIBUTING.md",
              "# Contributing\n\n## AI assistance and review\n\nSee [bad](AGENTS.md#no-such-heading).\n")
        try:
            check_markdown_docs(root)
        except ValueError as err:
            require("missing heading anchor #no-such-heading" in str(err),
                    f"Unexpected error for broken cross-file anchor: {err}")
        else:
            raise AssertionError("Self-test failed: broken cross-file anchor was not rejected")

        # Negative case 4: existing Complexity/ module not imported in Complexity.lean
        setup_valid_fixture()
        write("Complexity/Computability/Unimported.lean", "-- not in Complexity.lean\n")
        write("ROADMAP.md",
              "# Development roadmap\n\nSee [Unimported](Complexity/Computability/Unimported.lean).\n")
        try:
            check_markdown_docs(root)
        except ValueError as err:
            require("module not imported in Complexity.lean: Complexity.Computability.Unimported" in str(err),
                    f"Unexpected error for unimported module: {err}")
        else:
            raise AssertionError("Self-test failed: unimported Complexity/ module was not rejected")

        # Negative case 5: missing active backticked module path in UPSTREAM.md
        setup_valid_fixture()
        write("UPSTREAM.md", "# Upstream integration\n\nSee `Computability/DoesNotExist`.\n")
        try:
            check_markdown_docs(root)
        except ValueError as err:
            require("missing module path: Computability/DoesNotExist" in str(err),
                    f"Unexpected error for missing backticked module: {err}")
        else:
            raise AssertionError("Self-test failed: missing backticked module path was not rejected")

        # Negative case 6: missing active replacement after 'became' on a Renamed modules line
        setup_valid_fixture()
        write("UPSTREAM.md",
              "# Upstream integration\n\n"
              "* **Renamed modules (historical).** `Computability/OldRemoved` became `Computability/MissingNew`.\n")
        try:
            check_markdown_docs(root)
        except ValueError as err:
            require("missing module path: Computability/MissingNew" in str(err),
                    f"Unexpected error for missing replacement module: {err}")
        else:
            raise AssertionError("Self-test failed: missing replacement module on historical line was not rejected")

    print("Self-test passed (all positive and negative checks verified).")


def check_config():
    root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    docs_manifest = json.loads((ROOT / "docbuild/lake-manifest.json").read_text())
    docs_packages = {p["name"].strip("«»"): p for p in docs_manifest["packages"]}
    for package in root_manifest["packages"]:
        locked = docs_packages.get(package["name"])
        require(locked is not None, f"Documentation lockfile omits {package['name']}")
        for key in ("type", "url", "rev", "subDir"):
            require(package.get(key) == locked.get(key),
                    f"Documentation lockfile differs for {package['name']}: {key}")

    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    require((ROOT / "docbuild/lean-toolchain").read_text().strip() == toolchain,
            "Documentation toolchain differs from the library")
    config = tomllib.loads((ROOT / "docbuild/lakefile.toml").read_text())
    generator = next(p for p in config["require"] if p["name"] == "doc-gen4")
    version = toolchain.rsplit(":", 1)[-1]
    require(generator["rev"] == version, "doc-gen4 tag must match the Lean version")
    require(docs_packages["doc-gen4"]["inputRev"] == generator["rev"],
            "Documentation lockfile has a stale doc-gen4 tag")
    require((ROOT / "docbuild/docs/references.bib").read_bytes()
            == (ROOT / "references.bib").read_bytes(),
            "Documentation bibliography differs from references.bib")
    check_bibliography_keys((ROOT / "references.bib").read_text())
    if (ROOT / "README.md").is_file():
        check_markdown_docs(ROOT)


def check_bibliography_keys(bibliography):
    # BibTeX keys are case-insensitive; cslib pads some keys with spaces.
    keys = [key.lower() for key in
            re.findall(r"^@\w+\s*\{\s*([^,\s]+)\s*,", bibliography, re.MULTILINE)]
    duplicates = sorted({key for key in keys if keys.count(key) > 1})
    require(not duplicates, f"Duplicate bibliography keys: {', '.join(duplicates)}")


def local_modules(names):
    return {name for name in names if name == "Complexity" or name.startswith("Complexity.")}


def check_module_inventory(names, expected, label):
    actual = local_modules(names)
    obsolete = sorted(actual - expected)
    missing = sorted(expected - actual)
    require(not obsolete, f"Obsolete modules in {label}: {', '.join(obsolete)}")
    require(not missing, f"Missing modules in {label}: {', '.join(missing)}")


def check_intermediate_modules(build, expected):
    # Pinned doc-gen4's htmlOutputIndex/headerDataOutput merge these files on
    # incremental builds, even when the assembled index currently looks clean.
    prefix = "declaration-data-"
    names = (path.name[len(prefix):-len(".bmp")]
             for path in (build / "doc-data").glob(f"{prefix}*.bmp") if path.is_file())
    check_module_inventory(names, expected, "per-module declaration data")
    # DocGen4/DB/Schema.lean defines modules(name PRIMARY KEY, source_url).
    # Even mode=ro can create WAL/SHM files. Inspect a private snapshot of completed
    # output, including committed WAL rows; immutable=1 on the main file loses those.
    database = build / "api-docs.db"
    require(database.is_file(), "Missing documentation database: api-docs.db")
    with tempfile.TemporaryDirectory(prefix="check-docs-") as temporary:
        snapshot = Path(temporary) / database.name
        shutil.copyfile(database, snapshot)
        wal = database.with_name(database.name + "-wal")
        if wal.is_file():
            shutil.copyfile(wal, snapshot.with_name(snapshot.name + "-wal"))
        with closing(sqlite3.connect(snapshot.as_uri() + "?mode=ro", uri=True)) as db:
            names = (row[0] for row in db.execute("SELECT name FROM modules"))
            check_module_inventory(names, expected, "documentation database")


def check_output():
    docs = ROOT / "docbuild/.lake/build/doc"
    for name in ("index.html", "search.html", "search.js", "declaration-data.js",
                 "references.html", "references.bib", "find/index.html"):
        require((docs / name).is_file(), f"Missing documentation output: {name}")
    # doc-gen4 uses a .bmp extension for its JSON search index.
    index = json.loads((docs / "declarations/declaration-data.bmp").read_text())
    sources = [ROOT / "Complexity.lean", *sorted((ROOT / "Complexity").rglob("*.lean"))]
    expected_modules = {
        ".".join(source.relative_to(ROOT).with_suffix("").parts) for source in sources
    }
    # Reused doc-gen4 caches can retain removed modules. Dependency docs are allowed.
    stale_modules = sorted(local_modules(index["modules"]) - expected_modules)
    require(not stale_modules,
            f"Obsolete modules in search index: {', '.join(stale_modules)}")
    local_pages = {
        ".".join(page.relative_to(docs).with_suffix("").parts)
        for page in (docs / "Complexity").rglob("*.html") if page.is_file()
    }
    stale_pages = sorted(local_pages - expected_modules)
    require(not stale_pages, f"Obsolete module pages: {', '.join(stale_pages)}")
    for source in sources:
        module = ".".join(source.relative_to(ROOT).with_suffix("").parts)
        require(module in index["modules"], f"Missing module in search index: {module}")
        page = docs / source.relative_to(ROOT).with_suffix(".html")
        require(page.is_file(), f"Missing module page: {module}")
    check_intermediate_modules(docs.parent, expected_modules)
    for name in ("Cslib.Complexity.CookLevin.SAT_npComplete",
                 "Cslib.Complexity.NP_eq_PCP_log",
                 "Cslib.Crypto.OneWay.exists_pseudorandomFunction"):
        require(name in index["declarations"], f"Missing theorem in search index: {name}")
        link = urlsplit(index["declarations"][name]["docLink"])
        page = docs / unquote(link.path)
        anchor = html.escape(unquote(link.fragment), quote=True)
        require(f'id="{anchor}"' in page.read_text(), f"Missing theorem anchor: {name}")
    print(f"Documentation covers {len(sources)} modules and representative theorem search entries.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config-only", action="store_true",
                        help="check pins and Markdown docs before invoking Lake; do not require built documentation")
    parser.add_argument("--markdown-only", action="store_true",
                        help="check Markdown links, heading anchors, and module references only")
    parser.add_argument("--self-test", action="store_true",
                        help="run deterministic positive and negative self-tests for Markdown and module checks")
    args = parser.parse_args()
    try:
        if args.self_test:
            run_self_test()
        elif args.markdown_only:
            check_markdown_docs(ROOT)
            print("Markdown documentation links and module references are consistent.")
        else:
            check_config()
            if args.config_only:
                print("Documentation configuration is consistent.")
            else:
                check_output()
    except (OSError, ValueError, KeyError, StopIteration, sqlite3.Error) as error:
        parser.exit(1, f"Documentation check failed: {error}\n")


if __name__ == "__main__":
    main()

