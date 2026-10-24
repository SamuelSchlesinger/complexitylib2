#!/usr/bin/env python3
"""Check documentation pins, module/search coverage and the guide's links (Python 3.11+)."""

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


def require(condition, message):
    if not condition:
        raise ValueError(message)


LOCKED_KEYS = ("type", "url", "rev", "subDir")


def check_project(project, label, generator_name, root_packages, toolchain):
    """Check a documentation project that shares the library's toolchain and package checkouts."""
    manifest = json.loads((ROOT / project / "lake-manifest.json").read_text())
    packages = {p["name"].strip("«»"): p for p in manifest["packages"]}
    for package in root_packages:
        locked = packages.get(package["name"])
        require(locked is not None, f"{label} lockfile omits {package['name']}")
        for key in LOCKED_KEYS:
            require(package.get(key) == locked.get(key),
                    f"{label} lockfile differs for {package['name']}: {key}")
    require((ROOT / project / "lean-toolchain").read_text().strip() == toolchain,
            f"{label} toolchain differs from the library")
    config = tomllib.loads((ROOT / project / "lakefile.toml").read_text())
    generator = next(p for p in config["require"] if p["name"] == generator_name)
    require(generator["rev"] == toolchain.rsplit(":", 1)[-1],
            f"{generator_name} tag must match the Lean version")
    require(packages[generator_name]["inputRev"] == generator["rev"],
            f"{label} lockfile has a stale {generator_name} tag")
    return packages


def check_config():
    root_manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    docs_packages = check_project("docbuild", "Documentation", "doc-gen4",
                                  root_manifest["packages"], toolchain)
    guide_packages = check_project("guide", "Guide", "verso", root_manifest["packages"], toolchain)
    # Both projects check out their packages into the library's .lake/packages.
    for name in sorted(docs_packages.keys() & guide_packages.keys()):
        for key in LOCKED_KEYS:
            require(docs_packages[name].get(key) == guide_packages[name].get(key),
                    f"Guide and documentation lockfiles differ for {name}: {key}")
    require((ROOT / "docbuild/docs/references.bib").read_bytes()
            == (ROOT / "references.bib").read_bytes(),
            "Documentation bibliography differs from references.bib")
    check_bibliography_keys((ROOT / "references.bib").read_text())


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


# Where the guide links declarations (guide/ComplexityGuide/ApiDocs.lean).
API_DOCS_URL = "https://www.cslib.io/complexitylib/"


def check_guide_links():
    docs = ROOT / "docbuild/.lake/build/doc"
    pages = sorted((ROOT / "guide/.lake/build/site/html-multi").rglob("*.html"))
    require(pages, "Missing guide output")
    link = re.compile(r'href="' + re.escape(API_DOCS_URL) + r'([^"]*)"')
    anchors = {}
    links = set()
    for page in pages:
        links.update(html.unescape(target) for target in link.findall(page.read_text()))
    for target in sorted(links):
        path, _, fragment = target.partition("#")
        file = docs / (unquote(path) or "index.html")
        require(file.is_file(), f"Guide links to a missing documentation page: {path}")
        if fragment:
            if file not in anchors:
                ids = re.findall(r'id="([^"]*)"', file.read_text())
                anchors[file] = {html.unescape(i) for i in ids}
            require(unquote(fragment) in anchors[file],
                    f"Guide links to a missing documentation anchor: {target}")
    print(f"The guide's {len(links)} links into the documentation resolve.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config-only", action="store_true",
                        help="check pins before invoking Lake; do not require built documentation")
    parser.add_argument("--guide", action="store_true",
                        help="also check the built guide's links into the built documentation")
    args = parser.parse_args()
    try:
        check_config()
        if args.config_only:
            print("Documentation configuration is consistent.")
        else:
            check_output()
            if args.guide:
                check_guide_links()
    except (OSError, ValueError, KeyError, StopIteration, sqlite3.Error) as error:
        parser.exit(1, f"Documentation check failed: {error}\n")


if __name__ == "__main__":
    main()
