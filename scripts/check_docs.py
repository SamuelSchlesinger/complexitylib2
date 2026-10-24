#!/usr/bin/env python3
"""Check documentation pins, module/search coverage and the guide's links (Python 3.11+)."""

import argparse
from contextlib import closing
import html
import json
from pathlib import Path
import posixpath
import re
import shutil
import sqlite3
import tempfile
import tomllib
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
CORE_ROOTS = ("Init", "Std", "Lean", "Lake")
LOCAL_DECLARATION_PREFIXES = (
    "./Complexity/",
    "./Complexity.html",
    "./Cslib/",
    "./Cslib.html",
)
HREF_RE = re.compile(r'href="([^"]*)"')
IMPORT_ITEM_RE = re.compile(r'<li><a href="([^"]+)">[^<]*</a></li>')
EMPTY_IMPORTS_DETAILS_RE = re.compile(r'<details><summary>Imports</summary><ul></ul></details>')
DEP_BROKEN_LINK_RE = re.compile(
    r'<code><a href="([^"]+)">([^<]*\.lean)</a></code>'
    r'|<a href="([^"]+)">(<code>[^<]+</code>)</a>'
    r'|<a href="([^"]*(?:lean-manual://|\.lean|/fderiv\.html)[^"]*)">([^<]*)</a>'
)
NAV_LINK_RE = re.compile(
    r'<div class="nav_link"><a href="\./([^"]+)">[^<]*</a></div>'
    r'|\s*\(<a href="\./([^"]+)">file</a>\)'
)
EMPTY_NAV_SECT_RE = re.compile(
    r'<details class="nav_sect"[^>]*><summary>[^<]*</summary></details>'
)


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


def resolve_relative_href(rel_page, href):
    if not href:
        return None
    split = urlsplit(html.unescape(href))
    if split.scheme or split.netloc or not split.path:
        return None
    page_dir = posixpath.dirname(rel_page)
    raw_path = unquote(split.path)
    joined = posixpath.join(page_dir, raw_path) if page_dir else raw_path
    return posixpath.normpath(joined)


def resolve_doc_target(docs, norm_path):
    if not norm_path or norm_path == ".." or norm_path.startswith(("/", "../")):
        return None
    docs_root = docs.resolve()
    target = docs_root / ("index.html" if norm_path == "." else norm_path)
    if target.is_dir():
        target = target / "index.html"
    resolved = target.resolve()
    if not resolved.is_relative_to(docs_root):
        return None
    return resolved


def is_published_doc_file(docs, norm_path):
    target = resolve_doc_target(docs, norm_path)
    return target is not None and target.is_file()


def strip_imports_div(text):
    start = text.find('<div class="imports">')
    if start == -1:
        return text
    end = text.find("</div>", start)
    return text[:start] + text[end + 6:] if end != -1 else text


def imported_module_closure(docs, modules):
    imports = {}
    for module, info in modules.items():
        for importer in info.get("importedBy", ()):
            imports.setdefault(importer, []).append(module)

    closure = set()
    stack = [module for module in modules if module.split(".", 1)[0] not in CORE_ROOTS]
    while stack:
        module = stack.pop()
        if module in closure:
            continue
        closure.add(module)
        for imported in imports.get(module, ()):
            if imported not in closure and imported in modules:
                stack.append(imported)

    page_to_module = {module.replace(".", "/") + ".html": module for module in modules}
    non_module_pages = [
        page.relative_to(docs).as_posix()
        for page in sorted(docs.rglob("*.html"))
        if page.is_file()
        and page.relative_to(docs).as_posix() not in page_to_module
        and page.relative_to(docs).as_posix() != "navbar.html"
    ] if docs.is_dir() else []
    page_queue = [
        module.replace(".", "/") + ".html" for module in sorted(closure)
    ] + non_module_pages
    scanned_pages = set()
    while page_queue:
        rel_page = page_queue.pop()
        if rel_page in scanned_pages:
            continue
        scanned_pages.add(rel_page)
        page = docs / rel_page
        if not page.is_file():
            continue
        text = strip_imports_div(page.read_text())
        for raw_href in dict.fromkeys(html.unescape(h).partition("#")[0] for h in HREF_RE.findall(text)):
            norm = resolve_relative_href(rel_page, raw_href)
            target_module = page_to_module.get(norm) if norm else None
            if target_module and target_module not in closure:
                closure.add(target_module)
                page_queue.append(norm)
    return closure


def remove_empty_parents(path, stop):
    parent = path.parent
    while parent != stop and parent.exists():
        try:
            parent.rmdir()
        except OSError:
            break
        parent = parent.parent


def trim_navbar(navbar_path, pruned_pages):
    if not navbar_path.is_file() or not pruned_pages:
        return
    text = navbar_path.read_text()
    text = NAV_LINK_RE.sub(
        lambda m: "" if (m.group(1) or m.group(2)) in pruned_pages else m.group(0),
        text,
    )
    while EMPTY_NAV_SECT_RE.search(text):
        text = EMPTY_NAV_SECT_RE.sub("", text)
    navbar_path.write_text(text)


def trim_module_imports(docs, pruned_pages):
    if not docs.is_dir() or not pruned_pages:
        return
    for page in sorted(docs.rglob("*.html")):
        if not page.is_file() or page.name == "navbar.html":
            continue
        text = page.read_text()
        start = text.find('<div class="imports">')
        if start == -1:
            continue
        end = text.find("</div>", start)
        if end == -1:
            continue
        rel_page = page.relative_to(docs).as_posix()
        block = text[start:end + 6]
        updated_block = IMPORT_ITEM_RE.sub(
            lambda m: (
                "" if resolve_relative_href(rel_page, m.group(1)) in pruned_pages else m.group(0)
            ),
            block,
        )
        updated_block = EMPTY_IMPORTS_DETAILS_RE.sub("", updated_block)
        if updated_block != block:
            page.write_text(text[:start] + updated_block + text[end + 6:])


def sanitize_dependency_code_links(docs, modules=()):
    if not docs.is_dir():
        return
    page_to_module = {module.replace(".", "/") + ".html": module for module in modules}
    for page in sorted(docs.rglob("*.html")):
        if not page.is_file():
            continue
        rel_page = page.relative_to(docs).as_posix()
        if rel_page in ("Complexity.html", "navbar.html") or rel_page.startswith("Complexity/"):
            continue
        text = page.read_text()
        if (
            ".lean" not in text
            and "><code>" not in text
            and "lean-manual://" not in text
            and "/fderiv.html" not in text
        ):
            continue

        def replace_link(match):
            href = match.group(1) or match.group(3) or match.group(5)
            label = (
                f"<code>{match.group(2)}</code>"
                if match.group(2) is not None
                else (match.group(4) or match.group(6))
            )
            norm = resolve_relative_href(rel_page, href)
            if norm and norm not in page_to_module and not is_published_doc_file(docs, norm):
                return label
            return match.group(0)

        updated = DEP_BROKEN_LINK_RE.sub(replace_link, text)
        if updated != text:
            page.write_text(updated)


def trim_output():
    docs = ROOT / "docbuild/.lake/build/doc"
    index_path = docs / "declarations/declaration-data.bmp"
    require(index_path.is_file(), "Missing documentation output: declarations/declaration-data.bmp")
    index = json.loads(index_path.read_text())
    modules = index["modules"]
    closure = imported_module_closure(docs, modules)
    pruned_modules = {
        module for module in modules
        if module.split(".", 1)[0] in CORE_ROOTS and module not in closure
    }
    kept_modules = set(modules) - pruned_modules
    pruned_pages = {module.replace(".", "/") + ".html" for module in pruned_modules}

    for rel_page in sorted(pruned_pages):
        page = docs / rel_page
        if page.is_file():
            page.unlink()
            remove_empty_parents(page, docs)

    trim_navbar(docs / "navbar.html", pruned_pages)
    trim_module_imports(docs, pruned_pages)
    sanitize_dependency_code_links(docs, modules)

    kept_declarations = {
        name: info for name, info in index.get("declarations", {}).items()
        if info.get("docLink", "").startswith(LOCAL_DECLARATION_PREFIXES)
    }
    kept_instances = {
        name: [inst for inst in items if inst in kept_declarations]
        for name, items in index.get("instances", {}).items()
    }
    kept_instances = {name: items for name, items in kept_instances.items() if items}
    kept_instances_for = {
        name: [inst for inst in items if inst in kept_declarations]
        for name, items in index.get("instancesFor", {}).items()
    }
    kept_instances_for = {name: items for name, items in kept_instances_for.items() if items}
    kept_modules_dict = {
        module: {
            **info,
            **({"importedBy": [imp for imp in info["importedBy"] if imp in kept_modules]}
               if "importedBy" in info else {}),
        }
        for module, info in modules.items()
        if module in kept_modules
    }
    trimmed_index = {
        **index,
        "declarations": kept_declarations,
        "modules": kept_modules_dict,
    }
    if "instances" in index:
        trimmed_index["instances"] = kept_instances
    if "instancesFor" in index:
        trimmed_index["instancesFor"] = kept_instances_for
    index_path.write_text(json.dumps(trimmed_index, ensure_ascii=False, separators=(",", ":")))


def check_internal_links(docs):
    pages = sorted(page for page in docs.rglob("*.html") if page.is_file())
    checked_targets = {}
    for page in pages:
        rel_page = page.relative_to(docs).as_posix()
        for raw_href in dict.fromkeys(html.unescape(h).partition("#")[0] for h in HREF_RE.findall(page.read_text())):
            norm = resolve_relative_href(rel_page, raw_href)
            if norm is None:
                continue
            exists = checked_targets.get(norm)
            if exists is None:
                exists = is_published_doc_file(docs, norm)
                checked_targets[norm] = exists
            require(exists, f"Broken internal link in {rel_page}: {norm}")


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
    check_internal_links(docs)
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
    parser.add_argument("--trim", action="store_true",
                        help="prune unimported core pages and trim declaration data before checking")
    parser.add_argument("--guide", action="store_true",
                        help="also check the built guide's links into the built documentation")
    args = parser.parse_args()
    try:
        check_config()
        if args.config_only:
            print("Documentation configuration is consistent.")
        else:
            if args.trim:
                trim_output()
            check_output()
            if args.guide:
                check_guide_links()
    except (OSError, ValueError, KeyError, StopIteration, sqlite3.Error) as error:
        parser.exit(1, f"Documentation check failed: {error}\n")


if __name__ == "__main__":
    main()
