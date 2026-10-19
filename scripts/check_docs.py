#!/usr/bin/env python3
"""Check documentation pins and generated module/search coverage (Python 3.11+)."""

import argparse
import html
import json
from pathlib import Path
import re
import tomllib
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


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


def check_bibliography_keys(bibliography):
    # BibTeX keys are case-insensitive; cslib pads some keys with spaces.
    keys = [key.lower() for key in
            re.findall(r"^@\w+\s*\{\s*([^,\s]+)\s*,", bibliography, re.MULTILINE)]
    duplicates = sorted({key for key in keys if keys.count(key) > 1})
    require(not duplicates, f"Duplicate bibliography keys: {', '.join(duplicates)}")


def check_output():
    docs = ROOT / "docbuild/.lake/build/doc"
    for name in ("index.html", "search.html", "search.js", "declaration-data.js",
                 "references.html", "references.bib", "find/index.html"):
        require((docs / name).is_file(), f"Missing documentation output: {name}")
    # doc-gen4 uses a .bmp extension for its JSON search index.
    index = json.loads((docs / "declarations/declaration-data.bmp").read_text())
    sources = [ROOT / "Complexity.lean", *sorted((ROOT / "Complexity").rglob("*.lean"))]
    for source in sources:
        module = ".".join(source.relative_to(ROOT).with_suffix("").parts)
        require(module in index["modules"], f"Missing module in search index: {module}")
        page = docs / source.relative_to(ROOT).with_suffix(".html")
        require(page.is_file(), f"Missing module page: {module}")
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
                        help="check pins before invoking Lake; do not require built documentation")
    args = parser.parse_args()
    try:
        check_config()
        if args.config_only:
            print("Documentation configuration is consistent.")
        else:
            check_output()
    except (OSError, ValueError, KeyError, StopIteration) as error:
        parser.exit(1, f"Documentation check failed: {error}\n")


if __name__ == "__main__":
    main()
