#!/usr/bin/env python3
"""Compare #573's list-topic transitive importers over the base's fixed library universe.

Uses the existing native Lean header parser and shared quality-report graph calculation.
Counts source-import reach, not actual rebuilds, cache hits or elapsed build time.
"""

import argparse
import io
from pathlib import Path
import subprocess
import tarfile
import tempfile

from quality_report import transitive_importers
from quick_check import imports_from_lean

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "Complexity.Foundations.Data.List."
TOPICS = ("Append", "Counting", "Fold", "Lookup")


def snapshot(ref: str, destination: Path) -> dict[str, list[tuple[str, bool]]]:
    archive = subprocess.check_output(["git", "archive", ref, "Complexity"], cwd=ROOT)
    sources = {}
    with tarfile.open(fileobj=io.BytesIO(archive)) as files:
        for entry in files:
            if entry.isfile() and entry.name.endswith(".lean"):
                path = destination / entry.name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_bytes(files.extractfile(entry).read())
                sources[str(path)] = entry.name[:-5].replace("/", ".")
    parsed = imports_from_lean(ROOT, list(sources))
    # Publicness does not affect transitive source-import reach.
    return {sources[path]: [(module, False) for module in modules]
            for path, modules in parsed.items()}


def fixed_scope_counts(base: dict, head: dict) -> tuple[int, dict[str, int]]:
    """Walk all head edges, including new modules, then count only original library modules."""
    scope = set(base)
    before, after = transitive_importers(base), transitive_importers(head)
    return len(before[PREFIX + "Basic"] & scope), {
        topic: len(after[PREFIX + topic] & scope) for topic in ("Basic", *TOPICS)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", required=True, help="original library revision")
    parser.add_argument("--head", default="HEAD", help="committed split revision")
    args = parser.parse_args()
    refs = [subprocess.check_output(["git", "rev-parse", "--verify", ref + "^{commit}"],
                                   cwd=ROOT, text=True).strip()
            for ref in (args.base, args.head)]
    with tempfile.TemporaryDirectory(prefix="list-split-fanout-") as temporary:
        base = snapshot(refs[0], Path(temporary) / "base")
        head = snapshot(refs[1], Path(temporary) / "head")
    missing = {PREFIX + topic for topic in ("Basic", *TOPICS)} - head.keys()
    if missing:
        parser.error("head lacks split modules: " + ", ".join(sorted(missing)))
    before, after = fixed_scope_counts(base, head)
    print(f"Base {refs[0]}; head {refs[1]}")
    print(f"Fixed original library scope: {len(base)} modules")
    print(f"Before Basic: {before} transitive importers")
    for topic, count in after.items():
        print(f"After {topic}: {count} transitive importers")


if __name__ == "__main__":
    main()
