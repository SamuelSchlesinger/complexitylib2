#!/usr/bin/env python3
"""Check every elaborated tidy certificate against the same-budget plain fun_prop search.

Uses the exact registry from PlainMirror, never a guessed counterpart name. Run after building
all three libraries and any requested mirror sidecar. Unsupported notions remain output rows;
a partial run is marked incomplete. This is a certificate check, not a quality metric system.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
import tomllib

ROOT = Path(__file__).resolve().parents[1]
LIBRARIES = ("Complexity", "ComplexityTests", "ComplexityAbstracts")
RUNNER = "scripts/PlainCertificateInventory.lean"
CORE = "Complexity.Tactic.PlainMirror"


def discover_sources(root: Path) -> dict[str, Path]:
    """Enumerate source modules, including private/test/abstract clients and custom srcDirs."""
    config = tomllib.loads((root / "lakefile.toml").read_text())
    libraries = {row["name"]: row for row in config.get("lean_lib", [])}
    result: dict[str, Path] = {}
    for name in LIBRARIES:
        if name not in libraries:
            raise ValueError(f"missing library {name}")
        row = libraries[name]
        src = root / row.get("srcDir", ".")
        base = src.joinpath(*name.split("."))
        paths = [base.with_suffix(".lean"), *sorted(base.rglob("*.lean"))]
        for path in paths:
            if not path.is_file():
                continue
            if path.is_symlink():
                raise ValueError(f"source symlink is not a stable snapshot: {path}")
            module = ".".join(path.relative_to(src).with_suffix("").parts)
            if module in result:
                raise ValueError(f"duplicate module {module}")
            result[module] = path
    return result


def validate_ileans(root: Path, sources: dict[str, Path]) -> None:
    """Require a current-schema reference artifact for every enumerated module."""
    build = root / ".lake/build/lib/lean"
    for module in sources:
        path = build.joinpath(*module.split(".")).with_suffix(".ilean")
        data = json.loads(path.read_text())
        if data.get("version") != 5 or data.get("module") != module:
            raise ValueError(f"unsupported or mismatched .ilean: {path}")


def validate_rows(rows: list[dict]) -> dict:
    """Fail closed on truncated/duplicate/unaccounted-for inventory output."""
    if not rows or "inventory_total" not in rows[0]:
        raise ValueError("missing inventory header")
    header, records = rows[0], rows[1:]
    expected = min(header["inventory_total"], header["limit"] or header["inventory_total"])
    if len(records) != expected:
        raise ValueError(f"truncated inventory: expected {expected}, got {len(records)}")
    names = [row["declaration"]["name"] for row in records]
    if len(set(names)) != len(names):
        raise ValueError("duplicate certificate rows")
    statuses = Counter()
    pairs = Counter()
    for row in records:
        status = row["status"]
        if status not in {"compared", "unsupported_tidy", "transform_error", "non_proposition"}:
            raise ValueError(f"unknown status {status}")
        statuses[status] += 1
        if status == "compared":
            for arm in ("tidy_holdout", "plain_holdout"):
                attempt = row[arm]
                if attempt["status"] not in {"success", "failed", "error"}:
                    raise ValueError(f"unknown attempt {attempt['status']}")
                if not isinstance(attempt["heartbeats_raw"], int) or attempt["heartbeats_raw"] < 0:
                    raise ValueError("invalid heartbeat count")
            pairs[(row["tidy_holdout"]["status"], row["plain_holdout"]["status"])] += 1
        elif status == "unsupported_tidy" and not row["residual_tidy"]:
            raise ValueError("unsupported certificate without an explicit residual predicate")
    return {
        "inventory_total": header["inventory_total"], "records": len(records),
        "inventory_complete": len(records) == header["inventory_total"],
        "statuses": dict(statuses),
        "holdout_pairs": {f"tidy:{a}/plain:{b}": n for (a, b), n in sorted(pairs.items())},
        "registration_probes": sum("plain_registration" in row for row in records),
    }


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--extra-import", action="append", default=[],
                        help="mirror sidecar module; built outputs must already be current")
    parser.add_argument("--heartbeats", type=int, default=200000)
    parser.add_argument("--limit", type=int, default=0, help="debug subset; 0 inventories all")
    args = parser.parse_args()
    if args.limit < 0 or args.heartbeats <= 0:
        parser.error("limit must be nonnegative and heartbeat budget positive")
    sources = discover_sources(ROOT)
    subprocess.run(["lake", "build", "--no-build", *LIBRARIES, CORE, *args.extra_import],
                   cwd=ROOT, check=True)
    validate_ileans(ROOT, sources)
    identities = {str(p.relative_to(ROOT)): digest(p) for p in sources.values()}
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", RUNNER,
                 "scripts/plain_certificate_inventory.py"):
        identities[name] = digest(ROOT / name)
    metadata = {
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                             text=True).strip(),
        "dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)),
        "sources_sha256": identities, "extra_imports": args.extra_import,
        "pairing": "exact PlainMirror registry lookup; no inferred name rewrite",
        "scope": "all elaborated declarations in the three libraries mentioning tidy notions",
        "limitations": [
            "Registered-rule probes test indexing/transport, not independent synthesis.",
            "A deliberately held-out isolated primitive need not be structurally synthesizable.",
            "Module import-all exposes private declarations; source-local attribute scopes are not replayed.",
            "Exact-bound and unsupported tidy predicates remain explicit rows, never weakened.",
            "Heartbeats measure search with fresh state; import/filter/transform costs are excluded.",
        ],
    }
    with tempfile.TemporaryDirectory(prefix="plain-certificate-inventory-") as td:
        module_file, raw_file = Path(td) / "modules.txt", Path(td) / "attempts.jsonl"
        module_file.write_text("\n".join(sorted(set(sources) | set(args.extra_import))) + "\n")
        subprocess.run(["lake", "env", "lean", "--run", RUNNER, str(module_file),
                        str(raw_file), str(args.heartbeats), str(args.limit)], cwd=ROOT, check=True)
        rows = [json.loads(line) for line in raw_file.read_text().splitlines() if line.strip()]
    summary = validate_rows(rows)
    if any(digest(ROOT / p) != sha for p, sha in identities.items()):
        raise RuntimeError("source snapshot changed during inventory")
    report = {"metadata": metadata, "summary": summary, "header": rows[0], "records": rows[1:]}
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(summary, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
