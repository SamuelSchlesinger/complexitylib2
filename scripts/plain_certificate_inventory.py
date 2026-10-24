#!/usr/bin/env python3
"""Check every elaborated tidy certificate against the same-budget plain fun_prop search.

Finds compatible ordinary declarations by elaborated type and kernel-checked application, never
a guessed counterpart name. Run after building all three libraries and requested plain modules. Unsupported notions remain output rows;
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
        if src.is_symlink() or base.is_symlink() or any(p.is_symlink() for p in base.rglob("*")):
            raise ValueError(f"symlinked source tree is not a complete inventory: {base}")
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


def annotate_sources(root: Path, sources: dict[str, Path], rows: list[dict]) -> None:
    """Distinguish source-written certificates from generated helpers without dropping either."""
    definitions = {}
    for module, path in sources.items():
        artifact = root / ".lake/build/lib/lean" / Path(*module.split("."))
        data = json.loads(artifact.with_suffix(".ilean").read_text())
        for key, info in data["references"].items():
            constant = json.loads(key).get("c")
            if constant and constant["m"] == module and info.get("definition"):
                definitions[constant["n"]] = (str(path.relative_to(root)), info["definition"])
    for row in rows[1:]:
        decl = row["declaration"]
        definition = definitions.get(decl.get("owner", decl["name"]))
        decl["source_written"] = definition is not None and not decl.get("local_path")
        decl["scope"] = "local_certificate" if decl.get("local_path") else (
            "source_declaration" if definition else "generated_helper")
        if definition:
            decl["source_path"], decl["source_definition"] = definition
        decl["elaborated_type_sha256"] = hashlib.sha256(decl["type"].encode()).hexdigest()


def validate_rows(rows: list[dict]) -> dict:
    """Fail closed on truncated/duplicate/unaccounted-for inventory output."""
    if not rows or "inventory_total" not in rows[0]:
        raise ValueError("missing inventory header")
    header, records = rows[0], rows[1:]
    selected = header.get("selected_total", header["inventory_total"])
    expected = min(selected, header["limit"] or selected)
    if len(records) != expected:
        raise ValueError(f"truncated inventory: expected {expected}, got {len(records)}")
    names = [row["declaration"]["name"] for row in records]
    if len(set(names)) != len(names):
        raise ValueError("duplicate certificate rows")
    statuses = Counter()
    pairs = Counter()
    registration_pairs = Counter()
    for row in records:
        status = row["status"]
        if status not in {"compared", "unsupported_tidy", "transform_error", "non_proposition"}:
            raise ValueError(f"unknown status {status}")
        statuses[status] += 1
        if "plain_registration" in row and "tidy_registration" in row:
            registration_pairs[(row["tidy_registration"]["status"],
                                row["plain_registration"]["status"])] += 1
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
        "selected_total": selected, "selection_complete": len(records) == selected,
        "statuses": dict(statuses),
        "registration_boundary": header.get("registration_boundary", {"status": "unknown"}),
        "holdout_pairs": {f"tidy:{a}/plain:{b}": n for (a, b), n in sorted(pairs.items())},
        "registration_probes": sum("plain_registration" in row for row in records),
        "registration_pairs": {f"tidy:{a}/plain:{b}": n
                               for (a, b), n in sorted(registration_pairs.items())},
        "tidy_only_holdout_success": sum(n for (a, b), n in pairs.items()
                                  if a == "success" and b != "success"),
        "tidy_only_registration_success": sum(n for (a, b), n in registration_pairs.items()
                                               if a == "success" and b != "success"),
        "plain_only_holdout_success": sum(n for (a, b), n in pairs.items()
                                           if b == "success" and a != "success"),
        "plain_only_registration_success": sum(n for (a, b), n in registration_pairs.items()
                                                if b == "success" and a != "success"),
        "holdout_pairs_by_role": {
            role: dict(Counter(
                f"tidy:{r['tidy_holdout']['status']}/plain:{r['plain_holdout']['status']}"
                for r in records if r["status"] == "compared" and
                ("ordinary_plain_rule" if r["declaration"].get("counterparts") else "without_counterpart") == role))
            for role in ("ordinary_plain_rule", "without_counterpart")},
    }


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--extra-import", action="append", default=[],
                        help="ordinary plain-rule module; built outputs must already be current")
    parser.add_argument("--only-names", type=Path,
                        help="JSON list of exact original identities for a disclosed delta check")
    parser.add_argument("--heartbeats", type=int, default=200000)
    parser.add_argument("--limit", type=int, default=0, help="debug subset; 0 inventories all")
    args = parser.parse_args()
    if args.limit < 0 or args.heartbeats <= 0:
        parser.error("limit must be nonnegative and heartbeat budget positive")
    selection = None
    if args.only_names:
        selection = json.loads(args.only_names.read_text())
        if (not isinstance(selection, list) or not selection or
                not all(isinstance(n, str) for n in selection) or len(set(selection)) != len(selection)):
            parser.error("--only-names must hold a nonempty JSON list of distinct identity strings")
    sources = discover_sources(ROOT)
    subprocess.run(["lake", "build", "--no-build", *LIBRARIES, *args.extra_import],
                   cwd=ROOT, check=True)
    validate_ileans(ROOT, sources)
    identities = {str(p.relative_to(ROOT)): digest(p) for p in sources.values()}
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml", RUNNER,
                 "scripts/plain_certificate_inventory.py"):
        identities[name] = digest(ROOT / name)
    if args.only_names:
        identities[str(args.only_names.resolve())] = digest(args.only_names)
    metadata = {
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                             text=True).strip(),
        "dirty": bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT)),
        "sources_sha256": identities, "extra_imports": args.extra_import,
        "selection": selection,
        "pairing": "ordinary elaborated statements and kernel-checked compatibility; no inferred name rewrite",
        "scope": "all elaborated declarations and captured local certificates in the three libraries",
        "local_inventory_unit": "unique stored expression per owner/binder/source context; repeated DAG use is not a new certificate",
        "limitations": [
            "Inventory/selection completion records coverage, never a claim of automation parity.",
            "Registered-rule probes test indexing/transport, not independent synthesis.",
            "A deliberately held-out isolated primitive need not be structurally synthesizable.",
            "Module import-all exposes private declarations; source-local attribute scopes are not replayed.",
            "Exact-bound and unsupported tidy predicates remain explicit rows, never weakened.",
            "Heartbeats measure search with fresh state; import/filter/transform costs are excluded.",
        ],
    }
    raw_file = args.output.with_suffix(".attempts.jsonl")
    args.output.with_suffix(".metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    raw_file.write_text("")  # Never relabel a previous run's rows after an early failure.
    args.output.write_text(json.dumps({"metadata": metadata,
        "summary": {"inventory_complete": False, "records": 0, "phase": "running"},
        "errors": [], "header": {}, "records": []}, indent=2) + "\n")
    with tempfile.TemporaryDirectory(prefix="plain-certificate-inventory-") as td:
        module_file = Path(td) / "modules.txt"
        module_file.write_text("\n".join(sorted(set(sources) | set(args.extra_import))) + "\n")
        command = ["lake", "env", "lean", "--run", RUNNER, str(module_file),
                   str(raw_file.resolve()), str(args.heartbeats), str(args.limit)]
        if args.only_names:
            command.append(str(args.only_names.resolve()))
        process = subprocess.run(command, cwd=ROOT, check=False)
    rows, errors = [], []
    for number, line in enumerate(raw_file.read_text().splitlines() if raw_file.exists() else [], 1):
        try:
            rows.append(json.loads(line))
        except json.JSONDecodeError:
            errors.append(f"invalid/truncated raw row {number}")
    if process.returncode:
        errors.append(f"Lean runner exited {process.returncode}")
    try:
        summary = validate_rows(rows)
    except (ValueError, KeyError) as error:
        errors.append(str(error))
        summary = {"inventory_complete": False, "records": max(0, len(rows) - 1)}
    if any(digest(ROOT / p) != sha for p, sha in identities.items()):
        errors.append("source snapshot changed during inventory")
    annotate_sources(ROOT, sources, rows)
    if errors:
        summary["inventory_complete"] = False
    report = {"metadata": metadata, "summary": summary, "errors": errors,
              "header": rows[0] if rows else {}, "records": rows[1:]}
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(summary, sort_keys=True))
    if errors:
        raise RuntimeError("; ".join(errors))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
