#!/usr/bin/env python3
"""Prepare a module of this library for a cslib pull request.

Usage:
    scripts/upstream.py Complexity.Foundations.Data.Encoding [more modules] \
        [--cslib ../cslib] [--no-mk-all] [--dry-run]

For each module the script
  * locates `Complexity/<Path>.lean` and the mirrored destination `<cslib>/Cslib/<Path>.lean`,
  * rewrites `import Complexity.` / `public import Complexity.` to the `Cslib.` prefix,
    mapping `Complexity.Init` to `Cslib.Init`, and likewise backticked module names
    (`` `Complexity.Foo.Bar` `` naming an existing module) in comments and docstrings,
  * drops the `-- upstream:` marker line,
  * refuses to continue if the module imports a local module whose marker is not
    `merged`/`submitted` (those must be upstreamed first, in the same stack),
  * refuses to overwrite an existing destination file or symlink in the cslib checkout
    (additions to existing upstream files must be integrated manually),
  * writes the file, runs `lake exe mk_all` in the cslib checkout (unless --no-mk-all), and
  * prints a suggested PR title from the module docstring.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
LIB = "Complexity"
UPSTREAM_LIB = "Cslib"

IMPORT_RE = re.compile(r"^(?P<prefix>\s*(?:public\s+)?import\s+(?:all\s+)?)Complexity(?P<rest>\.\S+|)\s*$")
MARKER_RE = re.compile(r"^--\s*upstream:\s*(?P<status>.*?)\s*$")
TITLE_RE = re.compile(r"^#\s+(?P<title>.+?)\s*$")
MODULE_REF_RE = re.compile(r"`Complexity(?P<rest>(?:\.[A-Z][A-Za-z0-9_']*)+)`")


def module_to_path(module: str, root: pathlib.Path = ROOT) -> pathlib.Path:
    parts = module.split(".")
    if parts[0] != LIB:
        sys.exit(f"error: module {module} does not start with {LIB}.")
    return root.joinpath(*parts).with_suffix(".lean")


def marker_of(path: pathlib.Path) -> str | None:
    for line in path.read_text(encoding="utf-8").splitlines():
        m = MARKER_RE.match(line)
        if m:
            return m.group("status")
    return None


def rewrite_module_ref(m: re.Match[str], root: pathlib.Path = ROOT) -> str:
    """Rewrite a backticked reference to an existing local module to its upstream name."""
    rest = m.group("rest")
    if root.joinpath(LIB, *rest[1:].split(".")).with_suffix(".lean").exists():
        return f"`{UPSTREAM_LIB}{rest}`"
    return m.group(0)


def rewrite(module: str, text: str, root: pathlib.Path = ROOT) -> tuple[str, list[str], str | None]:
    out: list[str] = []
    local_imports: list[str] = []
    title: str | None = None
    in_doc = False
    for line in text.splitlines():
        if MARKER_RE.match(line):
            continue
        m = IMPORT_RE.match(line)
        if m:
            rest = m.group("rest")
            local_imports.append(LIB + rest)
            out.append(f"{m.group('prefix')}{UPSTREAM_LIB}{rest}")
            continue
        if line.startswith("/-!"):
            in_doc = True
        if in_doc and title is None:
            t = TITLE_RE.match(line)
            if t:
                title = t.group("title")
        if in_doc and line.rstrip().endswith("-/"):
            in_doc = False
        out.append(MODULE_REF_RE.sub(lambda match: rewrite_module_ref(match, root=root), line))
    return "\n".join(out) + "\n", local_imports, title


def suggest_title(module: str, title: str | None) -> str:
    parts = module.split(".")[1:]
    scope = parts[-2] if len(parts) >= 2 else parts[-1]
    desc = (title or parts[-1]).rstrip(".")
    if len(desc) > 1 and desc[1].islower():
        desc = desc[0].lower() + desc[1:]
    return f"feat({scope}): {desc}"


def destination_exists(dest: pathlib.Path) -> bool:
    """Return True if dest already exists on disk, including broken symlinks."""
    return dest.exists() or dest.is_symlink()


def main(argv: list[str] | None = None, root: pathlib.Path = ROOT) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("modules", nargs="+")
    ap.add_argument("--cslib", default=str(root.parent / "cslib"), help="path to a cslib checkout")
    ap.add_argument("--no-mk-all", action="store_true")
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args(argv)

    cslib = pathlib.Path(args.cslib).resolve()
    if not (cslib / "lakefile.toml").exists():
        sys.exit(f"error: {cslib} is not a cslib checkout")

    requested = set(args.modules)
    planned: list[tuple[str, pathlib.Path, str | None, str, bool]] = []
    collisions: list[tuple[str, pathlib.Path]] = []

    for module in args.modules:
        src = module_to_path(module, root=root)
        if not src.exists():
            sys.exit(f"error: {src} does not exist")
        text = src.read_text(encoding="utf-8")
        new_text, local_imports, title = rewrite(module, text, root=root)

        for dep in local_imports:
            if dep == f"{LIB}.Init" or dep in requested:
                continue
            dep_path = module_to_path(dep, root=root)
            status = marker_of(dep_path) if dep_path.exists() else None
            if status is None or not (status.startswith("merged") or status.startswith("submitted")):
                sys.exit(
                    f"error: {module} imports {dep} whose upstream status is {status!r}; "
                    "upstream it first or include it in this invocation."
                )

        dest = cslib / UPSTREAM_LIB / src.relative_to(root / LIB)
        collides = destination_exists(dest)
        if collides:
            collisions.append((module, dest))
        planned.append((module, dest, title, new_text, collides))

    for module, dest, title, _, collides in planned:
        print(f"{module}\n  -> {dest}")
        print(f"  suggested PR title: {suggest_title(module, title)}")
        if collides:
            print(f"  existing destination: {dest} already exists; integrate additions manually")

    if collisions:
        details = ", ".join(f"{module} -> {dest}" for module, dest in collisions)
        sys.exit(
            f"error: refusing to overwrite existing upstream destination(s) ({details}); "
            "integrate additions to existing upstream files manually."
        )

    if not args.dry_run:
        for _, dest, _, new_text, _ in planned:
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_text(new_text, encoding="utf-8")

    if not args.dry_run and not args.no_mk_all:
        subprocess.run(["lake", "exe", "mk_all"], cwd=cslib, check=True)
        print("ran `lake exe mk_all` in", cslib)
    print("next: run cslib's gates there (build --wfail --iofail, mk_all --check, test, lint, lint-style)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
