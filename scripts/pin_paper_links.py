#!/usr/bin/env python3
"""Verify and re-pin \\decl and \\declat links in paper/**/*.tex against Lean sources.

Usage:
    python3 scripts/pin_paper_links.py --check
    python3 scripts/pin_paper_links.py --pin <SHA> [--tex FILE ...] [--path-prefix PREFIX]
"""

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from proof_lengths import masks  # noqa: E402

MAIN_DECL_RE = re.compile(
    r"\\newcommand\{\\decl\}\[3\]\{\\declat\{([0-9a-f]{7,40})\}\{#1\}\{#2\}\{#3\}\}"
)
DECLAT_RE = re.compile(
    r"(\\declat\{)([0-9a-f]{7,40})(\}\{)([^}]+)(\}\{)(\d+)(\}\{)([^}]+)(\})"
)
DECL_RE = re.compile(r"(\\decl\{)([^}]+)(\}\{)(\d+)(\}\{)([^}]+)(\})")

MODIFIERS = r"(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*"
DECL_LINE_RE = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*"
    + MODIFIERS
    + r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|alias|opaque)\s+([^\s({:\[]+)"
)


def default_base_sha(root: pathlib.Path = ROOT) -> str:
    main_tex = root / "paper/main.tex"
    if main_tex.exists():
        m = MAIN_DECL_RE.search(main_tex.read_text(encoding="utf-8"))
        if m:
            return m.group(1)
    return "8d38f7753b6c651c3363a157c806d05794d6ea11"


def parse_declarations(text: str) -> dict[int, tuple[str, str]]:
    """Return {1-based line: (short_name, full_name)} for top-level declarations in Lean source."""
    code, _ = masks(text)
    scope: list[str] = []
    blocks: list[tuple[str, int]] = []
    decls: dict[int, tuple[str, str]] = {}
    for idx, line in enumerate(code.splitlines(), 1):
        s = line.strip()
        m_ns = re.match(r"^namespace\s+(\S+)", s)
        if m_ns:
            parts = m_ns.group(1).split(".")
            scope.extend(parts)
            blocks.append(("ns", len(parts)))
            continue
        m_sec = re.match(
            r"^(?:@\[[^\]\n]*\]\s*)*(?:(?:public|private|noncomputable)\s+)*section(?:\s+(\S+))?$",
            s,
        )
        if m_sec:
            sec_parts = m_sec.group(1).split(".") if m_sec.group(1) else []
            blocks.append(("sec", max(1, len(sec_parts))))
            continue
        m_end = re.match(r"^end(?:\s+(\S+))?$", s)
        if m_end:
            if m_end.group(1):
                remaining = len(m_end.group(1).split("."))
                while remaining > 0 and blocks:
                    kind, count = blocks.pop()
                    take = min(remaining, count)
                    if kind == "ns":
                        for _ in range(take):
                            if scope:
                                scope.pop()
                    if count > take:
                        blocks.append((kind, count - take))
                    remaining -= take
            elif blocks:
                kind, count = blocks.pop()
                if kind == "ns":
                    for _ in range(count):
                        if scope:
                            scope.pop()
            continue
        m_decl = DECL_LINE_RE.match(line)
        if m_decl:
            raw = m_decl.group(1)
            if raw.startswith("_root_."):
                clean_raw = raw.removeprefix("_root_.")
                full = clean_raw
            else:
                clean_raw = raw
                full = ".".join(scope + [raw]) if scope else raw
            decls[idx] = (clean_raw, full)
    return decls


def matches_decl(expected: str, raw: str, full: str) -> bool:
    clean = expected.replace(r"\_", "_")
    return full == clean or clean == raw or clean.endswith("." + raw)


def find_declaration_line(decls: dict[int, tuple[str, str]], expected: str) -> int:
    clean = expected.replace(r"\_", "_")
    exact = [line for line, (_, full) in decls.items() if full == clean]
    if len(exact) == 1:
        return exact[0]
    suffix = [line for line, (raw, full) in decls.items() if matches_decl(clean, raw, full)]
    if len(suffix) == 1:
        return suffix[0]
    if not suffix:
        raise ValueError(f"Declaration {clean!r} not found")
    raise ValueError(f"Declaration {clean!r} is ambiguous at lines {suffix}")


class SourceReader:
    def __init__(self, root: pathlib.Path = ROOT) -> None:
        self.root = root
        self._cache: dict[tuple[str | None, str], dict[int, tuple[str, str]]] = {}

    def get_decls(self, rev: str | None, rel_path: str) -> dict[int, tuple[str, str]]:
        key = (rev, rel_path)
        if key not in self._cache:
            if rev is None:
                file_path = self.root / rel_path
                if not file_path.exists():
                    raise ValueError(f"Missing working-tree file: {rel_path}")
                text = file_path.read_text(encoding="utf-8")
            else:
                proc = subprocess.run(
                    ["git", "-C", str(self.root), "show", f"{rev}:{rel_path}"],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                if proc.returncode != 0:
                    raise ValueError(f"Cannot read {rev}:{rel_path}: {proc.stderr.strip()}")
                text = proc.stdout
            self._cache[key] = parse_declarations(text)
        return self._cache[key]


def tex_files(root: pathlib.Path = ROOT, explicit: list[str] | None = None) -> list[pathlib.Path]:
    if explicit:
        return [pathlib.Path(p).resolve() for p in explicit]
    return [
        p
        for p in sorted((root / "paper").rglob("*.tex"))
        if p.name != "main.tex"
    ]


def check_links(
    root: pathlib.Path = ROOT,
    explicit_tex: list[str] | None = None,
    worktree_only: bool = False,
) -> tuple[int, list[str]]:
    reader = SourceReader(root)
    base_sha = default_base_sha(root)
    checked = 0
    errors: list[str] = []

    for tex in tex_files(root, explicit_tex):
        rel_tex = tex.relative_to(root) if tex.is_relative_to(root) else tex
        content = tex.read_text(encoding="utf-8")
        for m in DECLAT_RE.finditer(content):
            sha, path, line_str, decl = m.group(2), m.group(4), m.group(6), m.group(8)
            line = int(line_str)
            rev = None if worktree_only else sha
            checked += 1
            try:
                decls = reader.get_decls(rev, path)
            except ValueError as exc:
                errors.append(f"{rel_tex}: {exc}")
                continue
            if line not in decls:
                errors.append(
                    f"{rel_tex}: {path}:{line} ({decl} @{sha[:8]}) does not point to a declaration"
                )
                continue
            raw, full = decls[line]
            if not matches_decl(decl, raw, full):
                errors.append(
                    f"{rel_tex}: {path}:{line} expected {decl}, found {full}"
                )

        for m in DECL_RE.finditer(content):
            path, line_str, decl = m.group(2), m.group(4), m.group(6)
            line = int(line_str)
            rev = None if worktree_only else base_sha
            checked += 1
            try:
                decls = reader.get_decls(rev, path)
            except ValueError as exc:
                errors.append(f"{rel_tex}: {exc}")
                continue
            if line not in decls:
                errors.append(
                    f"{rel_tex}: {path}:{line} ({decl} @{base_sha[:8]}) does not point to a declaration"
                )
                continue
            raw, full = decls[line]
            if not matches_decl(decl, raw, full):
                errors.append(
                    f"{rel_tex}: {path}:{line} expected {decl}, found {full}"
                )

    return checked, errors


def pin_links(
    target_sha: str,
    root: pathlib.Path = ROOT,
    explicit_tex: list[str] | None = None,
    path_prefix: str | None = None,
    from_sha: str | None = None,
    use_worktree: bool = False,
) -> int:
    reader = SourceReader(root)
    base_sha = default_base_sha(root)
    rev = None if use_worktree else target_sha
    updated = 0

    for tex in tex_files(root, explicit_tex):
        content = tex.read_text(encoding="utf-8")

        def replace_declat(m: re.Match[str]) -> str:
            nonlocal updated
            old_sha, path, old_line, decl = m.group(2), m.group(4), m.group(6), m.group(8)
            if path_prefix and not path.startswith(path_prefix):
                return m.group(0)
            if from_sha and not old_sha.startswith(from_sha):
                return m.group(0)
            decls = reader.get_decls(rev, path)
            new_line = str(find_declaration_line(decls, decl))
            if old_sha != target_sha or old_line != new_line:
                updated += 1
            return f"{m.group(1)}{target_sha}{m.group(3)}{path}{m.group(5)}{new_line}{m.group(7)}{decl}{m.group(9)}"

        def replace_decl(m: re.Match[str]) -> str:
            nonlocal updated
            path, old_line, decl = m.group(2), m.group(4), m.group(6)
            if path_prefix and not path.startswith(path_prefix):
                return m.group(0)
            if from_sha and not base_sha.startswith(from_sha):
                return m.group(0)
            if not path_prefix and not from_sha:
                return m.group(0)
            decls = reader.get_decls(rev, path)
            new_line = str(find_declaration_line(decls, decl))
            if target_sha == base_sha:
                if old_line != new_line:
                    updated += 1
                return f"{m.group(1)}{path}{m.group(3)}{new_line}{m.group(5)}{decl}{m.group(7)}"
            updated += 1
            return f"\\declat{{{target_sha}}}{{{path}}}{{{new_line}}}{{{decl}}}"

        new_content = DECLAT_RE.sub(replace_declat, content)
        new_content = DECL_RE.sub(replace_decl, new_content)
        if new_content != content:
            tex.write_text(new_content, encoding="utf-8")

    return updated


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--check", action="store_true", help="Verify all \\decl and \\declat links")
    group.add_argument("--pin", metavar="SHA", help="Re-pin matching \\declat links to SHA")
    parser.add_argument("--tex", nargs="*", help="Restrict to specific .tex files")
    parser.add_argument(
        "--path-prefix",
        help="With --pin, only update links whose Lean path starts with this prefix",
    )
    parser.add_argument(
        "--from-sha",
        help="With --pin, only update links currently pinned to this SHA prefix",
    )
    parser.add_argument(
        "--worktree",
        action="store_true",
        help="Read Lean files from the working tree instead of git objects",
    )
    args = parser.parse_args()

    if args.check:
        checked, errors = check_links(ROOT, args.tex, worktree_only=args.worktree)
        if errors:
            for err in errors:
                print(f"ERROR: {err}", file=sys.stderr)
            return 1
        print(f"Verified {checked} declaration links across paper/.")
        return 0

    count = pin_links(
        args.pin,
        ROOT,
        explicit_tex=args.tex,
        path_prefix=args.path_prefix,
        from_sha=args.from_sha,
        use_worktree=args.worktree,
    )
    print(f"Updated {count} \\declat link(s) to {args.pin}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
