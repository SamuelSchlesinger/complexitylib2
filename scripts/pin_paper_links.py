#!/usr/bin/env python3
"""Verify and re-pin \\decl and \\declat links in paper/**/*.tex against Lean sources.

Usage:
    python3 scripts/pin_paper_links.py --check
    python3 scripts/pin_paper_links.py --pin <SHA> [--tex FILE ...] [--path-prefix PREFIX]

A link matches only when its declaration name equals the full name (namespace included) of the
declaration that starts on the linked line. Every .tex file under paper/, including main.tex, is
scanned; only the `\\newcommand` lines that define the `\\decl` and `\\declat` macros are skipped.
`--pin` requires a full 40-character commit SHA that is an ancestor of HEAD.
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
FULL_SHA_RE = re.compile(r"[0-9a-f]{40}")
PIN_HINT = (
    "hint: the declaration may have been moved or renamed at the target revision; update the "
    "Lean path and full declaration name of this link in the .tex file, then re-run --pin."
)


class PinError(ValueError):
    """A link that cannot be re-pinned, with the .tex file and Lean path in the message."""


ATTR_PREFIX = r"(?:@\[(?:[^\[\]\n]|\[[^\[\]\n]*\])*\]\s*)*"
MODIFIERS = r"(?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|scoped|local)\s+)*"
DECL_LINE_RE = re.compile(
    r"^\s*"
    + ATTR_PREFIX
    + MODIFIERS
    + r"(?:theorem|lemma|def|irreducible_def|abbrev|structure|inductive|class|instance|alias|opaque|axiom|example)\s+([^\s({:\[]+)"
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
    for idx, line in enumerate(code.split("\n"), 1):
        s = line.strip()
        m_ns = re.match(r"^namespace\s+(\S+)", s)
        if m_ns:
            parts = m_ns.group(1).split(".")
            scope.extend(parts)
            blocks.append(("ns", len(parts)))
            continue
        m_sec = re.match(
            r"^" + ATTR_PREFIX + r"(?:(?:public|private|noncomputable)\s+)*section(?:\s+(\S+))?$",
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


def matches_decl(expected: str, full: str) -> bool:
    """Whether the link name `expected` (LaTeX-escaped) is exactly the full declaration name."""
    return full == expected.replace(r"\_", "_")


def find_declaration_line(decls: dict[int, tuple[str, str]], expected: str) -> int:
    clean = expected.replace(r"\_", "_")
    exact = [line for line, (_, full) in decls.items() if full == clean]
    if len(exact) == 1:
        return exact[0]
    if exact:
        raise ValueError(f"Declaration {clean!r} is ambiguous at lines {exact}")
    short = clean.rsplit(".", 1)[-1]
    similar = [
        f"{full} (line {line})"
        for line, (raw, full) in decls.items()
        if raw == short or raw.endswith("." + short)
    ]
    if similar:
        raise ValueError(
            f"Declaration {clean!r} not found; declarations with the same short name: "
            + ", ".join(similar)
        )
    raise ValueError(f"Declaration {clean!r} not found")


def in_macro_definition(content: str, pos: int) -> bool:
    """Whether `pos` lies on the line defining the `\\decl` or `\\declat` macro."""
    line_start = content.rfind("\n", 0, pos) + 1
    return content.startswith(("\\newcommand{\\decl}", "\\newcommand{\\declat}"), line_start)


def validate_pin_sha(sha: str, root: pathlib.Path = ROOT) -> None:
    """Require `sha` to be a full 40-character commit SHA that is an ancestor of HEAD."""
    if not FULL_SHA_RE.fullmatch(sha):
        raise ValueError(
            f"--pin needs a full 40-character lowercase commit SHA, got {sha!r}; "
            "use `git rev-parse <rev>`"
        )
    exists = subprocess.run(
        ["git", "-C", str(root), "cat-file", "-e", f"{sha}^{{commit}}"],
        capture_output=True,
        check=False,
    )
    if exists.returncode != 0:
        raise ValueError(f"--pin SHA {sha} is not a commit in this repository")
    ancestor = subprocess.run(
        ["git", "-C", str(root), "merge-base", "--is-ancestor", sha, "HEAD"],
        capture_output=True,
        check=False,
    )
    if ancestor.returncode != 0:
        raise ValueError(
            f"--pin SHA {sha} is not an ancestor of HEAD; pin to a commit on the current branch"
        )


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
    return sorted((root / "paper").rglob("*.tex"))


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
            if in_macro_definition(content, m.start()):
                continue
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
            _, full = decls[line]
            if not matches_decl(decl, full):
                errors.append(
                    f"{rel_tex}: {path}:{line} expected {decl}, found {full}"
                )

        for m in DECL_RE.finditer(content):
            if in_macro_definition(content, m.start()):
                continue
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
            _, full = decls[line]
            if not matches_decl(decl, full):
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
    pending_writes: list[tuple[pathlib.Path, str]] = []

    for tex in tex_files(root, explicit_tex):
        rel_tex = tex.relative_to(root) if tex.is_relative_to(root) else tex
        content = tex.read_text(encoding="utf-8")

        def locate(path: str, decl: str) -> str:
            try:
                return str(find_declaration_line(reader.get_decls(rev, path), decl))
            except ValueError as exc:
                at = "working tree" if rev is None else rev
                raise PinError(f"{rel_tex}: {path} (@{at}): {exc}") from exc

        def replace_declat(m: re.Match[str]) -> str:
            nonlocal updated
            old_sha, path, old_line, decl = m.group(2), m.group(4), m.group(6), m.group(8)
            if path_prefix and not path.startswith(path_prefix):
                return m.group(0)
            if from_sha and not old_sha.startswith(from_sha):
                return m.group(0)
            if in_macro_definition(m.string, m.start()):
                return m.group(0)
            new_line = locate(path, decl)
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
            if in_macro_definition(m.string, m.start()):
                return m.group(0)
            new_line = locate(path, decl)
            if target_sha == base_sha:
                if old_line != new_line:
                    updated += 1
                return f"{m.group(1)}{path}{m.group(3)}{new_line}{m.group(5)}{decl}{m.group(7)}"
            updated += 1
            return f"\\declat{{{target_sha}}}{{{path}}}{{{new_line}}}{{{decl}}}"

        new_content = DECLAT_RE.sub(replace_declat, content)
        new_content = DECL_RE.sub(replace_decl, new_content)
        if new_content != content:
            pending_writes.append((tex, new_content))

    for tex, new_content in pending_writes:
        tex.write_text(new_content, encoding="utf-8")

    return updated


def main(argv: list[str] | None = None, root: pathlib.Path = ROOT) -> int:
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
    args = parser.parse_args(argv)

    if args.check:
        checked, errors = check_links(root, args.tex, worktree_only=args.worktree)
        if errors:
            for err in errors:
                print(f"ERROR: {err}", file=sys.stderr)
            return 1
        print(f"Verified {checked} declaration links across paper/.")
        return 0

    try:
        validate_pin_sha(args.pin, root)
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 1
    try:
        count = pin_links(
            args.pin,
            root,
            explicit_tex=args.tex,
            path_prefix=args.path_prefix,
            from_sha=args.from_sha,
            use_worktree=args.worktree,
        )
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        print(PIN_HINT, file=sys.stderr)
        print("No .tex file was modified.", file=sys.stderr)
        return 1
    print(f"Updated {count} declaration link(s) to {args.pin}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
