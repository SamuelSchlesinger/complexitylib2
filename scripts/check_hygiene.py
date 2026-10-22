#!/usr/bin/env python3
"""Static proof-hygiene and module-template checks for Complexitylib Lean files.

Checks enforced (see AGENTS.md):
1. Every module under Complexity/ has a valid `-- upstream:` marker.
2. No `sorry`, custom `axiom`, or `native_decide` in Complexity/ or ComplexityTests/.
3. Every `set_option maxHeartbeats` or `set_option maxRecDepth` has an explanatory comment
   on the same line or within the preceding 3 lines.
4. No non-terminal bare `simp` in `-- upstream: candidate` modules under Complexity/.
"""

from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from proof_lengths import COMMAND, masks  # noqa: E402

UPSTREAM_MARKER_RE = re.compile(
    r"^--\s*upstream:\s*(?:"
    r"candidate(?:\s+.*)?|"
    r"submitted\s+#\d+(?:\s+@[0-9a-f]{7,40})?(?:\s+.*)?|"
    r"(?:vendored|subset of)\s+\S+(?:\s+@[0-9a-f]{7,40})?(?:\s+.*)?|"
    r"merged\s+@[0-9a-f]{7,40}(?:\s+.*)?|"
    r"local-only\s+\([^)]+\)"
    r")\s*$",
    re.M,
)

FORBIDDEN_TOKEN_RE = re.compile(r"\b(sorry|native_decide)\b")
CUSTOM_AXIOM_RE = re.compile(
    r"^\s*(?:@\[[^\]\n]*\]\s*)*(?:(?:public|private|protected|noncomputable|scoped|local)\s+)*axiom\b",
    re.M,
)
SET_OPTION_RE = re.compile(r"^\s*set_option\s+(maxHeartbeats|maxRecDepth)\b")
BARE_SIMP_RE = re.compile(
    r"(?<![.\w])simp(?:\?)?(?!\s+only\b|\s*\[[^\]]*\]\s*at\b)(?=\s*$|\s+\[|\s+at\b)"
)


def is_candidate_module(text: str) -> bool:
    return bool(re.search(r"^--\s*upstream:\s*candidate\b", text, re.M))


def has_nearby_comment(raw_lines: list[str], code_lines: list[str], idx_0based: int) -> bool:
    start = max(0, idx_0based - 3)
    for j in range(start, idx_0based + 1):
        # If masking comments changed the line, a comment is present on line j.
        if raw_lines[j] != code_lines[j]:
            return True
    return False


def find_nonterminal_bare_simps(code: str) -> list[int]:
    """Return 1-based line numbers of non-terminal bare `simp` tactics in masked code."""
    lines = code.splitlines()
    violations: list[int] = []
    for i, line in enumerate(lines):
        stripped = line.strip()
        if not stripped:
            continue
        # Only inspect lines that start with a bare `simp` (or `· simp`).
        bullet_stripped = re.sub(r"^[·•*-]\s*", "", stripped)
        if not re.match(r"^simp(?!\s+only\b|_all\b|_arith\b|_rw\b|a\b|\w)", bullet_stripped):
            continue
        if "<;>" in bullet_stripped or ";" in bullet_stripped:
            continue
        indent = len(line) - len(line.lstrip(" "))
        has_bullet = stripped.startswith(("·", "•"))
        # Scan subsequent non-empty lines to see if another tactic follows in the same block.
        j = i + 1
        while j < len(lines) and not lines[j].strip():
            j += 1
        if j >= len(lines):
            continue
        next_line = lines[j]
        next_stripped = next_line.strip()
        if COMMAND.match(next_line):
            continue
        if re.match(r"^\|(\s|$)", next_stripped) or re.match(r"^case\s+", next_stripped):
            continue
        next_indent = len(next_line) - len(next_line.lstrip(" "))
        next_has_bullet = next_stripped.startswith(("·", "•"))
        if has_bullet:
            # Inside a `· simp` line, a following tactic at indent > bullet indent is non-terminal.
            if next_indent > indent and not next_has_bullet:
                violations.append(i + 1)
        else:
            if next_indent == indent and not next_has_bullet:
                violations.append(i + 1)
    return violations


def check_file(
    path: pathlib.Path,
    root: pathlib.Path = ROOT,
    check_simp: bool = False,
    max_lines: int | None = None,
) -> list[str]:
    rel = path.relative_to(root) if path.is_relative_to(root) else path
    raw = path.read_text(encoding="utf-8")
    code, syntax = masks(raw)
    raw_lines = raw.splitlines()
    code_lines = code.splitlines()
    errors: list[str] = []

    in_complexity = rel.parts and rel.parts[0] == "Complexity"
    if in_complexity and not UPSTREAM_MARKER_RE.search(raw):
        errors.append(f"{rel}: missing or invalid `-- upstream:` marker")

    for idx, s_line in enumerate(syntax.splitlines(), 1):
        for m in FORBIDDEN_TOKEN_RE.finditer(s_line):
            errors.append(f"{rel}:{idx}: forbidden `{m.group(1)}`")

    for m in CUSTOM_AXIOM_RE.finditer(syntax):
        line_no = syntax.count("\n", 0, m.start()) + 1
        errors.append(f"{rel}:{line_no}: forbidden custom `axiom` declaration")

    for idx, c_line in enumerate(code_lines):
        m_opt = SET_OPTION_RE.match(c_line)
        if m_opt and not has_nearby_comment(raw_lines, code_lines, idx):
            errors.append(
                f"{rel}:{idx + 1}: `set_option {m_opt.group(1)}` requires a justifying comment"
            )

    if check_simp and in_complexity and is_candidate_module(raw):
        for line_no in find_nonterminal_bare_simps(syntax):
            errors.append(f"{rel}:{line_no}: non-terminal bare `simp` (use `simp only`)")

    if max_lines is not None and len(raw_lines) > max_lines:
        errors.append(f"{rel}: file has {len(raw_lines)} lines (exceeds limit of {max_lines})")

    return errors


def check_paths(
    paths: list[pathlib.Path],
    root: pathlib.Path = ROOT,
    check_simp: bool = False,
    max_lines: int | None = None,
) -> list[str]:
    errors: list[str] = []
    for p in paths:
        if p.is_dir():
            files = sorted(p.rglob("*.lean"))
        else:
            files = [p]
        for f in files:
            errors.extend(check_file(f, root=root, check_simp=check_simp, max_lines=max_lines))
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "paths",
        nargs="*",
        help="Files or directories to check (defaults to Complexity/ and ComplexityTests/)",
    )
    parser.add_argument(
        "--check-simp",
        action="store_true",
        help="Also flag non-terminal bare `simp` calls in candidate modules",
    )
    parser.add_argument(
        "--max-lines",
        type=int,
        default=None,
        help="Optional maximum line count per Lean file",
    )
    args = parser.parse_args()

    if args.paths:
        targets = [pathlib.Path(p).resolve() for p in args.paths]
    else:
        targets = [ROOT / "Complexity", ROOT / "ComplexityTests"]

    errors = check_paths(
        targets,
        root=ROOT,
        check_simp=args.check_simp,
        max_lines=args.max_lines,
    )
    if errors:
        for err in errors:
            print(f"ERROR: {err}", file=sys.stderr)
        return 1
    print("All hygiene checks passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
