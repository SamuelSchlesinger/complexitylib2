#!/usr/bin/env python3
"""Resolve git conflict markers in references.bib-style files by keeping both sides (ours, then
theirs). Git often factors a shared closing `}` out of the conflict; if the `ours` side then
lacks its closing brace, one is inserted before `theirs`."""
import sys
for path in sys.argv[1:]:
    out, ours, theirs, state = [], [], [], None
    for line in open(path, encoding="utf-8"):
        if line.startswith("<<<<<<< "):
            state, ours, theirs = "ours", [], []; continue
        if line.startswith("||||||| ") and state:
            state = "base"; continue
        if line.startswith("=======") and state:
            state = "theirs"; continue
        if line.startswith(">>>>>>> ") and state:
            last = [l for l in ours if l.strip()]
            if last and not last[-1].startswith("}"):
                ours.append("}\n\n")
            out += ours + theirs
            state = None; continue
        if state == "ours": ours.append(line)
        elif state == "theirs": theirs.append(line)
        elif state is None: out.append(line)
    s = "".join(out)
    assert s.count("{") == s.count("}"), f"unbalanced braces in {path}"
    open(path, "w", encoding="utf-8").write(s)
