#!/usr/bin/env python3
"""Build the theorem-index PDF and record the source revision used for review."""

import hashlib
import json
import os
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]


def git(*args):
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def main():
    output = ROOT / "paper/build"
    output.mkdir(parents=True, exist_ok=True)
    subprocess.run(
        ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
         "-no-shell-escape", "-bibtexfudge-", "-outdir=build", "main.tex"],
        cwd=ROOT / "paper", check=True,
    )

    event_path = os.environ.get("GITHUB_EVENT_PATH")
    event = json.loads(Path(event_path).read_text()) if event_path else {}
    pull_request = event.get("pull_request", {})
    repository = os.environ.get("GITHUB_REPOSITORY")
    run_id = os.environ.get("GITHUB_RUN_ID")
    server = os.environ.get("GITHUB_SERVER_URL", "https://github.com")
    provenance = {
        "source_sha": git("rev-parse", "HEAD"),
        "source_dirty": bool(git("status", "--porcelain")),
        "repository": repository,
        "event": os.environ.get("GITHUB_EVENT_NAME", "local"),
        "ref": os.environ.get("GITHUB_REF"),
        "pull_request_number": pull_request.get("number"),
        "pull_request_head_sha": pull_request.get("head", {}).get("sha"),
        "pull_request_base_sha": pull_request.get("base", {}).get("sha"),
        "run_url": f"{server}/{repository}/actions/runs/{run_id}" if run_id else None,
        "run_attempt": os.environ.get("GITHUB_RUN_ATTEMPT"),
        "pdf_sha256": hashlib.sha256((output / "main.pdf").read_bytes()).hexdigest(),
    }
    (output / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    print(f"Built {output / 'main.pdf'} from {provenance['source_sha']}")


if __name__ == "__main__":
    main()
