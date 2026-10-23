#!/usr/bin/env python3
"""Require authoritative exact-source Lean CI before a formal-abstract release write.

Use the workflow-file endpoint, not a check name or a success-filtered run list. The
largest workflow run_number selects the latest run; its current run_attempt must
have completed successfully. A previous green attempt never overrides a rerun.
Only push/main validation from this repository counts, including on manual retries
of the *publication* job. This script performs GET requests only.

Source: the two codebase reviews recorded in issue #432, and GitHub's REST API:
https://docs.github.com/en/rest/actions/workflow-runs
https://docs.github.com/en/actions/reference/workflows-and-actions/variables
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from urllib.parse import urlencode


WORKFLOW_FILE = "lean_action_ci.yml"
WORKFLOW_PATH = f".github/workflows/{WORKFLOW_FILE}"
WORKFLOW_NAME = "Lean Action CI"


class Rejected(RuntimeError):
    """The available evidence does not authorize publication."""


class Pending(Rejected):
    """Evidence is missing or a current attempt is still running."""


def gh_get(endpoint: str, *, paginate: bool = False):
    command = [
        "gh", "api", "--hostname", "github.com", "--method", "GET",
        "-H", "Accept: application/vnd.github+json",
        "-H", "X-GitHub-Api-Version: 2022-11-28", endpoint,
    ]
    if paginate:
        command += ["--paginate", "--slurp"]
    result = subprocess.run(command, check=True, capture_output=True, text=True, timeout=60)
    return json.loads(result.stdout)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise Rejected(message)


def positive(value) -> bool:
    return type(value) is int and value > 0


def check_identity(run: dict, repository: str, sha: str, workflow_id: int) -> None:
    require(run.get("head_sha") == sha, "Lean run source SHA mismatch")
    require(run.get("event") == "push" and run.get("head_branch") == "main",
            "Lean run is not a push to main")
    require(run.get("workflow_id") == workflow_id, "Wrong Lean workflow ID")
    require(run.get("path", "").split("@", 1)[0] == WORKFLOW_PATH, "Wrong Lean workflow path")
    repo, head = run.get("repository", {}), run.get("head_repository", {})
    require(repo.get("full_name") == repository and head.get("full_name") == repository,
            "Lean run repository mismatch")
    require(positive(repo.get("id")) and repo.get("id") == head.get("id"),
            "Lean run head is from another repository")
    require(all(positive(run.get(field)) for field in ("id", "run_number", "run_attempt")),
            "Malformed Lean run identity")


def latest_run(api, repository: str, sha: str, workflow_id: int) -> dict:
    query = urlencode({"head_sha": sha, "event": "push", "branch": "main", "per_page": 100})
    pages = api(f"repos/{repository}/actions/workflows/{workflow_id}/runs?{query}", paginate=True)
    require(isinstance(pages, list) and bool(pages), "Malformed workflow-run pages")
    runs = []
    for page in pages:
        require(isinstance(page.get("workflow_runs"), list), "Malformed workflow-run list")
        runs.extend(page["workflow_runs"])
    require(all(page.get("total_count") == len(runs) for page in pages),
            "Incomplete or changing workflow-run listing")
    if not runs:
        raise Pending("No exact-source Lean push/main run exists")
    for run in runs:
        check_identity(run, repository, sha, workflow_id)
    require(len({run["id"] for run in runs}) == len(runs), "Duplicate workflow runs")
    require(len({run["run_number"] for run in runs}) == len(runs), "Ambiguous latest workflow run")
    return max(runs, key=lambda run: run["run_number"])


def check_once(repository: str, sha: str, *, api=gh_get) -> dict:
    require(bool(re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repository)),
            "Invalid repository")
    require(bool(re.fullmatch(r"[0-9a-f]{40}", sha)), "Invalid source SHA")
    main = api(f"repos/{repository}/git/ref/heads/main")
    require(main.get("ref") == "refs/heads/main" and main.get("object", {}).get("sha") == sha,
            "Artifact source is no longer current main")
    workflow = api(f"repos/{repository}/actions/workflows/{WORKFLOW_FILE}")
    require(workflow.get("path") == WORKFLOW_PATH and workflow.get("name") == WORKFLOW_NAME
            and workflow.get("state") == "active" and positive(workflow.get("id")),
            "Authoritative Lean workflow is missing, disabled or changed")
    workflow_id = workflow["id"]
    selected = latest_run(api, repository, sha, workflow_id)
    # A run-list response can lag the latest rerun. GET the run, not a historical
    # /attempts/{number} endpoint, before accepting its current conclusion.
    current = api(f"repos/{repository}/actions/runs/{selected['id']}")
    check_identity(current, repository, sha, workflow_id)
    require(current["id"] == selected["id"] and current["run_number"] == selected["run_number"]
            and current["run_attempt"] >= selected["run_attempt"], "Lean run changed identity")
    if current.get("status") != "completed":
        raise Pending(f"Lean run {current['id']} attempt {current['run_attempt']} is not complete")
    require(current.get("conclusion") == "success",
            f"Lean run {current['id']} attempt {current['run_attempt']} did not succeed")
    # Do not accept an older success if another run/rerun appeared during the read.
    latest = latest_run(api, repository, sha, workflow_id)
    require((latest["id"], latest["run_attempt"], latest.get("status"), latest.get("conclusion"))
            == (current["id"], current["run_attempt"], "completed", "success"),
            "Lean validation changed while checking; retry publication")
    main = api(f"repos/{repository}/git/ref/heads/main")
    require(main.get("object", {}).get("sha") == sha, "Main changed while checking Lean CI")
    return current


def wait_for_success(repository: str, sha: str, wait_seconds: float, *, api=gh_get,
                     clock=time.monotonic, sleep=time.sleep) -> dict:
    deadline = clock() + wait_seconds
    while True:
        try:
            return check_once(repository, sha, api=api)
        except Pending as error:
            remaining = deadline - clock()
            if remaining <= 0:
                raise
            print(f"{error}; waiting for exact-source validation", flush=True)
            sleep(min(30, remaining))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY", ""))
    parser.add_argument("--sha", default=os.environ.get("GITHUB_SHA", ""))
    parser.add_argument("--wait-seconds", type=float, default=0)
    args = parser.parse_args()
    try:
        require(0 <= args.wait_seconds <= 1200, "Wait must be between zero and 1200 seconds")
        run = wait_for_success(args.repository, args.sha, args.wait_seconds)
    except (Rejected, subprocess.SubprocessError, OSError, ValueError, KeyError, TypeError,
            AttributeError) as error:
        print(f"Abstract publication denied: {error}", file=sys.stderr)
        return 1
    print(f"Lean validation: https://github.com/{args.repository}/actions/runs/{run['id']} "
          f"attempt {run['run_attempt']} succeeded for {args.sha}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
