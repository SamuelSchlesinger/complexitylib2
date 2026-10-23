"""Exact-source CI policy and release-command boundary regressions (issue #432)."""

import contextlib
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import textwrap
import unittest
from unittest.mock import patch

import check_abstract_ci as gate


REPOSITORY = "cslib-community/complexitylib"
SHA = "a" * 40
ROOT = Path(__file__).resolve().parents[1]


def run(**changes):
    result = {
        "id": 101, "run_number": 20, "run_attempt": 1, "workflow_id": 7,
        "path": gate.WORKFLOW_PATH, "head_sha": SHA, "event": "push", "head_branch": "main",
        "status": "completed", "conclusion": "success",
        "repository": {"id": 9, "full_name": REPOSITORY},
        "head_repository": {"id": 9, "full_name": REPOSITORY},
    }
    result.update(changes)
    return result


class API:
    def __init__(self, runs=None):
        self.runs = [run()] if runs is None else runs
        self.workflow = {"id": 7, "path": gate.WORKFLOW_PATH,
                         "name": gate.WORKFLOW_NAME, "state": "active"}
        self.listings = []
        self.current = None
        self.main_reads = []
        self.calls = []

    def __call__(self, endpoint, *, paginate=False):
        self.calls.append((endpoint, paginate))
        if endpoint.endswith("git/ref/heads/main"):
            return self.main_reads.pop(0) if self.main_reads else {
                "ref": "refs/heads/main", "object": {"sha": SHA}}
        if endpoint.endswith("/" + gate.WORKFLOW_FILE):
            return self.workflow
        if "/workflows/7/runs?" in endpoint:
            if self.listings:
                return self.listings.pop(0)
            return [{"total_count": len(self.runs), "workflow_runs": self.runs}]
        if "/actions/runs/" in endpoint:
            return self.current or next(r for r in self.runs if endpoint.endswith(str(r["id"])))
        raise AssertionError(f"Unexpected API request: {endpoint}")


class ExactSourceTests(unittest.TestCase):
    def check(self, api):
        return gate.check_once(REPOSITORY, SHA, api=api)

    def test_success_uses_authoritative_workflow_and_unfiltered_exact_sha_list(self):
        api = API()
        self.assertEqual(self.check(api)["id"], 101)
        lists = [(url, paginate) for url, paginate in api.calls if "runs?" in url]
        self.assertEqual(len(lists), 2)
        for url, paginate in lists:
            self.assertIn(f"head_sha={SHA}&event=push&branch=main", url)
            self.assertNotIn("status=", url)  # Older green runs must not hide a later failure.
            self.assertTrue(paginate)

    def test_all_identity_mismatches_reject(self):
        cases = {
            "different SHA": {"head_sha": "b" * 40},
            "PR merge": {"event": "pull_request"},
            "manual Lean run": {"event": "workflow_dispatch"},
            "different branch": {"head_branch": "feature"},
            "different workflow ID": {"workflow_id": 8},
            "same name wrong file": {"path": ".github/workflows/fake.yml"},
            "different repository": {"repository": {"id": 10, "full_name": "fork/repo"}},
            "fork head": {"head_repository": {"id": 10, "full_name": REPOSITORY}},
            "missing head": {"head_repository": {}},
            "invalid attempt": {"run_attempt": 0},
            "boolean ID": {"id": True},
        }
        for label, changes in cases.items():
            with self.subTest(label=label), self.assertRaises(gate.Rejected):
                self.check(API([run(**changes)]))

    def test_workflow_metadata_must_match(self):
        for key, value in [("path", "fake.yml"), ("name", "PDFs"),
                           ("state", "disabled_manually"), ("id", 0)]:
            api = API()
            api.workflow[key] = value
            with self.subTest(key=key), self.assertRaises(gate.Rejected):
                self.check(api)

    def test_missing_and_pending_never_authorize(self):
        with self.assertRaises(gate.Pending):
            self.check(API([]))
        for status in ["queued", "in_progress", "waiting", "pending", "requested"]:
            with self.subTest(status=status), self.assertRaises(gate.Pending):
                self.check(API([run(status=status, conclusion=None)]))

    def test_every_unsuccessful_completed_conclusion_rejects(self):
        for conclusion in ["failure", "cancelled", "timed_out", "skipped", "neutral",
                           "action_required", "stale", None]:
            with self.subTest(conclusion=conclusion), self.assertRaises(gate.Rejected):
                self.check(API([run(conclusion=conclusion)]))

    def test_latest_run_number_wins_over_older_success_and_opaque_id(self):
        older = run(id=900, run_number=19)
        latest = run(id=101, run_number=20, conclusion="failure")
        with self.assertRaises(gate.Rejected):
            self.check(API([older, latest]))

    def test_current_attempt_overrides_stale_success_in_listing(self):
        api = API()
        api.current = run(run_attempt=2, status="in_progress", conclusion=None)
        with self.assertRaises(gate.Pending):
            self.check(api)
        api.current = run(run_attempt=2, conclusion="cancelled")
        with self.assertRaises(gate.Rejected):
            self.check(api)

    def test_successful_rerun_is_allowed_after_latest_listing_confirms_it(self):
        api = API()
        api.current = run(run_attempt=2)
        api.listings = [[{"total_count": 1, "workflow_runs": [run()]}],
                        [{"total_count": 1, "workflow_runs": [run(run_attempt=2)]}]]
        self.assertEqual(self.check(api)["run_attempt"], 2)

    def test_new_run_or_attempt_during_check_rejects(self):
        for later in [run(id=102, run_number=21), run(run_attempt=2),
                      run(status="queued", conclusion=None)]:
            api = API()
            api.listings = [[{"total_count": 1, "workflow_runs": [run()]}],
                            [{"total_count": 1, "workflow_runs": [later]}]]
            with self.subTest(later=later), self.assertRaises(gate.Rejected):
                self.check(api)

    def test_pagination_and_incomplete_response(self):
        api = API([run(id=100, run_number=19, conclusion="failure"), run()])
        pages = [{"total_count": 2, "workflow_runs": [api.runs[0]]},
                 {"total_count": 2, "workflow_runs": [api.runs[1]]}]
        api.listings = [pages, pages]
        self.assertEqual(self.check(api)["id"], 101)
        api = API()
        api.listings = [[{"total_count": 2, "workflow_runs": [run()]}]]
        with self.assertRaises(gate.Rejected):
            self.check(api)

    def test_duplicate_or_ambiguous_runs_reject(self):
        for runs in [[run(), run()], [run(), run(id=102)]]:
            with self.assertRaises(gate.Rejected):
                self.check(API(runs))

    def test_main_freshness_before_and_after_ci_read(self):
        stale = {"ref": "refs/heads/main", "object": {"sha": "b" * 40}}
        for reads in [[stale], [{"ref": "refs/heads/main", "object": {"sha": SHA}}, stale]]:
            api = API()
            api.main_reads = reads
            with self.assertRaises(gate.Rejected):
                self.check(api)

    def test_pending_wait_is_bounded_and_failure_does_not_wait(self):
        now = [0.0]
        def sleep(seconds):
            now[0] += seconds
        with self.assertRaises(gate.Pending):
            gate.wait_for_success(REPOSITORY, SHA, 31, api=API([]),
                                  clock=lambda: now[0], sleep=sleep)
        self.assertEqual(now[0], 31)
        with self.assertRaises(gate.Rejected):
            gate.wait_for_success(REPOSITORY, SHA, 1200, api=API([run(conclusion="failure")]),
                                  clock=lambda: now[0], sleep=sleep)
        self.assertEqual(now[0], 31)

    def test_pending_attempt_can_finish_during_bounded_wait(self):
        api = API([run(run_attempt=2, status="in_progress", conclusion=None)])
        now = [0.0]
        def finish(seconds):
            now[0] += seconds
            api.runs = [run(run_attempt=2)]
        result = gate.wait_for_success(REPOSITORY, SHA, 60, api=api,
                                       clock=lambda: now[0], sleep=finish)
        self.assertEqual(result["run_attempt"], 2)
        self.assertEqual(now[0], 30)

    def test_cli_fails_closed_when_api_transport_or_json_fails(self):
        for error in [subprocess.CalledProcessError(1, ["gh", "api"]),
                      subprocess.TimeoutExpired(["gh", "api"], 60), ValueError("Invalid JSON")]:
            with self.subTest(error=error), patch.object(gate, "wait_for_success", side_effect=error), \
                    patch("sys.argv", ["check_abstract_ci.py", "--repository", REPOSITORY, "--sha", SHA]), \
                    contextlib.redirect_stderr(io.StringIO()) as stderr:
                self.assertEqual(gate.main(), 1)
                self.assertIn("publication denied", stderr.getvalue())

    def test_transport_only_uses_get_and_paginates(self):
        with patch.object(subprocess, "run") as invoke:
            invoke.return_value.stdout = "[]"
            gate.gh_get("repos/example/repo/actions/runs", paginate=True)
        command = invoke.call_args.args[0]
        self.assertIn("GET", command)
        self.assertIn("--paginate", command)
        self.assertIn("--slurp", command)
        self.assertEqual(command[command.index("--hostname") + 1], "github.com")


# This fake replaces only GitHub's API/release CLI at the process boundary. The
# real workflow shell, provenance verifier and check_abstract_ci.py all execute.
FAKE_GH = r'''#!/usr/bin/env python3
import json, os, pathlib, sys
root = pathlib.Path(os.environ["FAKE_ROOT"])
config = json.loads((root / "config.json").read_text())
args = sys.argv[1:]
if args[0] == "api":
    endpoint = next(a for a in args if a.startswith("repos/"))
    if endpoint.endswith("git/ref/heads/main"):
        if "--jq" in args:
            print(config["sha"])
        else:
            print(json.dumps({"ref": "refs/heads/main", "object": {"sha": config["sha"]}}))
    elif endpoint.endswith("/lean_action_ci.yml"):
        counter = root / "counter"
        n = int(counter.read_text()) + 1 if counter.exists() else 1
        counter.write_text(str(n))
        print(json.dumps(config["workflow"]))
    else:
        run = config["run"]
        if int((root / "counter").read_text()) >= config["deny_at"]:
            run["conclusion"] = "failure"
        if "/workflows/7/runs?" in endpoint:
            print(json.dumps([{"total_count": 1, "workflow_runs": [run]}]))
        elif "/actions/runs/" in endpoint:
            print(json.dumps(run))
        else:
            raise SystemExit("Unexpected API: " + endpoint)
elif args[:2] == ["release", "view"]:
    if "--json" in args:
        print("retired.pdf" if config["retired"] else "")
    elif not config["exists"]:
        raise SystemExit(1)
else:
    with (root / "writes").open("a") as f:
        f.write(json.dumps(args) + "\n")
'''


class WorkflowBoundaryTests(unittest.TestCase):
    def test_each_release_mutation_is_guarded_by_real_api_policy(self):
        workflow = (ROOT / ".github/workflows/abstracts.yml").read_text()
        shell = textwrap.dedent(workflow.split("      - name: Publish PDFs for the current main revision", 1)[1]
                                .split("        run: |\n", 1)[1])
        cases = [
            (False, False, 1, []),   # Initial wait rejects failed validation.
            (False, False, 2, []),   # Recheck before release creation.
            (True, True, 2, []),     # Recheck before retiring an asset.
            (True, False, 2, []),    # Recheck before overwriting assets.
            (True, False, 3, ["upload"]),  # Failure between upload and release edit.
            (False, True, 999, ["create", "delete-asset", "upload", "edit"]),
        ]
        for exists, retired, deny_at, expected in cases:
            with self.subTest(exists=exists, retired=retired, deny_at=deny_at), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                (root / "bin").mkdir()
                gh = root / "bin/gh"
                gh.write_text(FAKE_GH)
                gh.chmod(0o755)
                (root / "scripts").mkdir()
                (root / "scripts/check_abstract_ci.py").write_bytes((ROOT / "scripts/check_abstract_ci.py").read_bytes())
                artifact = root / "abstract-artifact"
                artifact.mkdir()
                pdf = artifact / "catalogue.pdf"
                pdf.write_bytes(b"%PDF-test")
                import hashlib
                source = {"source_sha": SHA, "repository": REPOSITORY, "event": "push",
                          "ref": "refs/heads/main", "source_dirty": False, "run_url": "https://example.com/build",
                          "catalogue": {"pdf": pdf.name, "pdf_sha256": hashlib.sha256(pdf.read_bytes()).hexdigest()},
                          "documents": []}
                (artifact / "provenance.json").write_text(json.dumps(source))
                (root / "config.json").write_text(json.dumps({
                    "sha": SHA, "run": run(), "workflow": API().workflow,
                    "exists": exists, "retired": retired, "deny_at": deny_at}))
                env = {**os.environ, "PATH": str(root / "bin") + os.pathsep + os.environ["PATH"],
                       "FAKE_ROOT": tmp, "GITHUB_REPOSITORY": REPOSITORY, "GITHUB_SHA": SHA,
                       "GITHUB_STEP_SUMMARY": str(root / "summary")}
                result = subprocess.run(["bash", "-c", shell], cwd=root, env=env,
                                        capture_output=True, text=True, timeout=20)
                writes = root / "writes"
                actual = [json.loads(line)[1] for line in writes.read_text().splitlines()] if writes.exists() else []
                self.assertEqual(actual, expected, result.stderr)
                self.assertEqual(result.returncode == 0, deny_at == 999, result.stderr)

    def test_permissions_events_and_immutable_artifact_selection(self):
        workflow = (ROOT / ".github/workflows/abstracts.yml").read_text()
        build, publish = workflow.split("  publish:\n")
        self.assertIn("  pull_request:\n", build)
        self.assertNotIn("contents: write", build)
        self.assertIn("permissions:\n  contents: read", build)
        self.assertIn("if: github.event_name == 'push' && github.ref == 'refs/heads/main'", publish)
        self.assertIn("contents: write\n      actions: read", publish)
        self.assertIn("artifact-id: ${{ steps.artifact.outputs.artifact-id }}", build)
        self.assertIn("artifact-ids: ${{ needs.build.outputs.artifact-id }}", publish)
        self.assertIn('[[ "$ARTIFACT_ID" =~ ^[0-9]+$ ]]', publish)
        self.assertNotIn("github.run_attempt", publish)
        for mutation in ["create", "delete-asset", "upload", "edit"]:
            self.assertIn("publish " + mutation, publish)
            self.assertNotIn("gh release " + mutation, publish)


if __name__ == "__main__":
    unittest.main()
