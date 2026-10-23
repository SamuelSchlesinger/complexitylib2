"""Cache routing and publication guards, using isolated Git repositories and fake services."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parent / "cache"
TOOLCHAIN = "leanprover--lean4---v4.36.0-rc1"
SCOPES = {"cslib": "leanprover/cslib", "complexitylib": "cslib-community/complexitylib"}

# Record commands and their payloads before the scripts remove their staging directories.
# The fake Lake emits distinct package artifacts; it never invokes Lean or touches shared caches.
FAKE_TOOL = r'''#!/usr/bin/env python3
import json, os, pathlib, sys

tool = pathlib.Path(sys.argv[0]).name
args = sys.argv[1:]
event = {"tool": tool, "args": args, "cwd": os.getcwd(),
         "artifact_endpoint": os.environ.get("LAKE_CACHE_ARTIFACT_ENDPOINT"),
         "revision_endpoint": os.environ.get("LAKE_CACHE_REVISION_ENDPOINT")}
if tool == "gcloud":
    sources = sys.stdin.read().splitlines() if "-I" in args else [args[-2]]
    event["contents"] = [pathlib.Path(p).read_text() for p in sources]
with open(os.environ["CACHE_TEST_LOG"], "a") as log:
    log.write(json.dumps(event) + "\n")

def option(name):
    for i, arg in enumerate(args):
        if arg == name:
            return args[i + 1]
        if arg.startswith(name + "="):
            return arg[len(name) + 1:]
    return None

if tool == "lake" and args[0] == "build":
    package = option("--package") or "complexitylib"
    if os.environ.get("CACHE_TEST_FAIL_BUILD") == package:
        sys.exit(1)
    pathlib.Path(option("-o")).write_text(json.dumps({"package": package}) + "\n")
elif tool == "lake" and args[:2] == ["cache", "stage"]:
    mapping = pathlib.Path(args[2])
    stage = pathlib.Path(args[3])
    stage.mkdir(parents=True)
    (stage / "outputs.jsonl").write_bytes(mapping.read_bytes())
    package = json.loads(mapping.read_text())["package"]
    (stage / (package + ".ltar")).write_text(package)
elif tool == "lake" and args[:2] == ["cache", "get"]:
    if os.environ.get("CACHE_TEST_FAIL_GET"):
        sys.exit(1)
elif tool == "lake" and args == ["exe", "cache", "get"]:
    if os.environ.get("CACHE_TEST_FAIL_MATHLIB"):
        sys.exit(1)
elif tool == "gcloud":
    failure_scope = os.environ.get("CACHE_TEST_FAIL_ARTIFACT")
    if failure_scope and "/a0/" in args[-1] and failure_scope in args[-1]:
        sys.exit(1)
'''


@unittest.skipUnless(shutil.which("git"), "git is required")
class CacheTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory(prefix="cache scripts ")
        self.addCleanup(temp.cleanup)
        self.temp = Path(temp.name).resolve()
        self.root = self.temp / "complexitylib"
        self.cslib = self.root / ".lake/packages/cslib"
        self.cslib.mkdir(parents=True)
        self.log = self.temp / "events.jsonl"
        self.env = {k: v for k, v in os.environ.items()
                    if not k.startswith(("GIT_", "CACHE_TEST_", "LAKE_CACHE_"))
                    and k != "COMPLEXITYLIB_CACHE_URL"}
        self.env.update({"GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1",
                         "GIT_AUTHOR_NAME": "Cache fixture", "GIT_COMMITTER_NAME": "Cache fixture",
                         "GIT_AUTHOR_EMAIL": "cache@example.invalid",
                         "GIT_COMMITTER_EMAIL": "cache@example.invalid",
                         "CACHE_TEST_LOG": str(self.log)})
        for repo in (self.root, self.cslib):
            self.git(repo, "init", "-q")
            (repo / "lean-toolchain").write_text("leanprover/lean4:v4.36.0-rc1\n")
        (self.cslib / "Cslib.lean").write_text("-- dependency fixture\n")
        self.cslib_sha = self.commit(self.cslib)
        (self.root / ".gitignore").write_text(".lake/\n")
        (self.root / "lake-manifest.json").write_text(json.dumps({
            "packagesDir": ".lake/packages", "packages": [
                {"name": "cslib", "type": "git", "rev": self.cslib_sha,
                 "url": "https://github.com/leanprover/cslib"}]}))
        shutil.copytree(SCRIPTS, self.root / "scripts/cache")
        self.root_sha = self.commit(self.root)
        bin_dir = self.temp / "bin"
        bin_dir.mkdir()
        for name in ("lake", "gcloud"):
            executable = bin_dir / name
            executable.write_text(FAKE_TOOL)
            executable.chmod(0o755)
        self.env["PATH"] = str(bin_dir) + os.pathsep + os.environ["PATH"]

    def git(self, repo, *args):
        return subprocess.check_output(["git", "-C", str(repo), *args],
                                       env=self.env, text=True).strip()

    def commit(self, repo):
        self.git(repo, "add", ".")
        self.git(repo, "commit", "-qm", "fixture")
        return self.git(repo, "rev-parse", "HEAD")

    def run_script(self, name, *args, cwd=None, **env):
        return subprocess.run(["bash", str(self.root / "scripts/cache" / name), *args],
                              cwd=cwd or self.root, env={**self.env, **env},
                              capture_output=True, text=True)

    def events(self, tool=None):
        events = [json.loads(line) for line in self.log.read_text().splitlines()] \
            if self.log.exists() else []
        return [e for e in events if tool is None or e["tool"] == tool]

    def assert_success(self, result):
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    @staticmethod
    def option(args, name):
        for i, arg in enumerate(args):
            if arg == name:
                return args[i + 1]
            if arg.startswith(name + "="):
                return arg[len(name) + 1:]
        return None

    def test_publish_full_libraries_with_their_own_revisions_and_artifacts_first(self):
        self.assert_success(self.run_script("upload.sh", "fixture-bucket"))
        builds = [e["args"] for e in self.events("lake") if e["args"][0] == "build"]
        self.assertEqual(len(builds), 2)
        dependency = next(args for args in builds if self.option(args, "--package") == "cslib")
        self.assertIn("@cslib/Cslib", dependency)
        self.assertTrue({"--wfail", "--iofail"} <= set(dependency))
        project = next(args for args in builds
                       if self.option(args, "--package") in (None, "complexitylib"))
        self.assertTrue({"Complexity", "ComplexityTests"} <= set(project))
        uploads = self.events("gcloud")
        self.assertEqual(len(uploads), 4)
        self.assertTrue(all("--no-clobber" in event["args"] for event in uploads))
        for package, revision in (("cslib", self.cslib_sha), ("complexitylib", self.root_sha)):
            scope = SCOPES[package]
            artifact = next(i for i, e in enumerate(uploads)
                            if e["args"][-1] == f"gs://fixture-bucket/a0/{scope}/")
            mapping = next(i for i, e in enumerate(uploads) if e["args"][-1] ==
                           f"gs://fixture-bucket/r0/{scope}/tc/{TOOLCHAIN}/{revision}.jsonl")
            self.assertLess(artifact, mapping)
            self.assertEqual(uploads[artifact]["contents"], [package])
            self.assertEqual(json.loads(uploads[mapping]["contents"][0])["package"], package)

    def test_dirty_dependency_refuses_all_uploads(self):
        (self.cslib / "Cslib.lean").write_text("-- changed dependency\n")
        self.assertNotEqual(self.run_script("upload.sh", "fixture-bucket").returncode, 0)
        self.assertEqual(self.events("gcloud"), [])

    def test_dependency_revision_differing_from_manifest_refuses_all_uploads(self):
        (self.cslib / "Cslib.lean").write_text("-- a different committed dependency\n")
        self.commit(self.cslib)
        self.assertNotEqual(self.run_script("upload.sh", "fixture-bucket").returncode, 0)
        self.assertEqual(self.events("gcloud"), [])

    def test_dirty_root_refuses_all_uploads(self):
        (self.root / "lean-toolchain").write_text("leanprover/lean4:changed\n")
        self.assertNotEqual(self.run_script("upload.sh", "fixture-bucket").returncode, 0)
        self.assertEqual(self.events("gcloud"), [])

    def test_failed_artifact_upload_does_not_publish_its_mapping(self):
        result = self.run_script("upload.sh", "fixture-bucket",
                                 CACHE_TEST_FAIL_ARTIFACT=SCOPES["cslib"])
        self.assertNotEqual(result.returncode, 0)
        self.assertTrue(any("/a0/leanprover/cslib/" in e["args"][-1]
                            for e in self.events("gcloud")))
        self.assertFalse(any("/r0/leanprover/cslib/" in e["args"][-1]
                             for e in self.events("gcloud")))

    def test_standalone_download_uses_callers_checkout_and_portable_scope(self):
        standalone = self.temp / "standalone cslib"
        standalone.mkdir()
        url = "https://cache.example.invalid"
        result = self.run_script("get-cslib.sh", cwd=standalone, COMPLEXITYLIB_CACHE_URL=url)
        self.assert_success(result)
        event, = self.events("lake")
        self.assertEqual(event["args"][:2], ["cache", "get"])
        self.assertEqual(event["cwd"], str(standalone))
        self.assertEqual(self.option(event["args"], "--repo"), SCOPES["cslib"])
        self.assertEqual(self.option(event["args"], "--platform"), "")
        self.assertIsNone(self.option(event["args"], "--package"))
        self.assertEqual(event["artifact_endpoint"], url + "/a0")
        self.assertEqual(event["revision_endpoint"], url + "/r0")

    def test_optional_cache_failure_succeeds_with_a_note(self):
        result = self.run_script("get-cslib.sh", CACHE_TEST_FAIL_GET="1")
        self.assert_success(result)
        self.assertIn("note:", result.stderr.lower())
        event, = self.events("lake")
        self.assertEqual(event["args"][:2], ["cache", "get"])

    def test_project_download_continues_through_optional_failures_in_dependency_order(self):
        result = self.run_script("get.sh", CACHE_TEST_FAIL_GET="1", CACHE_TEST_FAIL_MATHLIB="1")
        self.assert_success(result)
        mathlib, cslib, project = self.events("lake")
        self.assertEqual(mathlib["args"], ["exe", "cache", "get"])
        self.assertEqual(self.option(cslib["args"], "--repo"), SCOPES["cslib"])
        self.assertEqual(self.option(cslib["args"], "--package"), "cslib")
        self.assertEqual(self.option(cslib["args"], "--platform"), "")
        self.assertEqual(self.option(project["args"], "--repo"), SCOPES["complexitylib"])
        self.assertTrue(all(e["cwd"] == str(self.root) for e in (mathlib, cslib, project)))

    def test_empty_url_skips_custom_caches_but_keeps_mathlib(self):
        self.assert_success(self.run_script("get-cslib.sh", COMPLEXITYLIB_CACHE_URL=""))
        self.assertEqual(self.events(), [])
        self.assert_success(self.run_script("get.sh", COMPLEXITYLIB_CACHE_URL=""))
        event, = self.events()
        self.assertEqual(event["args"], ["exe", "cache", "get"])

    def test_standalone_helper_rejects_unknown_arguments(self):
        result = self.run_script("get-cslib.sh", "--package=other")
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(self.events(), [])


if __name__ == "__main__":
    unittest.main()
