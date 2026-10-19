/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (repository coordination tests)

import Tests.Support

namespace Coordination.Tests

private structure WorktreeSnapshot where
  head : String
  headFile : ByteArray
  index : ByteArray
  fetchHead : ByteArray
  status : String
  dirty : String
  untracked : String
  deriving BEq

private def snapshot (directory : System.FilePath) : IO WorktreeSnapshot := do
  let gitdir := System.FilePath.mk (← git directory #["rev-parse", "--absolute-git-dir"])
  return {
    head := ← git directory #["rev-parse", "HEAD"]
    headFile := ← IO.FS.readBinFile (gitdir / "HEAD")
    index := ← IO.FS.readBinFile (gitdir / "index")
    fetchHead := ← IO.FS.readBinFile (gitdir / "FETCH_HEAD")
    status := ← git directory #["--no-optional-locks", "status", "--porcelain=v1"]
    dirty := ← IO.FS.readFile (directory / "allowed/a.txt")
    untracked := ← IO.FS.readFile (directory / "untracked.txt") }

private def dirtyWorktree (directory : System.FilePath) : IO Unit := do
  IO.FS.writeFile (directory / "allowed/a.txt") "staged\n"
  discard <| git directory #["add", "--", "allowed/a.txt"]
  IO.FS.writeFile (directory / "allowed/a.txt") "staged plus unstaged\n"
  IO.FS.writeFile (directory / "untracked.txt") "untracked\n"

/-- A normal wildcard refmap must not turn a private fetch into a shared tracking-ref write.
The linked worktrees have separate indexes and FETCH_HEAD files but share remote-tracking refs. -/
private def testFetchIsolation : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  check ((← git fixture.repository #["config", "--get-all", "remote.origin.fetch"]) ==
    "+refs/heads/*:refs/remotes/origin/*") "Fixture lacks the normal wildcard fetch refmap"
  discard <| repository.update (0 : Nat) "initialize fetch test"
    (fun state => pure (state, none)) true
  let old ← fixture.ref Git.boardRef
  let linked := fixture.directory / "linked"
  discard <| git fixture.repository #["worktree", "add", "--quiet", "--detach",
    linked.toString, fixture.base]
  let other ← Git.Repository.open linked
  for directory in [fixture.repository, linked] do
    discard <| git directory #["fetch", "--quiet", "origin", "main"]
    dirtyWorktree directory
  let before ← snapshot fixture.repository
  let linkedBefore ← snapshot linked
  let tracking ← repository.run #["for-each-ref", "--format=%(refname) %(objectname) %(symref)",
    "refs/remotes/"]
  check ((← repository.run #["rev-parse", "refs/remotes/origin/coordination"]).trimAsciiEnd.toString
    == old) "Fixture tracking ref did not start at the previous journal"
  -- Advance the bare origin directly: neither worktree has fetched or pushed this commit.
  configure fixture.origin
  let tree ← git fixture.origin #["rev-parse", old ++ "^{tree}"]
  let next ← git fixture.origin #["commit-tree", tree, "-p", old] (some "advance remote journal\n")
  discard <| git fixture.origin #["update-ref", Git.boardRef, next, old]
  let preserved : IO Unit := do
    check ((← repository.run #["for-each-ref", "--format=%(refname) %(objectname) %(symref)",
      "refs/remotes/"]) == tracking) "Private fetch changed shared remote-tracking refs"
    check ((← snapshot fixture.repository) == before) "Private fetch changed primary worktree state"
    check ((← snapshot linked) == linkedBefore) "Private fetch changed linked worktree state"
    check ((← repository.run #["for-each-ref", "--format=%(refname)",
      "refs/coordination-fetch/"]).isEmpty) "Private fetch leaked a temporary ref"
  for caller in [other, repository] do
    check ((← caller.fetch Git.boardRef) == some next) "Private fetch returned a stale journal"
    preserved
  -- A normal tracking-ref lock in shared Git storage must not interfere with either fetch.
  let lock := System.FilePath.mk (← git fixture.repository #["rev-parse", "--path-format=absolute",
    "--git-path", "refs/remotes/origin/coordination.lock"])
  IO.FS.writeFile lock "held by another worktree\n"
  try
    check ((← other.fetch Git.boardRef) == some next) "Tracking lock blocked isolated fetch"
    check ((← IO.FS.readFile lock) == "held by another worktree\n") "Fetch touched another ref lock"
    preserved
  finally
    IO.FS.removeFile lock
  -- Cleanup also applies when a failure is reported after Git has created the temporary ref.
  let failed := {other with execute := fun args input => do
    let result ← other.execute args input
    if args[0]? == some "fetch" && result.exitCode == 0 then
      pure {result with exitCode := 1, stderr := "injected failure after receiving objects"}
    else pure result }
  expectError (failed.fetch Git.boardRef) "injected failure after receiving objects"
  preserved
  check ((← other.fetch "refs/heads/missing" false).isNone) "Missing optional ref must remain none"
  expectError (other.fetch "refs/heads/missing") "Cannot read"
  preserved

def fetchTests : List (String × IO Unit) := [
  ("private fetches isolate linked worktrees, tracking refs, locks and failure cleanup",
    testFetchIsolation)]

end Coordination.Tests
