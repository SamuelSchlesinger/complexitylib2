/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (repository coordination tests)

import Coordination.Git

/-!
# Coordinator regression tests

Protocol tests use explicit logical time. Integration tests use disposable local bare Git
repositories; they never invoke project validation or contact a hosting service.
-/

namespace Coordination.Tests

open Lean

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

def expectError {α : Type} (action : IO α) (message : String) : IO Unit := do
  let failed ← try
    let _ ← action
    pure false
  catch error =>
    check ((error.toString.splitOn message).length > 1) s!"Wrong error: {error} (expected {message})"
    pure true
  check failed s!"Expected failure: {message}"

/-- All fixture commands have private configuration and argument-array subprocess calls. -/
def git (directory : System.FilePath) (args : Array String)
    (input : Option String := none) : IO String := do
  let result ← IO.Process.output {
    cmd := "git"
    args := #["-C", directory.toString] ++ args
    env := #[("GIT_CONFIG_GLOBAL", some "/dev/null"), ("GIT_CONFIG_NOSYSTEM", some "1"),
      ("GIT_TERMINAL_PROMPT", some "0")]
  } input
  check (result.exitCode == 0) s!"git {args} failed: {result.stderr}"
  pure result.stdout.trimAsciiEnd.toString

def configure (directory : System.FilePath) : IO Unit := do
  let _ ← git directory #["config", "user.name", "Coordination Test"]
  let _ ← git directory #["config", "user.email", "coordination@example.invalid"]
  let _ ← git directory #["config", "commit.gpgsign", "false"]
  let _ ← git directory #["config", "tag.gpgsign", "false"]

structure Fixture where
  directory : System.FilePath
  origin : System.FilePath
  repository : System.FilePath
  base : String

def fixture (directory : System.FilePath) : IO Fixture := do
  let seed := directory / "seed"
  IO.FS.createDirAll (seed / "allowed")
  let _ ← git seed #["init", "--quiet", "--initial-branch=main"]
  configure seed
  IO.FS.writeFile (seed / "allowed/a.txt") "original\n"
  IO.FS.writeFile (seed / "outside.txt") "outside\n"
  let _ ← git seed #["add", "."]
  let _ ← git seed #["commit", "--quiet", "-m", "initial"]
  let base ← git seed #["rev-parse", "HEAD"]
  let origin := directory / "origin.git"
  let repository := directory / "caller"
  let _ ← git directory #["clone", "--quiet", "--bare", seed.toString, origin.toString]
  let _ ← git directory #["clone", "--quiet", origin.toString, repository.toString]
  configure repository
  pure { directory, origin, repository, base }

def Fixture.commit (fixture : Fixture) (path content : String) : IO String := do
  let target := fixture.repository / path
  if let some parent := target.parent then IO.FS.createDirAll parent
  IO.FS.writeFile target content
  let _ ← git fixture.repository #["add", "--", path]
  let _ ← git fixture.repository #["commit", "--quiet", "-m", "change"]
  git fixture.repository #["rev-parse", "HEAD"]


def Fixture.open (fixture : Fixture) : IO Git.Repository := do
  let repository ← Git.Repository.open fixture.repository
  -- Local fixture identity controls commit-tree; no user-wide configuration is written.
  let execute : Git.Runner := fun args input => IO.Process.output {
    cmd := "git", args := #["-C", fixture.repository.toString] ++ args
    env := #[("GIT_CONFIG_GLOBAL", some "/dev/null"), ("GIT_CONFIG_NOSYSTEM", some "1"),
      ("GIT_TERMINAL_PROMPT", some "0")]
  } input
  pure {repository with execute}

def Fixture.ref (fixture : Fixture) (ref : String) : IO String :=
  git fixture.origin #["rev-parse", ref]

def withFixture (action : Fixture → IO Unit) : IO Unit :=
  IO.FS.withTempDir fun directory => do action (← fixture directory)

end Coordination.Tests
