/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (repository coordination tests)

import Tests.Support
import Tests.Runtime
import Coordination.Protocol

/-!
# Coordinator regression tests

Protocol tests use explicit logical time. Integration tests use disposable local bare Git
repositories; they never invoke project validation or contact a hosting service.
-/

namespace Coordination.Tests

open Lean

private structure Journal where
  left : Nat := 0
  right : Nat := 0
  owner : String := ""
  landed : Bool := false
  deriving BEq, Repr, ToJson, FromJson

private def initializeBoard (repository : Git.Repository) : IO Unit := do
  discard <| repository.update ({} : Journal) "initialize tests" (fun state => pure (state, none)) true

private def journal (repository : Git.Repository) : IO Journal := do
  let some (_, value) ← repository.readBoard | throw <| IO.userError "Missing board"
  IO.ofExcept <| fromJson? value

private def testJournalAndFetch : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  check ((← repository.fetch Git.boardRef false).isNone) "Missing optional board must be none"
  expectError (repository.fetch Git.boardRef) "Cannot read"
  initializeBoard repository
  let before ← fixture.ref Git.boardRef
  discard <| repository.update ({} : Journal) "unchanged" (fun state => pure (state, none))
  check ((← fixture.ref Git.boardRef) == before) "No-op update created a journal commit"
  check ((← repository.fetch Git.mainRef) == some fixture.base) "Fetched wrong main"
  check ((← repository.run #["for-each-ref", "--format=%(refname)", "refs/coordination-fetch/"]).isEmpty)
    "Temporary fetch refs leaked"
  check ((← journal repository) == {}) "Initial journal did not round-trip"

private def testRawPathsAndRename : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  let paths := [" allowed/leading.txt", "\nallowed/newline.txt", "allowed/tab\tname.txt",
    "allowed/trailing\n"]
  for path in paths do discard <| fixture.commit path "unusual filename\n"
  discard <| git fixture.repository #["mv", "outside.txt", "allowed/renamed.txt"]
  discard <| git fixture.repository #["commit", "--quiet", "-m", "cross-scope rename"]
  let changed ← repository.changedPaths fixture.base (← repository.head)
  for path in paths ++ ["outside.txt", "allowed/renamed.txt"] do
    check (changed.contains path) s!"Path was lost or trimmed: {repr path}; got {repr changed}"
  check (changed.length == paths.length + 2) "Unexpected changed-path count"

private def testCallerPreservation : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  initializeBoard repository
  discard <| git fixture.repository #["fetch", "--quiet", "origin", "main"]
  IO.FS.writeFile (fixture.repository / "allowed/a.txt") "staged\n"
  discard <| git fixture.repository #["add", "allowed/a.txt"]
  IO.FS.writeFile (fixture.repository / "allowed/a.txt") "staged plus unstaged\n"
  IO.FS.writeFile (fixture.repository / "untracked.txt") "untracked\n"
  let gitdir := System.FilePath.mk (← git fixture.repository #["rev-parse", "--absolute-git-dir"])
  let index ← IO.FS.readBinFile (gitdir / "index")
  let fetchHead ← IO.FS.readBinFile (gitdir / "FETCH_HEAD")
  let status ← repository.run #["status", "--porcelain=v1"]
  let branch ← repository.run #["symbolic-ref", "HEAD"]
  discard <| repository.update ({} : Journal) "dirty caller" fun state =>
    pure ({state with left := state.left + 1}, none)
  check ((← IO.FS.readBinFile (gitdir / "index")) == index) "Caller index changed"
  check ((← IO.FS.readBinFile (gitdir / "FETCH_HEAD")) == fetchHead) "Caller FETCH_HEAD changed"
  check ((← repository.run #["status", "--porcelain=v1"]) == status) "Caller status changed"
  check ((← repository.run #["symbolic-ref", "HEAD"]) == branch) "Caller branch changed"
  check ((← repository.head) == fixture.base) "Caller HEAD changed"
  check ((← IO.FS.readFile (fixture.repository / "allowed/a.txt")) == "staged plus unstaged\n")
    "Caller dirty file changed"
  check ((← IO.FS.readFile (fixture.repository / "untracked.txt")) == "untracked\n")
    "Caller untracked file changed"

private def testCleanPreservesIndex : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  -- Rewriting identical bytes changes stat data, so ordinary git status refreshes the index.
  IO.FS.writeFile (fixture.repository / "allowed/a.txt") "original\n"
  let gitdir := System.FilePath.mk (← git fixture.repository #["rev-parse", "--absolute-git-dir"])
  let before ← IO.FS.readBinFile (gitdir / "index")
  repository.clean fixture.base
  check ((← IO.FS.readBinFile (gitdir / "index")) == before) "Cleanliness check rewrote caller index"
  IO.FS.writeFile (fixture.repository / "allowed/a.txt") "dirty\n"
  let dirtyBefore ← IO.FS.readBinFile (gitdir / "index")
  expectError (repository.clean fixture.base) "clean, dedicated"
  check ((← IO.FS.readBinFile (gitdir / "index")) == dirtyBefore) "Rejected dirty check rewrote caller index"
  check ((← IO.FS.readFile (fixture.repository / "allowed/a.txt")) == "dirty\n")
    "Rejected cleanliness check modified caller file"

private def testAtomicLanding : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  initializeBoard repository
  let head ← fixture.commit "allowed/a.txt" "candidate\n"
  let before ← fixture.ref Git.boardRef
  let result ← repository.update ({} : Journal) "atomic landing" fun state =>
    pure ({state with landed := true}, some {base := fixture.base, head})
  check result.landed "Landing did not return committed state"
  check ((← fixture.ref Git.mainRef) == head) "Atomic landing did not publish main"
  check (← journal repository).landed "Atomic landing did not publish board"
  check ((← git fixture.origin #["rev-parse", Git.boardRef ++ "^"]) == before)
    "Journal did not advance from its exact parent"

private def testAncestorRace : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  initializeBoard repository
  let intermediate ← fixture.commit "allowed/a.txt" "first candidate commit\n"
  let head ← fixture.commit "allowed/a.txt" "second candidate commit\n"
  discard <| git fixture.repository #["push", "--quiet", "origin", "HEAD:refs/heads/work/feature"]
  let before ← fixture.ref Git.boardRef
  let fired ← IO.mkRef false
  let racing := {repository with execute := fun args input => do
    if args[0]? == some "push" && args.contains "--atomic" && !(← fired.get) then
      fired.set true
      discard <| git fixture.origin #["update-ref", Git.mainRef, intermediate, fixture.base]
    repository.execute args input }
  expectError (racing.update ({} : Journal) "racing atomic landing" fun state =>
    pure ({state with landed := true}, some {base := fixture.base, head})) "Push rejected"
  check (← fired.get) "Ancestor race hook did not run"
  check (← repository.ancestor intermediate head) "Race main was not an ancestor of candidate"
  check ((← fixture.ref Git.mainRef) == intermediate) "Race main was overwritten"
  check ((← fixture.ref Git.boardRef) == before) "Failed atomic landing advanced board"
  check (!(← journal repository).landed) "Failed atomic landing marked work merged"

private def testNonFastForwardRefused : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  initializeBoard repository
  let head ← fixture.commit "allowed/a.txt" "new commit\n"
  let before ← fixture.ref Git.boardRef
  expectError (repository.update ({} : Journal) "backward landing" fun state =>
    pure ({state with landed := true}, some {base := head, head := fixture.base})) "fast-forward"
  check ((← fixture.ref Git.boardRef) == before) "Rejected backward landing advanced board"
  check ((← fixture.ref Git.mainRef) == fixture.base) "Rejected backward landing changed main"

private def testDisjointBoardConflict : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  initializeBoard repository
  let fired ← IO.mkRef false
  let calls ← IO.mkRef 0
  let racing := {repository with execute := fun args input => do
    if args[0]? == some "push" && !(← fired.get) then
      fired.set true
      discard <| repository.update ({} : Journal) "competing right write" fun state =>
        pure ({state with right := state.right + 1}, none)
    repository.execute args input }
  let result ← racing.update ({} : Journal) "retry left write" fun state => do
    calls.modify (· + 1)
    pure ({state with left := state.left + 1}, none)
  check (result.left == 1 && result.right == 1) "Conflict lost or duplicated a disjoint edit"
  check ((← calls.get) == 2) "Conflicting edit was not re-evaluated on fresh state"
  check ((← journal repository) == result) "Returned state differs from accepted journal"

private def testSameAssignmentConflict : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  initializeBoard repository
  let fired ← IO.mkRef false
  let racing := {repository with execute := fun args input => do
    if args[0]? == some "push" && !(← fired.get) then
      fired.set true
      discard <| repository.update ({} : Journal) "winning assignment" fun state =>
        pure ({state with owner := "winner"}, none)
    repository.execute args input }
  expectError (racing.update ({} : Journal) "losing assignment" fun state => do
    check state.owner.isEmpty "Assignment already held"
    pure ({state with owner := "loser"}, none)) "Assignment already held"
  check ((← journal repository).owner == "winner") "Losing assignment overwrote winner"

private def testLostAcknowledgements : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  initializeBoard repository
  let head ← fixture.commit "allowed/a.txt" "validated candidate\n"
  for atomic in [false, true] do
    let lost ← IO.mkRef false
    let calls ← IO.mkRef 0
    let losing := {repository with execute := fun args input => do
      let result ← repository.execute args input
      if args[0]? == some "push" && result.exitCode == 0 && !(← lost.get) then
        lost.set true
        pure {result with exitCode := 1, stderr := "lost acknowledgement after acceptance"}
      else pure result }
    let before ← fixture.ref Git.boardRef
    let result ← losing.update ({} : Journal) "lost push response" fun state => do
      calls.modify (· + 1)
      pure ({state with left := state.left + 1, landed := atomic},
        if atomic then some {base := fixture.base, head} else none)
    check (← lost.get) "Lost-ack hook did not run"
    check ((← calls.get) == 1) "Lost acknowledgement repeated an accepted operation"
    check ((← journal repository) == result) "Lost-ack result did not match committed state"
    check ((← git fixture.origin #["rev-parse", Git.boardRef ++ "^"]) == before)
      "Lost acknowledgement created extra journal commits"
    check ((← fixture.ref Git.mainRef) == if atomic then head else fixture.base)
      "Lost acknowledgement produced inconsistent main"

private def testAmbiguousAcceptanceRetry : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  initializeBoard repository
  let accepted ← IO.mkRef false
  let readFailed ← IO.mkRef false
  let ambiguous := {repository with execute := fun args input => do
    if args[0]? == some "ls-remote" && (← accepted.get) && !(← readFailed.get) then
      readFailed.set true
      throw <| IO.userError "injected unavailable follow-up read"
    let result ← repository.execute args input
    if args[0]? == some "push" && result.exitCode == 0 && !(← accepted.get) then
      accepted.set true
      pure {result with exitCode := 1, stderr := "lost accepted response"}
    else pure result }
  let desired (state : Journal) : IO (Journal × Option Git.Landing) :=
    pure ({state with owner := "stable-generation"}, none)
  expectError (ambiguous.update ({} : Journal) "ambiguous claim" desired) "follow-up read"
  check ((← journal repository).owner == "stable-generation") "Accepted claim was not present"
  let committed ← fixture.ref Git.boardRef
  discard <| repository.update ({} : Journal) "retry stable generation" desired
  check ((← fixture.ref Git.boardRef) == committed) "Retry duplicated an accepted idempotent claim"

private def testMalformedBoardRefused : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  discard <| git fixture.repository #["push", "--quiet", "origin", "HEAD:" ++ Git.boardRef]
  let before ← fixture.ref Git.boardRef
  expectError (initializeBoard repository) "Unexpected coordination tree"
  check ((← fixture.ref Git.boardRef) == before) "Malformed board was overwritten"

private def exampleSnapshot : Snapshot := {base := ⟨"base"⟩, head := ⟨"head"⟩}
private def feature : EpicId := ⟨"feature"⟩
private def coordToken : Token := ⟨"coordinator-generation"⟩
private def workToken : Token := ⟨"work-generation"⟩
private def apiToken : Token := ⟨"api-generation"⟩
private def correctnessToken : Token := ⟨"correctness-generation"⟩
private def integrationToken : Token := ⟨"integration-generation"⟩

private def context (name : String) (tokens : List Token := [])
    (snapshot := exampleSnapshot) : Context := {
  actor := {agent := ⟨name⟩, session := ⟨name ++ "-session"⟩}
  now := 1000
  heldTokens := tokens
  main := some snapshot.base
  branchHead := some snapshot.head
  cleanHead := some snapshot.head
  ancestry := [snapshot]
}

private def leadContext (snapshot := exampleSnapshot) : Context :=
  context "lead" [coordToken, integrationToken] snapshot

private def transition (ctx : Context) (state : State) (command : Command) : IO State :=
  (·.state) <$> IO.ofExcept (Coordination.apply ctx state command)

private def reject (ctx : Context) (state : State) (command : Command) (reason : String) : IO Unit :=
  match Coordination.apply ctx state command with
  | .error _ => pure ()
  | .ok _ => throw <| IO.userError s!"Unexpectedly accepted: {reason}"

private def epic (state : State) : IO Epic :=
  match state.epics.find? (fun epic => epic.id == feature) with
  | some epic => pure epic
  | none => throw <| IO.userError "Missing feature epic"

private def submission (state : State) : IO Submission := do
  match (← epic state).phase with
  | .submitted submitted => pure submitted
  | _ => throw <| IO.userError "Expected submitted epic"

/-- Stages: registered, working, submitted, independently approved, integration reserved. -/
private def protocolState (stage : Nat) (snapshot := exampleSnapshot) : IO State := do
  let lead := leadContext snapshot
  let alice := context "alice" [workToken] snapshot
  let api := context "api-reviewer" [apiToken] snapshot
  let correctness := context "correctness-reviewer" [correctnessToken] snapshot
  let mut state ← transition lead {} (.join .coordinator 300 coordToken false)
  for name in ["alice", "replacement", "api-reviewer", "correctness-reviewer"] do
    state ← transition (context name [] snapshot) state (.join .worker 300 ⟨"unused"⟩ false)
  if stage == 0 then return state
  state ← transition lead state (.plan feature "Implement a scoped feature" ["allowed"] [])
  state ← transition lead state (.assign feature alice.actor.agent .work false)
  state ← transition alice state (.start feature .work workToken)
  if stage == 1 then return state
  state ← transition alice state (.submit feature snapshot ["allowed/a.txt"] "Focused tests passed")
  if stage == 2 then return state
  state ← transition lead state (.assign feature api.actor.agent .api false)
  state ← transition api state (.start feature .api apiToken)
  state ← transition api state (.review feature .api snapshot .approve "Independent API review")
  state ← transition lead state (.assign feature correctness.actor.agent .correctness false)
  state ← transition correctness state (.start feature .correctness correctnessToken)
  state ← transition correctness state
    (.review feature .correctness snapshot .approve "Independent correctness review")
  if stage == 3 then return state
  transition lead state (.reserve feature integrationToken)

private def testProtocolFullFlow : IO Unit := do
  let lead := leadContext
  let submitted ← protocolState 2
  reject lead submitted (.reserve feature integrationToken) "missing both reviews"
  let approved ← protocolState 3
  let reserved ← transition lead approved (.reserve feature integrationToken)
  let retried ← transition lead reserved (.reserve feature integrationToken)
  check (retried == reserved) "Same pending integration generation was not idempotent"
  let outcome ← IO.ofExcept <| Coordination.apply lead reserved
    (.land feature exampleSnapshot "Validation complete")
  check (outcome.publication == .atomicLanding exampleSnapshot) "Land did not require atomic publication"
  check outcome.state.integration.isNone "Landing retained an integration lease"
  match (← epic outcome.state).phase with
  | .merged completed =>
    check (completed.api.reviewer.agent != completed.correctness.reviewer.agent)
      "Completion did not retain two independent reviewers"
    check (completed.snapshot == exampleSnapshot) "Completion changed reviewed snapshot"
    check (completed.validation == "Validation complete") "Completion dropped validation evidence"
  | _ => throw <| IO.userError "Land did not complete epic"
  reject lead outcome.state (.reopen feature "edit merged work") "reopening merged work"

private def testStaleWorkGeneration : IO Unit := do
  let state ← protocolState 1
  let old := context "alice" [workToken]
  let nextToken : Token := ⟨"next-work-generation"⟩
  let fresh := context "alice" [workToken, nextToken]
  let state ← transition fresh state (.start feature .work nextToken)
  reject old state (.note feature .work "stale report" false) "stale implementation generation"
  let current := context "alice" [nextToken]
  discard <| transition current state (.note feature .work "current report" false)
  let state ← transition {old with now := 1010} state .heartbeat
  match (← epic state).phase with
  | .working work =>
    check (work.lease.any (fun lease => lease.expires == 1300))
      "Stale heartbeat renewed another generation"
  | _ => throw <| IO.userError "Expected working epic"
  let state ← transition leadContext state (.assign feature ⟨"alice"⟩ .work true)
  reject current state (.note feature .work "revoked report" false) "explicitly revoked work claim"
  reject (context "alice" []) state (.start feature .work nextToken) "unpersisted pending token"

private def testStaleReviewsAndChangedHead : IO Unit := do
  let state ← protocolState 2
  let lead := leadContext
  let api := context "api-reviewer" [apiToken]
  let state ← transition lead state (.assign feature api.actor.agent .api false)
  let state ← transition api state (.start feature .api apiToken)
  let nextToken : Token := ⟨"next-api-generation"⟩
  let fresh := context "api-reviewer" [apiToken, nextToken]
  let state ← transition fresh state (.start feature .api nextToken)
  reject api state (.review feature .api exampleSnapshot .approve "old token") "stale review generation"
  let changed : Snapshot := {exampleSnapshot with head := ⟨"different-head"⟩}
  reject fresh state (.review feature .api changed .approve "different head") "changed reviewed head"
  let changedBase : Snapshot := {exampleSnapshot with base := ⟨"different-base"⟩}
  reject fresh state (.review feature .api changedBase .approve "different base") "changed reviewed base"
  reject {fresh with cleanHead := none} state
    (.review feature .api exampleSnapshot .approve "dirty reviewer") "reviewer must inspect clean exact head"
  let state ← transition lead state (.reopen feature "revision")
  reject fresh state (.review feature .api exampleSnapshot .approve "old snapshot") "review after reopen"
  reject lead state (.reserve feature integrationToken) "reopen revoked approvals"

private def testReviewRestartAndChangesRecovery : IO Unit := do
  let state ← protocolState 3
  let api := context "api-reviewer" [apiToken]
  let state ← transition api state (.start feature .api apiToken)
  match (← submission state).reviews.api with
  | .active _ _ _ => pure ()
  | _ => throw <| IO.userError "Restart retained a finished approval"
  reject leadContext state (.reserve feature integrationToken) "re-review must revoke old approval"
  let state ← transition api state (.review feature .api exampleSnapshot .changes "Changes requested")
  reject leadContext state (.reserve feature integrationToken) "requested changes"
  let state ← transition api state (.start feature .api apiToken)
  let state ← transition api state (.review feature .api exampleSnapshot .approve "Concern resolved")
  discard <| transition leadContext state (.reserve feature integrationToken)

private def testAuthorAndReviewerIndependence : IO Unit := do
  let state ← protocolState 1
  let lead := leadContext
  let replacement := context "replacement" [workToken]
  let state ← transition lead state (.assign feature replacement.actor.agent .work true)
  let state ← transition replacement state (.start feature .work workToken)
  let state ← transition replacement state
    (.submit feature exampleSnapshot ["allowed/a.txt"] "Both contributors credited")
  check ((← epic state).authors == [⟨"alice"⟩, ⟨"replacement"⟩]) "Prior author was discarded"
  for author in ["alice", "replacement"] do
    reject lead state (.assign feature ⟨author⟩ .api false) s!"author review: {author}"
  let state ← transition lead state (.assign feature ⟨"api-reviewer"⟩ .api false)
  reject lead state (.assign feature ⟨"api-reviewer"⟩ .correctness false) "same reviewer in both slots"
  let api := context "api-reviewer" [apiToken]
  let state ← transition api state (.start feature .api apiToken)
  reject (context "correctness-reviewer" [apiToken]) state
    (.review feature .api exampleSnapshot .approve "someone else's token") "wrong lease actor"

private def testScopeComponentsAndSubmissionEvidence : IO Unit := do
  let state ← protocolState 1
  let lead := leadContext
  let alice := context "alice" [workToken]
  let state ← transition lead state (.plan ⟨"nested"⟩ "nested" ["allowed/child"] [])
  reject lead state (.assign ⟨"nested"⟩ ⟨"replacement"⟩ .work false) "overlapping active scope"
  let state ← transition lead state (.plan ⟨"sibling"⟩ "sibling" ["allowedness"] [])
  discard <| transition lead state (.assign ⟨"sibling"⟩ ⟨"replacement"⟩ .work false)
  for path in ["outside.txt", "allowedness/file", " allowed/file", "\nallowed/file"] do
    reject alice state (.submit feature exampleSnapshot [path] "scope test") s!"outside path {repr path}"
  discard <| transition alice state (.submit feature exampleSnapshot
    ["allowed/a.txt", "Complexity.lean", "ComplexityTests.lean"] "Generated roots permitted")
  reject {alice with branchHead := some ⟨"unpushed-head"⟩} state
    (.submit feature exampleSnapshot ["allowed/a.txt"] "unpushed") "branch must match exact head"
  reject {alice with cleanHead := none} state
    (.submit feature exampleSnapshot ["allowed/a.txt"] "dirty") "clean worktree required"
  reject {alice with ancestry := []} state
    (.submit feature exampleSnapshot ["allowed/a.txt"] "not fast-forward") "explicit ancestry evidence"
  for invalid in ["../escape", "/absolute", ".git/config", ".lake/build", ".worktrees/a", ".", "a//b"] do
    reject lead state (.plan ⟨"invalid"⟩ "bad path" [invalid] []) s!"invalid scope {invalid}"

private def testPlanRevision : IO Unit := do
  let lead := leadContext
  let alice := context "alice" [workToken]
  let state ← protocolState 1
  let state ← transition alice state (.note feature .work "Useful theorem proved" false)
  let before ← epic state
  let revised ← transition lead state
    (.revise feature "First complete theorem milestone" ["tests", "tests"])
  check ((← epic revised) == {before with
      goal := "First complete theorem milestone", paths := ["allowed", "tests"]})
    "Revision changed work, authors, dependencies, reports or branch"
  check (revised.agents == state.agents && revised.coordinator == state.coordinator &&
      revised.integration == state.integration) "Revision changed unrelated authority"
  discard <| transition alice revised (.note feature .work "Continuing with the same claim" false)
  discard <| transition alice revised
    (.submit feature exampleSnapshot ["allowed/a.txt", "tests/feature.lean"] "Expanded scope")
  reject alice state (.revise feature "Worker changed own scope" ["outside"])
    "worker cannot revise scope"
  reject {lead with heldTokens := []} state (.revise feature "Missing generation" [])
    "coordinator generation required"
  reject {lead with now := 1301} state (.revise feature "Expired coordinator" [])
    "expired coordinator cannot revise"
  reject lead state (.revise feature "" []) "empty revised goal"
  for invalid in ["../escape", "/absolute", ".git/config", ".lake/build", ".worktrees/a", ".", "a//b"] do
    reject lead state (.revise feature "Invalid expansion" [invalid]) s!"invalid expansion {invalid}"
  let other : EpicId := ⟨"other"⟩
  let state ← transition lead state (.plan other "Other work" ["shared/subtree"] [])
  let state ← transition lead state (.assign other ⟨"replacement"⟩ .work false)
  for path in ["shared", "shared/subtree", "shared/subtree/child"] do
    reject lead state (.revise feature "Overlapping expansion" [path]) s!"overlap {path}"
  discard <| transition lead state (.revise feature "Sibling scope" ["shared/subtrees"])
  let pending : EpicId := ⟨"pending"⟩
  let state ← transition lead state (.plan pending "Future work" ["future"] [feature])
  let state ← transition lead state (.revise pending "Future milestone" ["shared"])
  let some planned := state.epics.find? (·.id == pending)
    | throw <| IO.userError "Missing pending epic"
  check (planned.dependencies == [feature] && planned.paths == ["future", "shared"])
    "Unassigned revision lost paths or dependencies"
  reject lead state (.assign pending ⟨"replacement"⟩ .work false)
    "Revising a future plan bypassed assignment overlap checks"
  let submitted ← protocolState 2
  reject lead submitted (.revise feature "Changed after review began" []) "submitted plan is frozen"
  let reserved ← protocolState 4
  reject lead reserved (.revise feature "Changed during integration" []) "reserved plan is frozen"
  let reopened ← transition lead reserved (.reopen feature "Review a changed contract")
  discard <| transition lead reopened (.revise feature "Reopened endpoint" [])
  let merged ← transition lead reserved (.land feature exampleSnapshot "Checks passed")
  reject lead merged (.revise feature "Rewrite completed history" []) "merged plan is immutable"

private def testCoordinatorGuidance : IO Unit := do
  let lead := leadContext
  for stage in [1, 2, 4] do
    let state ← protocolState stage
    let before ← epic state
    let message := "Reuse the shared lemma; report any missing scope"
    let instructed ← transition lead state (.instruct feature message)
    check ((← epic instructed) == {before with report := message})
      "Guidance changed the goal, paths, implementation, or reviews"
    check (instructed.agents == state.agents && instructed.coordinator == state.coordinator &&
        instructed.integration == state.integration) "Guidance changed authority or integration"
    check ((← transition lead instructed (.instruct feature message)) == instructed)
      "Retrying identical guidance changed state"
    reject (context "alice" [workToken]) state (.instruct feature "Impersonate coordinator")
      "worker cannot issue coordinator guidance"
    reject {lead with heldTokens := []} state (.instruct feature "No held generation")
      "guidance requires coordinator generation"
    reject {lead with now := 1301} state (.instruct feature "Expired coordinator")
      "expired coordinator cannot issue guidance"
    reject lead state (.instruct feature "") "empty guidance"
  let state ← protocolState 1
  let state ← transition lead state (.instruct feature "Coordinator direction")
  let state ← transition (context "alice" [workToken]) state
    (.note feature .work "Independent progress report" false)
  check ((← epic state).report == "Coordinator direction") "Worker report erased guidance"
  match (← epic state).phase with
  | .working work => check (work.report == "Independent progress report") "Worker report was lost"
  | _ => throw <| IO.userError "Guidance changed work phase"
  let reserved ← protocolState 4
  let merged ← transition lead reserved (.land feature exampleSnapshot "Checks passed")
  reject lead merged (.instruct feature "Rewrite completed history") "completed record is immutable"

private def testIntegrationAndSessionGenerations : IO Unit := do
  let state ← protocolState 4
  let lead := leadContext
  let state ← transition lead state .cancel
  let nextToken : Token := ⟨"next-integration-generation"⟩
  let fresh := {lead with heldTokens := [coordToken, nextToken]}
  let state ← transition fresh state (.reserve feature nextToken)
  reject lead state (.land feature exampleSnapshot "stale reservation") "stale integration generation"
  reject {fresh with main := some ⟨"new-main"⟩} state
    (.land feature exampleSnapshot "main moved") "stale main before publish"
  reject {fresh with cleanHead := none} state
    (.land feature exampleSnapshot "dirty candidate") "dirty publish"
  reject {fresh with now := 1301} state .heartbeat "expired session"
  let takeover := {context "alice" [] with
    actor := {agent := ⟨"alice"⟩, session := ⟨"replacement-session"⟩}, now := 1361}
  let state ← transition takeover state (.join .worker 300 ⟨"unused"⟩ true)
  reject {context "alice" [workToken] with now := 1361} state .heartbeat "replaced session"

private def testDependenciesAndConflictingStarts : IO Unit := do
  let state ← protocolState 0
  let lead := leadContext
  let alice := context "alice" [workToken]
  let state ← transition lead state (.plan ⟨"dependency"⟩ "prerequisite" ["dependency"] [])
  let state ← transition lead state (.plan feature "dependent" ["allowed"] [⟨"dependency"⟩])
  let state ← transition lead state (.assign feature alice.actor.agent .work false)
  reject alice state (.start feature .work workToken) "unlanded dependency"
  let working ← protocolState 1
  reject (context "replacement" [workToken]) working (.start feature .work workToken)
    "assignment belongs to another agent"
  reject (context "alice" [⟨"unrelated-generation"⟩]) working
    (.start feature .work ⟨"unrelated-generation"⟩) "unheld current assignment generation"
  let restarted ← transition alice working (.start feature .work workToken)
  check (restarted == working) "Retrying the same pending work generation was not idempotent"

/-- The real journal stores the same State ADT used by the pure protocol, including landing. -/
private def testProtocolThroughGit : IO Unit := withFixture fun fixture => do
  let repository ← fixture.open
  let head ← fixture.commit "allowed/a.txt" "candidate with actual protocol state\n"
  let snapshot : Snapshot := {base := ⟨fixture.base⟩, head := ⟨head⟩}
  let drive (ctx : Context) (command : Command) : IO State :=
    repository.update ({} : State) "protocol transition" (fun state => do
      let outcome ← IO.ofExcept <| Coordination.apply ctx state command
      let landing := match outcome.publication with
        | .boardOnly => none
        | .atomicLanding snap => some {base := snap.base.value, head := snap.head.value}
      pure (outcome.state, landing)) true
  let lead := leadContext snapshot
  let alice := context "alice" [workToken] snapshot
  let api := context "api-reviewer" [apiToken] snapshot
  let correctness := context "correctness-reviewer" [correctnessToken] snapshot
  discard <| drive lead (.join .coordinator 300 coordToken false)
  for person in [alice, api, correctness] do
    discard <| drive person (.join .worker 300 ⟨"unused"⟩ false)
  discard <| drive lead (.plan feature "End-to-end feature" ["allowed"] [])
  discard <| drive lead (.assign feature alice.actor.agent .work false)
  discard <| drive alice (.start feature .work workToken)
  discard <| drive lead (.instruct feature "Preserve the existing proof API")
  discard <| drive lead (.revise feature "Complete first milestone" ["tests"])
  let some (_, guidedJson) ← repository.readBoard | throw <| IO.userError "Missing revised board"
  let guidedState : State ← IO.ofExcept <| fromJson? guidedJson
  check ((← epic guidedState).report == "Preserve the existing proof API") "Guidance was not published"
  check ((← epic guidedState).goal == "Complete first milestone") "Revision was not published"
  discard <| drive alice (.note feature .work "Same claim still active" false)
  discard <| git fixture.repository #["push", "--quiet", "origin", "HEAD:refs/heads/work/feature/alice"]
  check ((← repository.fetch "refs/heads/work/feature/alice") == some head) "Pushed head mismatch"
  repository.clean head
  let changed ← repository.changedPaths fixture.base head
  discard <| drive alice (.submit feature snapshot changed "Real Git observations checked")
  expectError (drive lead (.reserve feature integrationToken)) "approval"
  discard <| drive lead (.assign feature api.actor.agent .api false)
  discard <| drive api (.start feature .api apiToken)
  discard <| drive api (.review feature .api snapshot .approve "Independent API evidence")
  expectError (drive lead (.reserve feature integrationToken)) "approval"
  discard <| drive lead (.assign feature correctness.actor.agent .correctness false)
  discard <| drive correctness (.start feature .correctness correctnessToken)
  discard <| drive correctness (.review feature .correctness snapshot .approve "Independent correctness evidence")
  discard <| drive lead (.reserve feature integrationToken)
  check ((← fixture.ref Git.mainRef) == fixture.base) "Reservation prematurely published main"
  let before ← fixture.ref Git.boardRef
  let landed ← drive lead (.land feature snapshot "Focused integration validation passed")
  check ((← fixture.ref Git.mainRef) == head) "Protocol did not atomically publish candidate"
  check ((← git fixture.origin #["rev-parse", Git.boardRef ++ "^"]) == before) "Landing journal parent changed"
  let some (_, json) ← repository.readBoard | throw <| IO.userError "Missing landed state"
  let remoteState : State ← IO.ofExcept <| fromJson? json
  check (remoteState == landed) "Remote protocol state differs from landed result"
  match (← epic remoteState).phase with
  | .merged _ => pure ()
  | _ => throw <| IO.userError "Remote protocol state is not merged"

private def protocolTests : List (String × IO Unit) := [
  ("protocol full flow requires two reviews and atomic completion", testProtocolFullFlow),
  ("stale work tokens and heartbeats do not revive revoked claims", testStaleWorkGeneration),
  ("stale review generations and replaced heads refused", testStaleReviewsAndChangedHead),
  ("review restart revokes approval and changes can be resolved", testReviewRestartAndChangesRecovery),
  ("self, former-author and same-agent reviews refused", testAuthorAndReviewerIndependence),
  ("scope components, unusual paths and exact submission evidence", testScopeComponentsAndSubmissionEvidence),
  ("plan revisions preserve claims and fence scope and review changes", testPlanRevision),
  ("coordinator guidance preserves work, reviews and integration", testCoordinatorGuidance),
  ("integration, expiry and session replacement fence old authority", testIntegrationAndSessionGenerations),
  ("dependencies, conflicting starts and idempotent claim retry", testDependenciesAndConflictingStarts),
  ("actual protocol state flows through local Git to atomic publish", testProtocolThroughGit)]

private def gitTests : List (String × IO Unit) := [
  ("journal round-trip, no-op, optional fetch and temporary refs", testJournalAndFetch),
  ("raw whitespace/NUL paths and both rename endpoints", testRawPathsAndRename),
  ("caller index, FETCH_HEAD, HEAD and dirty files preserved", testCallerPreservation),
  ("clean and dirty preflight preserve index bytes", testCleanPreservesIndex),
  ("atomic main and journal landing", testAtomicLanding),
  ("exact-base guard rejects an ancestor main race atomically", testAncestorRace),
  ("backward landing refused", testNonFastForwardRefused),
  ("disjoint journal conflict rechecks and preserves both writes", testDisjointBoardConflict),
  ("same assignment conflict has one winner", testSameAssignmentConflict),
  ("lost ordinary and atomic push acknowledgements reconciled", testLostAcknowledgements),
  ("accepted claim plus failed verification read can be retried", testAmbiguousAcceptanceRetry),
  ("unrelated coordination branch refused without overwrite", testMalformedBoardRefused)]

end Coordination.Tests

open Coordination.Tests in

private def runTests : IO UInt32 := do
  let mut failed := 0
  let tests := protocolTests ++ gitTests ++ runtimeTests
  for (name, action) in tests do
    try
      action
      IO.println s!"PASS {name}"
    catch error =>
      failed := failed + 1
      IO.eprintln s!"FAIL {name}: {error}"
  IO.println s!"{tests.length - failed}/{tests.length} coordinator tests passed"
  pure (if failed == 0 then 0 else 1)

/-- Re-execute once so production subprocesses also inherit private Git configuration. -/
def main (args : List String) : IO UInt32 := do
  if args == ["--isolated-git"] then
    runTests
  else if args.isEmpty then
    let child ← IO.Process.spawn {
      cmd := (← IO.appPath).toString
      args := #["--isolated-git"]
      env := #[("GIT_CONFIG_GLOBAL", some "/dev/null"), ("GIT_CONFIG_NOSYSTEM", some "1"),
        ("GIT_TERMINAL_PROMPT", some "0"), ("GIT_CONFIG_COUNT", none),
        ("GIT_CONFIG_PARAMETERS", none)]
    }
    child.wait
  else
    IO.eprintln "Run coordinateTests without arguments"
    pure 1
