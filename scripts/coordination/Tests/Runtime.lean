/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (repository coordination tests)
import Coordination.Runtime
import Tests.Support

/-! Runtime regressions use real linked worktrees and private local origins. Expiry is set
explicitly in the fixture's journal instead of waiting for a wall-clock lease to elapse. -/

namespace Coordination.Tests

open Lean

private def initState (repository : Git.Repository) : IO Unit := do
  discard <| repository.update ({} : State) "initialize runtime tests"
    (fun state => pure (state, none)) true

private def joined (primary : Git.Repository) (name : String) (role := Role.worker) :
    IO Git.Repository := do
  let path ← Runtime.join primary ⟨name⟩ role false false 300
  Git.Repository.open path

private def linked (fixture : Fixture) (name := "pending-worker") : IO Git.Repository := do
  let path := fixture.directory / name
  discard <| git fixture.repository #["worktree", "add", "--detach", path.toString, fixture.base]
  Git.Repository.open path

private def commitAt (repository : Git.Repository) (text : String) : IO String := do
  IO.FS.writeFile (repository.root / "allowed/a.txt") text
  discard <| repository.run #["add", "allowed/a.txt"]
  discard <| repository.run #["commit", "--quiet", "-m", "worker contribution"]
  repository.head

private def pushWork (repository : Git.Repository) (branch : String) : IO Unit := do
  discard <| repository.run #["push", "--quiet", "origin", "HEAD:refs/heads/" ++ branch]

/-- Server acceptance succeeds, but the reply and the first reconciliation read are lost. -/
private def ambiguousRunner (repository : Git.Repository)
    (beforePush : IO Unit := pure ()) : IO Git.Repository := do
  let accepted ← IO.mkRef false
  let readFailed ← IO.mkRef false
  pure {repository with execute := fun args input => do
    if args[0]? == some "ls-remote" && (← accepted.get) && !(← readFailed.get) then
      readFailed.set true
      throw <| IO.userError "injected unavailable reconciliation read"
    if args[0]? == some "push" && !(← accepted.get) then beforePush
    let result ← repository.execute args input
    if args[0]? == some "push" && result.exitCode == 0 && !(← accepted.get) then
      accepted.set true
      pure {result with exitCode := 1, stderr := "accepted push response lost"}
    else pure result }

private def testJoinPreservesPrimary : IO Unit := withFixture fun fixture => do
  let renamed := fixture.directory / "caller\nprimary"
  IO.FS.rename fixture.repository renamed
  let fixture := {fixture with repository := renamed}
  let primary ← fixture.open
  initState primary
  discard <| git fixture.repository #["fetch", "--quiet", "origin", "main"]
  IO.FS.writeFile (fixture.repository / "allowed/a.txt") "staged primary\n"
  discard <| git fixture.repository #["add", "allowed/a.txt"]
  IO.FS.writeFile (fixture.repository / "allowed/a.txt") "staged plus dirty primary\n"
  IO.FS.writeFile (fixture.repository / "primary-untracked.txt") "keep me\n"
  let gitdir := System.FilePath.mk (← git fixture.repository #["rev-parse", "--absolute-git-dir"])
  let index ← IO.FS.readBinFile (gitdir / "index")
  let fetchHead ← IO.FS.readBinFile (gitdir / "FETCH_HEAD")
  let branch ← primary.run #["symbolic-ref", "HEAD"]
  let worker ← joined primary "alice"
  check (worker.root != primary.root) "Join reused the dirty primary checkout"
  let identity ← Runtime.identity worker
  check (identity.actor.agent == ⟨"alice"⟩) "Wrong worker identity"
  check ((← primary.head) == fixture.base) "Join changed primary HEAD"
  check ((← primary.run #["symbolic-ref", "HEAD"]) == branch) "Join changed primary branch"
  check ((← IO.FS.readBinFile (gitdir / "index")) == index) "Join changed primary index"
  check ((← IO.FS.readBinFile (gitdir / "FETCH_HEAD")) == fetchHead) "Join changed primary FETCH_HEAD"
  check ((← IO.FS.readFile (fixture.repository / "allowed/a.txt")) == "staged plus dirty primary\n")
    "Join changed primary dirty file"
  check ((← IO.FS.readFile (fixture.repository / "primary-untracked.txt")) == "keep me\n")
    "Join changed primary untracked file"
  check ((← worker.head) == fixture.base) "New worker did not start at main"

private def testInvalidJoinDurationLeavesNoCandidate : IO Unit := withFixture fun fixture => do
  let primary ← fixture.open
  initState primary
  expectError (Runtime.join primary ⟨"alice"⟩ .worker false false 60) "300"
  let destination := primary.root / ".worktrees" / "alice"
  check (!(← destination.pathExists)) "Invalid duration left a worker directory or pending identity"
  let worker ← joined primary "alice"
  check ((← Runtime.identity worker).leaseSeconds == 300) "Corrected duration could not join"

private def testRejectedTakeoverPreservesIdentity : IO Unit := withFixture fun fixture => do
  let primary ← fixture.open
  initState primary
  let worker ← joined primary "alice"
  let path ← Runtime.identityPath worker
  let before ← IO.FS.readBinFile path
  let original ← Runtime.identity worker
  expectError (Runtime.join worker ⟨"alice"⟩ .worker true true 300) "Agent name is in use"
  check ((← IO.FS.readBinFile path) == before) "Rejected takeover overwrote live identity"
  check ((← Runtime.identity worker).actor == original.actor) "Rejected takeover replaced local actor"
  discard <| Runtime.run worker .heartbeat

private def testPendingJoinRecovery : IO Unit := withFixture fun fixture => do
  let primary ← fixture.open
  initState primary
  let worker ← linked fixture
  let path ← Runtime.identityPath worker
  let pending := System.FilePath.mk (path.toString ++ ".pending")
  let unreliable ← ambiguousRunner worker
  expectError (Runtime.join unreliable ⟨"alice"⟩ .worker true false 300) "reconciliation read"
  check (!(← path.pathExists)) "Ambiguous first join finalized identity before verification"
  check (← pending.pathExists) "Ambiguous first join lost durable candidate"
  let candidate : Runtime.Identity ← Runtime.readJson pending
  let state ← Runtime.readState worker
  check (state.agents.any (fun agent => agent.actor == candidate.actor)) "Join was not accepted remotely"
  let before ← fixture.ref Git.boardRef
  discard <| Runtime.join worker ⟨"alice"⟩ .worker true false 300
  check ((← Runtime.identity worker).actor == candidate.actor) "Retry did not recover accepted candidate"
  check (!(← pending.pathExists)) "Successful retry retained pending join"
  check ((← fixture.ref Git.boardRef) == before) "Accepted join retry created a replacement session"

private def testExpiredPendingJoinRotatesIdentity : IO Unit := withFixture fun fixture => do
  let primary ← fixture.open
  initState primary
  let worker ← linked fixture
  let unreliable ← ambiguousRunner worker
  expectError (Runtime.join unreliable ⟨"alice"⟩ .worker true false 300) "reconciliation read"
  let path ← Runtime.identityPath worker
  let pending := System.FilePath.mk (path.toString ++ ".pending")
  let candidate : Runtime.Identity ← Runtime.readJson pending
  -- A different session took over remotely while the first caller was offline, then expired.
  let replacement : Actor := {agent := ⟨"alice"⟩, session := ⟨"intervening-session"⟩}
  discard <| worker.update ({} : State) "expired intervening session" fun state =>
    pure ({state with agents := state.agents.map fun agent =>
      if agent.actor.agent == ⟨"alice"⟩ then {agent with actor := replacement, expires := 0}
      else agent}, none)
  discard <| Runtime.join worker ⟨"alice"⟩ .worker true true 300
  let recovered ← Runtime.identity worker
  check (recovered.actor != candidate.actor && recovered.actor != replacement)
    "Expired pending takeover reused an old session"
  check (recovered.tokens.all (fun token => !candidate.tokens.contains token))
    "Expired pending takeover reused an old generation token"
  check (!(← pending.pathExists)) "Expired pending takeover left stale pending file"
  expectError (Runtime.dispatch worker candidate .heartbeat) "Session was replaced"
  discard <| Runtime.run worker .heartbeat

private def testDurableWorkClaimRecovery : IO Unit := withFixture fun fixture => do
  let primary ← fixture.open
  initState primary
  let lead ← joined primary "lead" .coordinator
  let worker ← joined primary "alice"
  let id : EpicId := ⟨"feature"⟩
  discard <| Runtime.run lead (.plan id "durable claim" ["allowed"] [])
  discard <| Runtime.run lead (.assign id ⟨"alice"⟩ .work false)
  let durable ← IO.mkRef (none : Option Token)
  let unreliable ← ambiguousRunner worker do
    let persisted ← Runtime.identity worker
    let some pending := persisted.pending.head? | throw <| IO.userError "Claim not saved before push"
    durable.set (some pending.token)
  expectError (Runtime.start unreliable id .work) "reconciliation read"
  let self ← Runtime.identity worker
  let some token := (← durable.get) | throw <| IO.userError "Durability hook did not run"
  check (self.pending.any (fun claim => claim.token == token)) "Ambiguous work claim lost pending token"
  let state ← Runtime.readState worker
  match (← Runtime.getEpic state id).phase with
  | .working work => check (work.lease.any (fun lease => lease.token == token)) "Remote lease token differs"
  | _ => throw <| IO.userError "Accepted work claim missing"
  discard <| Runtime.start worker id .work
  let self ← Runtime.identity worker
  check self.pending.isEmpty "Recovered work claim remains pending"
  check (self.tokens.contains token) "Recovered work claim was not finalized"
  match (← Runtime.getEpic (← Runtime.readState worker) id).phase with
  | .working work =>
    check (work.lease.any (fun lease => lease.token == token && lease.holder == self.actor))
      "Retry replaced accepted work generation"
  | _ => throw <| IO.userError "Recovered implementation phase missing"
  check ((Git.line (← worker.run #["symbolic-ref", "HEAD"])) == "refs/heads/work/feature/alice")
    "Recovered work claim did not finish checkout"

private def testLocalLockSerializesIdentityMutation : IO Unit := withFixture fun fixture => do
  let primary ← fixture.open
  initState primary
  let worker ← joined primary "alice"
  let entered ← IO.Promise.new (α := Unit)
  let release ← IO.Promise.new (α := Unit)
  let held ← IO.asTask (prio := .dedicated) <| Runtime.withLock worker do
    entered.resolve ()
    check release.result?.get.isSome "Lock release promise was dropped"
    let (_, token) ← Runtime.claim worker "first"
    Runtime.finishClaim worker "first" token
    pure token
  check entered.result?.get.isSome "Lock holder did not start"
  try
    expectError (Runtime.withLock worker (Runtime.claim worker "second")) "Another command holds"
  finally
    release.resolve ()
  let first ← IO.ofExcept held.get
  let second ← Runtime.withLock worker do
    let (_, token) ← Runtime.claim worker "second"
    Runtime.finishClaim worker "second" token
    pure token
  let self ← Runtime.identity worker
  check (self.tokens.contains first && self.tokens.contains second && first != second)
    "Serialized identity updates lost a claim"
  check self.pending.isEmpty "Serialized successful claims remain pending"
  -- An exception in the critical section must also release the local lock.
  expectError (Runtime.withLock worker (throw <| IO.userError "intentional failure" : IO Unit))
    "intentional failure"
  Runtime.withLock worker (pure ())

private def testAlternatingAuthorsPreservePushedWork : IO Unit := withFixture fun fixture => do
  let primary ← fixture.open
  initState primary
  let lead ← joined primary "lead" .coordinator
  let alice ← joined primary "alice"
  let bob ← joined primary "bob"
  let id : EpicId := ⟨"feature"⟩
  discard <| Runtime.run lead (.plan id "handoff" ["allowed"] [])
  discard <| Runtime.run lead (.assign id ⟨"alice"⟩ .work false)
  discard <| Runtime.start alice id .work
  let first ← commitAt alice "Alice contribution\n"
  pushWork alice "work/feature/alice"
  discard <| Runtime.run lead (.assign id ⟨"bob"⟩ .work true)
  discard <| Runtime.start bob id .work
  check ((← bob.head) == first) "B did not start from A's pushed contribution"
  let second ← commitAt bob "Alice plus Bob contribution\n"
  pushWork bob "work/feature/bob"
  discard <| Runtime.run lead (.assign id ⟨"alice"⟩ .work true)
  expectError (Runtime.start alice id .work) "omits"
  check ((← alice.head) == first) "Failed handoff silently reset A's existing branch"
  check (← bob.ancestor first second) "B's contribution does not extend A's"
  let tip ← Runtime.requiredRef alice "refs/heads/work/feature/bob"
  discard <| alice.run #["merge", "--quiet", "--ff-only", tip]
  discard <| Runtime.start alice id .work
  check ((← alice.head) == second) "Restart after explicit merge omitted B's contribution"
  let state ← Runtime.readState alice
  check ((← Runtime.getEpic state id).authors == [⟨"alice"⟩, ⟨"bob"⟩]) "Handoff lost prior authors"
  -- A fresh clone has no local A branch, but origin's A branch still predates B.
  let freshPrimary := fixture.directory / "fresh-clone"
  let freshPath := fixture.directory / "fresh-worker"
  discard <| git fixture.directory #["clone", "--quiet", fixture.origin.toString, freshPrimary.toString]
  configure freshPrimary
  discard <| git freshPrimary #["worktree", "add", "--detach", freshPath.toString, fixture.base]
  let fresh ← Git.Repository.open freshPath
  Runtime.writeJson (← Runtime.identityPath fresh) (← Runtime.identity alice)
  expectError (Runtime.start fresh id .work) "omits"
  check ((← fresh.head) == fixture.base) "Remote-only stale branch was checked out despite missing B"
  let absent ← fresh.execute #["show-ref", "--verify", "--quiet", "refs/heads/work/feature/alice"] none
  check (absent.exitCode != 0) "Failed remote-only handoff created a stale local branch"

private def approvedRuntime (fixture : Fixture) : IO (Git.Repository × EpicId × Snapshot) := do
  let primary ← fixture.open
  initState primary
  let lead ← joined primary "lead" .coordinator
  let alice ← joined primary "alice"
  let api ← joined primary "api-reviewer"
  let correctness ← joined primary "correctness-reviewer"
  let id : EpicId := ⟨"feature"⟩
  discard <| Runtime.run lead (.plan id "validation retry" ["allowed"] [])
  discard <| Runtime.run lead (.assign id ⟨"alice"⟩ .work false)
  discard <| Runtime.start alice id .work
  let head ← commitAt alice "validated runtime candidate\n"
  pushWork alice "work/feature/alice"
  discard <| Runtime.ready alice id "Focused runtime checks"
  let snapshot : Snapshot := {base := ⟨fixture.base⟩, head := ⟨head⟩}
  discard <| Runtime.run lead (.assign id ⟨"api-reviewer"⟩ .api false)
  discard <| Runtime.start api id .api
  discard <| Runtime.run api (.review id .api snapshot .approve "Independent API review")
  discard <| Runtime.run lead (.assign id ⟨"correctness-reviewer"⟩ .correctness false)
  discard <| Runtime.start correctness id .correctness
  discard <| Runtime.run correctness (.review id .correctness snapshot .approve "Independent correctness review")
  pure (lead, id, snapshot)

private def testReservationSurvivesValidationFailure : IO Unit := withFixture fun fixture => do
  let (lead, id, snapshot) ← approvedRuntime fixture
  let (self, original) ← Runtime.claim lead "integration"
  let reserved ← Runtime.dispatch lead self (.reserve id original)
  Runtime.finishClaim lead "integration" original
  let submitted ← Runtime.submission reserved.state id
  Runtime.checkout lead (.review submitted.work.branch snapshot)
  expectError (Runtime.validate lead "false" #[]) "failed; no code was published"
  check ((← fixture.ref Git.mainRef) == fixture.base) "Failed validation published main"
  let before ← fixture.ref Git.boardRef
  let (self, retry) ← Runtime.claim lead "integration"
  check (retry != original) "Retry did not exercise a new pending token"
  let recovered ← Runtime.dispatch lead self (.reserve id retry)
  Runtime.finishClaim lead "integration" retry
  check (recovered.state.integration.any (fun integration => integration.lease.token == original))
    "Same-owner reservation retry replaced or lost original lease"
  check ((← fixture.ref Git.boardRef) == before) "Reservation continuation changed accepted lease"
  Runtime.validate lead "true" #[]
  discard <| Runtime.run lead (.land id snapshot "Focused runtime validation passed")
  check ((← fixture.ref Git.mainRef) == snapshot.head.value) "Recovered integration did not publish"
  match (← Runtime.getEpic (← Runtime.readState lead) id).phase with
  | .merged _ => pure ()
  | _ => throw <| IO.userError "Recovered integration did not complete journal"

/-- Runtime coverage is intentionally separate from pure transition and transport tests. -/
def runtimeTests : List (String × IO Unit) := [
  ("runtime join creates linked worktree without changing dirty primary", testJoinPreservesPrimary),
  ("runtime invalid join duration leaves no candidate and corrected retry works", testInvalidJoinDurationLeavesNoCandidate),
  ("runtime rejected takeover preserves old identity and authority", testRejectedTakeoverPreservesIdentity),
  ("runtime accepted pending join recovers after lost reply and failed read", testPendingJoinRecovery),
  ("runtime expired replaced pending join rotates fresh identity and token", testExpiredPendingJoinRotatesIdentity),
  ("runtime claim is durable before push and recovers its accepted generation", testDurableWorkClaimRecovery),
  ("runtime worktree lock rejects overlapping mutations and preserves claims", testLocalLockSerializesIdentityMutation),
  ("runtime A-B-A checkout refuses to omit B's pushed contribution", testAlternatingAuthorsPreservePushedWork),
  ("runtime validation failure permits reservation retry with new pending token", testReservationSurvivesValidationFailure)]

end Coordination.Tests
