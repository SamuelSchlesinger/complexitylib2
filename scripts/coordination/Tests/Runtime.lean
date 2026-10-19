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

private structure Crew where
  primary : Git.Repository
  lead : Git.Repository
  api : Git.Repository
  correctness : Git.Repository

private def crew (fixture : Fixture) : IO Crew := do
  let primary ← fixture.open
  initState primary
  let lead ← joined primary "lead" .coordinator
  let api ← joined primary "api-reviewer"
  let correctness ← joined primary "correctness-reviewer"
  pure { primary, lead, api, correctness }

/-- Plan `id` on `scope`, then implement it as `worker` with `commit` and push the branch. -/
private def implement (crew : Crew) (id : EpicId) (scope worker : String)
    (commit : Git.Repository → IO String) : IO Git.Repository := do
  let repo ← joined crew.primary worker
  discard <| Runtime.run crew.lead (.plan id s!"validation of {id.value}" [scope] [])
  discard <| Runtime.run crew.lead (.assign id ⟨worker⟩ .work false)
  discard <| Runtime.start repo id .work
  discard <| commit repo
  pushWork repo s!"work/{id.value}/{worker}"
  pure repo

/-- Submit the worker's head and approve it with both independent reviews. -/
private def approve (crew : Crew) (id : EpicId) (worker : Git.Repository) : IO Snapshot := do
  let submitted ← Runtime.ready worker id "Focused runtime checks"
  let snapshot := (← Runtime.submission submitted.state id).snapshot
  discard <| Runtime.run crew.lead (.assign id ⟨"api-reviewer"⟩ .api false)
  discard <| Runtime.start crew.api id .api
  discard <| Runtime.run crew.api (.review id .api snapshot .approve "Independent API review")
  discard <| Runtime.run crew.lead (.assign id ⟨"correctness-reviewer"⟩ .correctness false)
  discard <| Runtime.start crew.correctness id .correctness
  discard <| Runtime.run crew.correctness
    (.review id .correctness snapshot .approve "Independent correctness review")
  pure snapshot

private def approvedRuntime (fixture : Fixture) : IO (Git.Repository × EpicId × Snapshot) := do
  let crew ← crew fixture
  let id : EpicId := ⟨"feature"⟩
  let alice ← implement crew id "allowed" "alice" (commitAt · "validated runtime candidate\n")
  let snapshot ← approve crew id alice
  check (snapshot == {base := ⟨fixture.base⟩, head := ⟨← alice.head⟩}) "Unexpected reviewed snapshot"
  pure (crew.lead, id, snapshot)

/-- Stand-in for `lake exe mk_all`: the root lists every file under `allowed` and `other`. -/
private def regenerate (repo : Git.Repository) : IO Unit := do
  let mut imports := ""
  for directory in ["allowed", "other"] do
    if ← (repo.root / directory).isDir then
      let entries := (← (repo.root / directory).readDir).qsort (·.fileName < ·.fileName)
      for entry in entries do
        imports := imports ++ s!"import {directory}/{entry.fileName}\n"
  IO.FS.writeFile (repo.root / "Complexity.lean") imports

/-- Add `path` and regenerate the root, as a worker running `mk_all` would. -/
private def addFile (repo : Git.Repository) (path : String) : IO String := do
  let target := repo.root / path
  if let some parent := target.parent then IO.FS.createDirAll parent
  IO.FS.writeFile target s!"{path}\n"
  regenerate repo
  discard <| repo.run #["add", "--", path, "Complexity.lean"]
  discard <| repo.run #["commit", "--quiet", "-m", s!"add {path}"]
  repo.head

/-- Advance origin's `main` from the primary checkout. -/
private def moveMain (crew : Crew) (path : String) : IO String := do
  let moved ← addFile crew.primary path
  discard <| crew.primary.run #["push", "--quiet", "origin", "HEAD:" ++ Git.mainRef]
  pure moved

private def stubChecks (_ : Git.Repository) : IO String := pure "Focused runtime validation passed"

private def landedCommit (state : State) (id : EpicId) : IO (Option Oid) := do
  match (← Runtime.getEpic state id).phase with
  | Phase.merged completed => pure completed.landed
  | _ => throw <| IO.userError s!"{id.value} was not merged"

private def testLandingFastForwardsCurrentBase : IO Unit := withFixture fun fixture => do
  let (lead, id, snapshot) ← approvedRuntime fixture
  let outcome ← Runtime.land lead [id] stubChecks regenerate
  check ((← fixture.ref Git.mainRef) == snapshot.head.value)
    "Landing on the reviewed base did not fast-forward to the reviewed head"
  check ((← lead.head) == snapshot.head.value) "Coordinator worktree is not at the reviewed head"
  check ((← landedCommit outcome.state id) == some snapshot.head)
    "Fast-forward did not record the reviewed head as landed"

private def testLandingMergesDisjointMainMove : IO Unit := withFixture fun fixture => do
  let crew ← crew fixture
  let id : EpicId := ⟨"feature"⟩
  let alice ← implement crew id "allowed" "alice" (addFile · "allowed/c.txt")
  let snapshot ← approve crew id alice
  check (snapshot.base.value == fixture.base) "Reviewed base is not the main the branch forked from"
  let moved ← moveMain crew "allowed/b.txt"
  let outcome ← Runtime.land crew.lead [id] stubChecks regenerate
  let landed ← fixture.ref Git.mainRef
  check ((← git fixture.origin #["rev-list", "--parents", "-n", "1", landed]) ==
    s!"{landed} {moved} {snapshot.head.value}") "Main is not a merge of the moved main and the reviewed head"
  check ((← git fixture.origin #["show", landed ++ ":Complexity.lean"]) ==
    "import allowed/a.txt\nimport allowed/b.txt\nimport allowed/c.txt")
    "Roots were not regenerated on the merged tree"
  let files := (← git fixture.origin #["ls-tree", "-r", "--name-only", landed]).splitOn "\n"
  check (files.contains "allowed/b.txt" && files.contains "allowed/c.txt") "Merged tree lost a change"
  let message ← git fixture.origin #["log", "-1", "--format=%B", landed]
  check (message.startsWith "merge: land feature" && (message.splitOn snapshot.head.value).length == 2 &&
    (message.splitOn fixture.base).length == 2) "Merge message does not name the epic and its reviewed snapshot"
  check ((← crew.lead.head) == landed) "Coordinator worktree is not at the landed commit"
  check outcome.state.integration.isNone "Landing retained the reservation"
  check ((← landedCommit outcome.state id) == some ⟨landed⟩) "Completion did not record the merge commit"
  match (← Runtime.getEpic outcome.state id).phase with
  | Phase.merged completed => check (completed.snapshot == snapshot) "Completion changed the reviewed snapshot"
  | _ => throw <| IO.userError "Merge landing did not complete the epic"

private def testLandingRefusesOverlappingMainMove : IO Unit := withFixture fun fixture => do
  let crew ← crew fixture
  let id : EpicId := ⟨"feature"⟩
  let alice ← implement crew id "allowed" "alice" (commitAt · "reviewed change\n")
  discard <| approve crew id alice
  let moved ← moveMain crew "allowed/a.txt"
  let before ← fixture.ref Git.boardRef
  expectError (Runtime.land crew.lead [id] stubChecks regenerate) "Main moved on reviewed files"
  check ((← fixture.ref Git.mainRef) == moved) "Refused landing changed main"
  check ((← fixture.ref Git.boardRef) == before) "Refused reservation changed the board"
  check (← Runtime.readState crew.lead).integration.isNone "Refused reservation was recorded"

private def testLandingRefusesTextualConflict : IO Unit := withFixture fun fixture => do
  let crew ← crew fixture
  let id : EpicId := ⟨"feature"⟩
  -- Disjoint paths can still conflict: main adds a file where the epic created a directory.
  let alice ← implement crew id "allowed" "alice" (addFile · "allowed/x/y.txt")
  discard <| approve crew id alice
  let moved ← moveMain crew "allowed/x"
  expectError (Runtime.land crew.lead [id] stubChecks regenerate) "conflicts"
  check ((← fixture.ref Git.mainRef) == moved) "Refused landing changed main"
  check ((← crew.lead.run #["--no-optional-locks", "status", "--porcelain"]).isEmpty)
    "Refused merge left the coordinator worktree dirty"
  let inProgress ← crew.lead.execute #["rev-parse", "-q", "--verify", "MERGE_HEAD"] none
  check (inProgress.exitCode != 0) "Refused merge was left in progress"
  -- As after a failed validation, the reservation remains until it is cancelled.
  check (← Runtime.readState crew.lead).integration.isSome "Refused merge released the reservation"
  discard <| Runtime.run crew.lead .cancel

private def testLandingBatchesDisjointEpics : IO Unit := withFixture fun fixture => do
  let crew ← crew fixture
  let first : EpicId := ⟨"feature"⟩
  let second : EpicId := ⟨"second"⟩
  let alice ← implement crew first "allowed" "alice" (addFile · "allowed/c.txt")
  let bob ← implement crew second "other" "bob" (addFile · "other/d.txt")
  let firstSnapshot ← approve crew first alice
  let secondSnapshot ← approve crew second bob
  let moved ← moveMain crew "allowed/b.txt"
  let outcome ← Runtime.land crew.lead [first, second] stubChecks regenerate
  let landed ← fixture.ref Git.mainRef
  let parents ← git fixture.origin #["rev-list", "--parents", "-n", "1", landed]
  let some firstMerge := (parents.splitOn " ")[1]? | throw <| IO.userError "Missing first parent"
  check (parents == s!"{landed} {firstMerge} {secondSnapshot.head.value}")
    "Final main is not a merge of the second reviewed head"
  check ((← git fixture.origin #["rev-list", "--parents", "-n", "1", firstMerge]) ==
    s!"{firstMerge} {moved} {firstSnapshot.head.value}") "First merge does not chain on the moved main"
  check ((← git fixture.origin #["show", landed ++ ":Complexity.lean"]) ==
    "import allowed/a.txt\nimport allowed/b.txt\nimport allowed/c.txt\nimport other/d.txt")
    "Roots were not regenerated on the final tree"
  check ((← git fixture.origin #["show", firstMerge ++ ":Complexity.lean"]) ==
    "import allowed/a.txt\nimport allowed/b.txt\nimport allowed/c.txt")
    "Intermediate merge has inconsistent roots"
  for id in [first, second] do
    check ((← landedCommit outcome.state id) == some ⟨landed⟩) s!"{id.value} did not record the landed main"

private def testLandingRefusesOverlappingBatch : IO Unit := withFixture fun fixture => do
  let crew ← crew fixture
  let first : EpicId := ⟨"feature"⟩
  let second : EpicId := ⟨"second"⟩
  let alice ← implement crew first "allowed" "alice" (addFile · "allowed/c.txt")
  let bob ← implement crew second "other" "bob" (addFile · "allowed/c.txt")
  let firstSnapshot ← approve crew first alice
  -- Assignment fences overlapping scopes, so the last line of defence is exercised by widening
  -- the second scope on the board directly.
  discard <| crew.lead.update ({} : State) "fixture widens a scope" fun state =>
    pure ({state with epics := state.epics.map fun e =>
      if e.id == second then {e with paths := ["other", "allowed"]} else e}, none)
  discard <| approve crew second bob
  let before ← fixture.ref Git.boardRef
  expectError (Runtime.land crew.lead [first, second] stubChecks regenerate) "both change allowed/c.txt"
  check ((← fixture.ref Git.mainRef) == fixture.base) "Refused batch changed main"
  check ((← fixture.ref Git.boardRef) == before) "Refused batch changed the board"
  discard <| Runtime.land crew.lead [first] stubChecks regenerate
  check ((← fixture.ref Git.mainRef) == firstSnapshot.head.value) "First epic could not land alone"
  expectError (Runtime.land crew.lead [second] stubChecks regenerate) "Main moved on reviewed files"

private def testReservationSurvivesValidationFailure : IO Unit := withFixture fun fixture => do
  let (lead, id, snapshot) ← approvedRuntime fixture
  let (self, original) ← Runtime.claim lead "integration"
  let reserved ← Runtime.dispatch lead self (.reserve [id] original)
  Runtime.finishClaim lead "integration" original
  let submitted ← Runtime.submission reserved.state id
  Runtime.checkout lead (.review submitted.work.branch snapshot)
  expectError (Runtime.validate lead "false" #[]) "failed; no code was published"
  check ((← fixture.ref Git.mainRef) == fixture.base) "Failed validation published main"
  let before ← fixture.ref Git.boardRef
  let (self, retry) ← Runtime.claim lead "integration"
  check (retry != original) "Retry did not exercise a new pending token"
  let recovered ← Runtime.dispatch lead self (.reserve [id] retry)
  Runtime.finishClaim lead "integration" retry
  check (recovered.state.integration.any (fun integration => integration.lease.token == original))
    "Same-owner reservation retry replaced or lost original lease"
  check ((← fixture.ref Git.boardRef) == before) "Reservation continuation changed accepted lease"
  Runtime.validate lead "true" #[]
  discard <| Runtime.run lead (.land [{ epic := id, snapshot }] snapshot.head "Focused runtime validation passed")
  check ((← fixture.ref Git.mainRef) == snapshot.head.value) "Recovered integration did not publish"
  match (← Runtime.getEpic (← Runtime.readState lead) id).phase with
  | .merged _ => pure ()
  | _ => throw <| IO.userError "Recovered integration did not complete journal"

private def testCoordinatorHandoff : IO Unit := withFixture fun fixture => do
  let (lead, id, snapshot) ← approvedRuntime fixture
  let before ← Runtime.readState lead
  let identity ← Runtime.identity lead
  IO.FS.writeFile (lead.root / "handoff-untracked.txt") "unfinished integration\n"
  expectError (Runtime.releaseCoordinator lead) "clean"
  check ((← Runtime.readState lead) == before) "Dirty handoff changed remote board"
  IO.FS.removeFile (lead.root / "handoff-untracked.txt")
  let released ← Runtime.releaseCoordinator lead
  check released.state.coordinator.isNone "Release did not publish vacant coordinator"
  check (released.state.epics == before.epics) "Release lost submitted work or approvals"
  let primary ← fixture.open
  let successor ← joined primary "successor" .coordinator
  check (successor.root != lead.root) "Successor reused outgoing worktree"
  check ((← Runtime.identity successor).actor != identity.actor) "Successor copied old identity"
  expectError (Runtime.run lead (.instruct id "stale instruction")) "generation"
  discard <| Runtime.run lead .heartbeat
  expectError (Runtime.releaseCoordinator lead) "generation"
  let (self, token) ← Runtime.claim successor "integration"
  discard <| Runtime.dispatch successor self (.reserve [id] token)
  Runtime.finishClaim successor "integration" token
  expectError (Runtime.releaseCoordinator successor) "Finish or cancel"
  let submitted ← Runtime.submission (← Runtime.readState successor) id
  Runtime.checkout successor (.review submitted.work.branch snapshot)
  discard <| Runtime.run successor (.land [{ epic := id, snapshot }] snapshot.head "Previously reviewed fixture")
  check ((← fixture.ref Git.mainRef) == snapshot.head.value) "Successor could not land reviewed work"

/-- Runtime coverage is intentionally separate from pure transition and transport tests. -/
def runtimeTests : List (String × IO Unit) := [
  ("runtime join creates linked worktree without changing dirty primary", testJoinPreservesPrimary),
  ("runtime invalid join duration leaves no candidate and corrected retry works", testInvalidJoinDurationLeavesNoCandidate),
  ("runtime rejected takeover preserves old identity and authority", testRejectedTakeoverPreservesIdentity),
  ("runtime accepted pending join recovers after lost reply and failed read", testPendingJoinRecovery),
  ("runtime expired replaced pending join rotates fresh identity and token", testExpiredPendingJoinRotatesIdentity),
  ("runtime claim is durable before push and recovers its accepted generation", testDurableWorkClaimRecovery),
  ("runtime worktree lock rejects overlapping mutations and preserves claims", testLocalLockSerializesIdentityMutation),
  ("runtime planned handoff rejects dirt and resumes reviewed work in a fresh worktree", testCoordinatorHandoff),
  ("runtime A-B-A checkout refuses to omit B's pushed contribution", testAlternatingAuthorsPreservePushedWork),
  ("runtime validation failure permits reservation retry with new pending token", testReservationSurvivesValidationFailure),
  ("runtime landing on the reviewed base fast-forwards unchanged", testLandingFastForwardsCurrentBase),
  ("runtime landing after a disjoint main move merges and regenerates roots", testLandingMergesDisjointMainMove),
  ("runtime landing refuses a main move on a reviewed file", testLandingRefusesOverlappingMainMove),
  ("runtime landing refuses a textual conflict and leaves a clean worktree", testLandingRefusesTextualConflict),
  ("runtime landing batches two disjoint epics in one call", testLandingBatchesDisjointEpics),
  ("runtime landing refuses a batch whose epics overlap", testLandingRefusesOverlappingBatch)]

end Coordination.Tests
