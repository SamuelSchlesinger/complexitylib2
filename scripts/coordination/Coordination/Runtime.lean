/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (project coordination tooling)
import Coordination.Protocol
import Coordination.Git
import Std.Time.DateTime.Timestamp

/-! Worktree-local identities and the IO interpretation of the typed protocol.
Pending claims are durable before publication; retries can recognize an accepted
claim after a lost response. Git observations are refreshed inside each transaction. -/

namespace Coordination.Runtime

open Lean Git

structure Claim where
  key : String
  token : Token
  deriving ToJson, FromJson

structure Identity where
  actor : Actor
  role : Role
  leaseSeconds : Nat := 14400
  tokens : List Token := []
  pending : List Claim := []
  deriving ToJson, FromJson

def now : IO Nat := do
  return (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat

def readJson {α : Type} [FromJson α] (path : System.FilePath) : IO α := do
  let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile path)
  IO.ofExcept <| fromJson? json

def writeJson {α : Type} [ToJson α] (path : System.FilePath) (value : α) : IO Unit := do
  let temporary := System.FilePath.mk (path.toString ++ "." ++ (← nonce))
  IO.FS.writeFile temporary ((toJson value).pretty ++ "\n")
  IO.FS.rename temporary path

/-- Serialize mutating CLI commands in one worktree, including local identity updates. -/
def withLock {α : Type} (repo : Repository) (action : IO α) : IO α := do
  let dir := System.FilePath.mk (line (← repo.run #["rev-parse", "--absolute-git-dir"]))
  let lock := dir / "coordination.lock"
  try
    IO.FS.createDir lock
  catch _ =>
    throw <| IO.userError s!"Another command holds {lock}. If interrupted, check its owner PID before removing the lock."
  let owner := lock / "owner"
  try
    IO.FS.writeFile owner s!"{← IO.Process.getPID}\n"
    action
  finally
    if ← owner.pathExists then IO.FS.removeFile owner
    IO.FS.removeDir lock

def identityPath (repo : Repository) : IO System.FilePath := do
  let common := line (← repo.run #["rev-parse", "--path-format=absolute", "--git-common-dir"])
  let current := line (← repo.run #["rev-parse", "--absolute-git-dir"])
  if common == current then
    throw <| IO.userError "Join from the primary checkout, then use the printed linked worktree"
  return System.FilePath.mk current / "coordination-agent.json"

def identity (repo : Repository) : IO Identity := do
  let path ← identityPath repo
  unless (← path.pathExists) do
    throw <| IO.userError "Run join first, then work inside the printed worktree"
  readJson path

def claim (repo : Repository) (key : String) : IO (Identity × Token) := do
  let mut self ← identity repo
  let token ← match self.pending.find? (·.key == key) with
    | some pending => pure pending.token
    | none => do
      let token := Token.mk (← nonce)
      self := { self with pending := { key, token } :: self.pending }
      writeJson (← identityPath repo) self
      pure token
  return (self, token)

def finishClaim (repo : Repository) (key : String) (token : Token) : IO Unit := do
  let self ← identity repo
  writeJson (← identityPath repo) { self with
    tokens := token :: self.tokens.filter (· != token)
    pending := self.pending.filter (·.key != key) }

def readState (repo : Repository) : IO State := do
  let some (_, json) ← repo.readBoard | throw <| IO.userError "Initialize the board first"
  let state : State ← IO.ofExcept <| fromJson? json
  unless state.version == 1 do throw <| IO.userError "Unsupported coordination schema"
  return state

def getEpic (state : State) (id : EpicId) : IO Epic := do
  let some epic := state.epics.find? (·.id == id) | throw <| IO.userError "Unknown epic"
  return epic

def submission (state : State) (id : EpicId) : IO Submission := do
  match (← getEpic state id).phase with
  | .submitted value => return value
  | _ => throw <| IO.userError "Epic has no submitted snapshot"

def requiredRef (repo : Repository) (ref : String) : IO String := do
  let some head ← repo.fetch ref | throw <| IO.userError s!"Missing ref {ref}"
  return head

/-- The ranges whose base is an ancestor of its head. -/
def observedAncestry (repo : Repository) (ranges : List Snapshot) : IO (List Snapshot) :=
  ranges.filterM fun range => repo.ancestor range.base.value range.head.value

/-- Ancestry and path observations for landing one submission on `main`, after confirming that
its head is still on its work branch, which also fetches the head's objects. -/
def evidence (repo : Repository) (epic : EpicId) (s : Submission) (main : Oid) :
    IO (List Snapshot × List Diff) := do
  let snapshot := s.snapshot
  let tip ← requiredRef repo ("refs/heads/" ++ s.work.branch)
  unless (← repo.ancestor snapshot.head.value tip) do
    throw <| IO.userError s!"Submitted commit of {epic.value} is no longer on its work branch"
  let moved : Snapshot := { base := snapshot.base, head := main }
  let ancestry ← observedAncestry repo [snapshot, moved]
  let diffs : List Diff := [
    { range := snapshot, paths := ← repo.changedPaths snapshot.base.value snapshot.head.value },
    { range := moved, paths := ← repo.changedPaths snapshot.base.value main.value }]
  return (ancestry, diffs)

private def submitted (state : State) (id : EpicId) : Option Submission :=
  match (state.epics.find? (·.id == id)).map (·.phase) with
  | some (Phase.submitted s) => some s
  | _ => none

def context (repo : Repository) (self : Identity) (state : State) (cmd : Command) :
    IO Context := do
  let time ← now
  let mut ctx : Context := {
    actor := self.actor
    now := time
    heldTokens := self.tokens ++ self.pending.map (·.token) }
  match cmd with
  | .submit epic snapshot _ _ =>
    let task ← getEpic state epic
    let .working work := task.phase | throw <| IO.userError "Epic is not being implemented"
    repo.clean snapshot.head.value
    let main : Oid := ⟨← requiredRef repo mainRef⟩
    ctx := { ctx with
      cleanHead := some snapshot.head
      main := some main
      branchHead := some ⟨(← requiredRef repo ("refs/heads/" ++ work.branch))⟩
      ancestry := ← observedAncestry repo [snapshot, { base := snapshot.base, head := main }] }
  | .review _ _ snapshot _ _ =>
    repo.clean snapshot.head.value
    ctx := { ctx with cleanHead := some snapshot.head }
  | .reserve epics _ =>
    let main : Oid := ⟨← requiredRef repo mainRef⟩
    ctx := { ctx with main := some main }
    for id in epics do
      if let some s := submitted state id then
        let (ancestry, diffs) ← evidence repo id s main
        ctx := { ctx with ancestry := ctx.ancestry ++ ancestry, diffs := ctx.diffs ++ diffs }
  | .land candidates landed _ =>
    repo.clean landed.value
    let main : Oid := ⟨← requiredRef repo mainRef⟩
    ctx := { ctx with
      main := some main
      cleanHead := some landed
      ancestry := ← observedAncestry repo [{ base := main, head := landed }] }
    for candidate in candidates do
      if let some s := submitted state candidate.epic then
        let (ancestry, diffs) ← evidence repo candidate.epic s main
        let included ← observedAncestry repo [{ base := candidate.snapshot.head, head := landed }]
        ctx := { ctx with
          ancestry := ctx.ancestry ++ ancestry ++ included
          diffs := ctx.diffs ++ diffs }
  | _ => pure ()
  return ctx

/-- Execute one typed command, rerunning observations and pure checks on every retry. -/
def dispatch (repo : Repository) (self : Identity) (cmd : Command) : IO Outcome := do
  let result ← IO.mkRef (none : Option Outcome)
  discard <| repo.update ({} : State) (reprStr cmd) (fun state => do
    let outcome ← IO.ofExcept <| Coordination.apply (← context repo self state cmd) state cmd
    result.set (some outcome)
    let landing := match outcome.publication with
      | .boardOnly => none
      | .atomicLanding main landed => some { base := main.value, head := landed.value : Landing }
    return (outcome.state, landing))
  let some outcome ← result.get | throw <| IO.userError "Transaction produced no result"
  return outcome

def checkout (repo : Repository) (action : Checkout) : IO Unit := do
  repo.clean (← repo.head)
  match action with
  | .review branch snapshot =>
    let head ← requiredRef repo ("refs/heads/" ++ branch)
    unless (← repo.ancestor snapshot.head.value head) do
      throw <| IO.userError "Submitted commit is no longer on its work branch"
    discard <| repo.run #["switch", "--detach", snapshot.head.value]
  | .work branch resume =>
    let resumeHead ← resume.mapM fun prior => requiredRef repo ("refs/heads/" ++ prior)
    let found ← repo.execute #["show-ref", "--verify", "--quiet", "refs/heads/" ++ branch] none
    let head ← if found.exitCode == 0 then pure ("refs/heads/" ++ branch) else do
      match (← repo.fetch ("refs/heads/" ++ branch) false) with
        | some head => pure head
        | none => match resumeHead with
          | some head => pure head
          | none => requiredRef repo mainRef
    if let some tip := resumeHead then
      unless (← repo.ancestor tip head) do
        throw <| IO.userError s!"Existing {branch} omits its continuation branch; merge {resume.getD ""} before restarting"
    if found.exitCode == 0 then
      discard <| repo.run #["switch", branch]
    else
      discard <| repo.run #["switch", "-c", branch, head]

def run (repo : Repository) (cmd : Command) : IO Outcome := do
  let outcome ← dispatch repo (← identity repo) cmd
  if let some action := outcome.checkout then checkout repo action
  return outcome

/-- Planned handoff preserves the board and refuses to leave uncommitted integration work. -/
def releaseCoordinator (repo : Repository) : IO Outcome := do
  repo.clean (← repo.head)
  run repo .releaseCoordinator

def start (repo : Repository) (epic : EpicId) (kind : AssignmentKind) : IO Outcome := do
  repo.clean (← repo.head)
  let key := s!"start:{epic.value}:{reprStr kind}"
  let (self, token) ← claim repo key
  let outcome ← dispatch repo self (.start epic kind token)
  finishClaim repo key token
  if let some action := outcome.checkout then checkout repo action
  return outcome

/-- Stage the identity before joining; a rejected takeover leaves the live identity intact. -/
def join (repo : Repository) (name : AgentId) (role : Role) (here takeover : Bool)
    (leaseSeconds := 14400) : IO System.FilePath := do
  unless 300 ≤ leaseSeconds && leaseSeconds ≤ 86400 do
    throw <| IO.userError "Lease duration must be 300 to 86400 seconds"
  -- Reuse the protocol's identifier check before constructing paths or branch names.
  unless !name.value.isEmpty && name.value.toList.all (fun c => c.isLower || c.isDigit || c == '-')
      && name.value.toList.head!.isLower && name.value.length ≤ 64 do
    throw <| IO.userError "Names must start with a lowercase letter and contain letters, digits or hyphens"
  let worker ← if here then pure repo else do
    let base ← requiredRef repo mainRef
    let entries := (← repo.run #["worktree", "list", "--porcelain", "-z"]).splitOn "\x00"
    let primary := System.FilePath.mk ((entries.head!.drop 9).toString)
    let destination := primary / ".worktrees" / name.value
    unless (← destination.pathExists) do
      discard <| repo.run #["worktree", "add", "-b", "worker/" ++ name.value,
        destination.toString, base]
    let worker ← Repository.open destination repo.remote
    let common (r : Repository) := line <$> r.run
      #["rev-parse", "--path-format=absolute", "--git-common-dir"]
    unless (← common repo) == (← common worker) do
      throw <| IO.userError "Destination belongs to a different repository"
    pure worker
  withLock worker do
    let path ← identityPath worker
    let pendingPath := System.FilePath.mk (path.toString ++ ".pending")
    let mut candidate : Option Identity ← if ← pendingPath.pathExists then
      some <$> readJson pendingPath else pure none
    -- A lost response followed by a long outage must not make --takeover unrecoverable.
    if let some self := candidate then
      let board ← readState worker
      if takeover then
        match board.agents.find? (·.actor.agent == self.actor.agent) with
        | none => candidate := none
        | some agent =>
          if agent.actor != self.actor || (← now) > agent.expires + 60 then candidate := none
    let self ← match candidate with
      | some self =>
        if self.actor.agent == name && self.role == role && self.leaseSeconds == leaseSeconds then
          pure self
        else throw <| IO.userError "Retry the pending join with the same name, role and duration"
      | none => do
        if (← path.pathExists) && !takeover then
          throw <| IO.userError "This worktree has an identity; use heartbeat, or takeover after expiry"
        let self : Identity := {
          actor := { agent := name, session := ⟨(← nonce)⟩ }
          role
          leaseSeconds
          tokens := [⟨(← nonce)⟩] }
        writeJson pendingPath self
        pure self
    let some token := self.tokens.head? | throw <| IO.userError "Pending identity has no join token"
    discard <| dispatch worker self (.join role leaseSeconds token takeover)
    writeJson path self
    IO.FS.removeFile pendingPath
    return worker.root

/-- Submit the worktree's head; the reviewed base is the latest `main` commit it contains. -/
def ready (repo : Repository) (epic : EpicId) (summary : String) : IO Outcome := do
  let head ← repo.head
  let main ← requiredRef repo mainRef
  let base := line (← repo.run #["merge-base", main, head])
  let paths ← repo.changedPaths base head
  run repo (.submit epic { base := ⟨base⟩, head := ⟨head⟩ } paths summary)

/-- Run validation with inherited output, renewing the lease while the child runs. -/
def validate (repo : Repository) (cmd : String) (args : Array String)
    (accept : UInt32 → Bool := (· == 0)) : IO Unit := do
  let child ← IO.Process.spawn { cmd, args, cwd := repo.root }
  let mut lastHeartbeat ← now
  repeat
    if let some code ← child.tryWait then
      unless accept code do
        throw <| IO.userError s!"{cmd} failed; no code was published. Use cancel if abandoning integration."
      return
    IO.sleep 1000
    if (← now) ≥ lastHeartbeat + 60 then
      try
        discard <| run repo .heartbeat
        lastHeartbeat ← now
      catch error =>
        child.kill
        discard child.wait
        throw error

/-- The six project gates and the coordination tests; the result is the validation evidence
recorded in each completed epic. -/
def projectChecks (repo : Repository) : IO String := do
  validate repo "bash" #["scripts/check.sh"]
  validate repo "lake" #["-d", "scripts/coordination", "test"]
  return "scripts/check.sh: six gates passed; coordination tests: passed"

/-- Regenerate the root imports on the working tree. `lake exe mk_all` exits with the number of
files it rewrote, so its `--check` mode verifies the result. Fixtures without a lakefile have no
roots to regenerate. -/
def regenerateRoots (repo : Repository) : IO Unit := do
  if ← (repo.root / "lakefile.toml").pathExists then
    validate repo "lake" #["exe", "mk_all"] (· ≤ 125)
    validate repo "lake" #["exe", "mk_all", "--check"]

def mergeMessage (candidate : Candidate) : String :=
  s!"merge: land {candidate.epic.value}\n\nReviewed base {candidate.snapshot.base.value}, head {
    candidate.snapshot.head.value}\n"

/-- Merge a reviewed head onto the detached HEAD. Conflicts are tolerated only in the generated
roots, which are reset to the `main` side and regenerated on the merged tree before the merge
commit is created. -/
private def merge (repo : Repository) (candidate : Candidate) (regenerate : Repository → IO Unit) :
    IO Unit := do
  let name := candidate.epic.value
  let attempt ← repo.execute #["merge", "--no-ff", "--no-commit", candidate.snapshot.head.value] none
  let unmerged ← if attempt.exitCode == 0 then pure [] else
    (fun paths => (paths.splitOn "\x00").dropLast) <$>
      repo.run #["diff", "--name-only", "--diff-filter=U", "-z"]
  let conflicts := unmerged.filter (!generatedRoots.contains ·)
  unless attempt.exitCode == 0 || (attempt.exitCode == 1 && !unmerged.isEmpty && conflicts.isEmpty) do
    discard <| repo.execute #["merge", "--abort"] none
    let detail := if conflicts.isEmpty then "" else s!" with conflicts in {", ".intercalate conflicts}"
    throw <| IO.userError s!"Merging the reviewed head of {name} onto main failed{detail}: {
      attempt.stdout}{attempt.stderr}Reopen, merge main and obtain new reviews."
  try
    for root in unmerged do
      IO.FS.writeFile (repo.root / root) (← repo.run #["show", ":2:" ++ root])
    regenerate repo
    let roots ← generatedRoots.filterM fun (root : String) => (repo.root / root).pathExists
    unless roots.isEmpty do discard <| repo.run (#["add", "--"] ++ roots.toArray)
    discard <| repo.run #["commit", "--quiet", "-m", mergeMessage candidate]
  catch error =>
    discard <| repo.execute #["merge", "--abort"] none
    throw error

/-- Build the commit to publish as `main` in this worktree: each reviewed head in order is
fast-forwarded when its base is the current tip and merged otherwise. -/
def integrate (repo : Repository) (main : Oid) (candidates : List Candidate)
    (regenerate : Repository → IO Unit) : IO Oid := do
  discard <| repo.run #["switch", "--detach", main.value]
  for candidate in candidates do
    if candidate.snapshot.base.value == (← repo.head) then
      discard <| repo.run #["switch", "--detach", candidate.snapshot.head.value]
    else
      merge repo candidate regenerate
  let landed ← repo.head
  repo.clean landed
  return ⟨landed⟩

/-- Reserve, integrate, validate and publish the listed epics; one epic is a batch of one.
`checks` returns the validation evidence recorded in each completed epic. -/
def land (repo : Repository) (epics : List EpicId)
    (checks : Repository → IO String := projectChecks)
    (regenerate : Repository → IO Unit := regenerateRoots) : IO Outcome := do
  repo.clean (← repo.head)
  let (self, token) ← claim repo "integration"
  let reserved ← dispatch repo self (.reserve epics token)
  finishClaim repo "integration" token
  let some integration := reserved.state.integration
    | throw <| IO.userError "Integration reservation is absent"
  let some main := integration.main
    | throw <| IO.userError "Integration reservation does not record its main; cancel and land again"
  let landed ← integrate repo main integration.candidates regenerate
  let validation ← checks repo
  discard <| run repo .heartbeat
  run repo (.land integration.candidates landed validation)

end Coordination.Runtime
