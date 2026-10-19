/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (repository coordination tooling)

public import Lean

/-!
# Pure coordination protocol

The transport supplies observations of Git and a clock. This module decides which board updates
are permitted. Publication, pending-token persistence, checkout and validation remain IO duties.
Agent identities describe cooperating sessions; they are not an authentication mechanism.
-/

public section

namespace Coordination

open Lean

structure AgentId where
  value : String
  deriving BEq, Repr, ToJson, FromJson

structure EpicId where
  value : String
  deriving BEq, Repr, ToJson, FromJson

structure SessionId where
  value : String
  deriving BEq, Repr, ToJson, FromJson

structure Token where
  value : String
  deriving BEq, Repr, ToJson, FromJson

structure Oid where
  value : String
  deriving BEq, Repr, ToJson, FromJson

inductive Role where
  | coordinator | worker
  deriving BEq, Repr, ToJson, FromJson

inductive AssignmentKind where
  | work | api | correctness
  deriving BEq, Repr, ToJson, FromJson

inductive ReviewKind where
  | api | correctness
  deriving BEq, Repr, ToJson, FromJson

inductive Verdict where
  | approve | changes
  deriving BEq, Repr, ToJson, FromJson

structure Actor where
  agent : AgentId
  session : SessionId
  deriving BEq, Repr, ToJson, FromJson

structure Lease where
  holder : Actor
  token : Token
  expires : Nat
  deriving BEq, Repr, ToJson, FromJson

structure Snapshot where
  base : Oid
  head : Oid
  deriving BEq, Repr, ToJson, FromJson

/-- A reviewed snapshot reserved for landing. -/
structure Candidate where
  epic : EpicId
  snapshot : Snapshot
  deriving BEq, Repr, ToJson, FromJson

structure Agent where
  actor : Actor
  role : Role
  expires : Nat
  leaseSeconds : Nat
  deriving BEq, Repr, ToJson, FromJson

structure Work where
  assignee : AgentId
  branch : String
  resume : Option String := none
  lease : Option Lease := none
  report : String := ""
  blocked : Bool := false
  deriving BEq, Repr, ToJson, FromJson

structure Review where
  reviewer : Actor
  snapshot : Snapshot
  verdict : Verdict
  note : String
  time : Nat
  deriving BEq, Repr, ToJson, FromJson

inductive ReviewSlot where
  | unassigned
  | assigned (agent : AgentId)
  | active (lease : Lease) (report : String) (blocked : Bool)
  | finished (review : Review)
  deriving BEq, Repr, ToJson, FromJson

structure Reviews where
  api : ReviewSlot := .unassigned
  correctness : ReviewSlot := .unassigned
  deriving BEq, Repr, ToJson, FromJson

structure Submission where
  work : Work
  snapshot : Snapshot
  summary : String
  reviews : Reviews := {}
  deriving BEq, Repr, ToJson, FromJson

structure Completion where
  snapshot : Snapshot
  /-- The commit published as `main`: the reviewed head when it was fast-forwarded, otherwise the
  merge commit landing it. Absent in records written before merge landings existed. -/
  landed : Option Oid := none
  summary : String
  api : Review
  correctness : Review
  validation : String
  landedBy : Actor
  landedAt : Nat
  deriving BEq, Repr, ToJson, FromJson

inductive Phase where
  | unassigned
  | working (work : Work)
  | submitted (submission : Submission)
  | merged (completion : Completion)
  deriving BEq, Repr, ToJson, FromJson

structure Epic where
  id : EpicId
  goal : String
  paths : List String
  dependencies : List EpicId := []
  authors : List AgentId := []
  resume : Option String := none
  report : String := ""
  phase : Phase := .unassigned
  deriving BEq, Repr, ToJson, FromJson

/-- Reviewed snapshots reserved for one landing onto the `main` observed at reservation. -/
structure Integration where
  lease : Lease
  /-- The landing must still extend exactly this commit. Absent in records written before merge
  landings existed. -/
  main : Option Oid := none
  candidates : List Candidate
  deriving BEq, Repr, ToJson

/-- Records written before batch landings reserved a single `epic` and `snapshot`. -/
instance : FromJson Integration where
  fromJson? json := do
    let lease ← json.getObjValAs? Lease "lease"
    let main ← json.getObjValAs? (Option Oid) "main"
    let candidates ← match json.getObjVal? "candidates" with
      | .ok value => fromJson? value
      | .error _ => do
        let epic ← json.getObjValAs? EpicId "epic"
        let snapshot ← json.getObjValAs? Snapshot "snapshot"
        pure [{ epic, snapshot }]
    pure { lease, main, candidates }

structure State where
  version : Nat := 1
  agents : List Agent := []
  epics : List Epic := []
  coordinator : Option Lease := none
  integration : Option Integration := none
  deriving BEq, Repr, ToJson, FromJson

/-- Paths observed to differ between the base and the head of a range. -/
structure Diff where
  range : Snapshot
  paths : List String
  deriving BEq, Repr, ToJson, FromJson

/-- Exact Git observations are supplied by the IO shell, never inferred from branch names.
`ancestry` lists ranges whose base was observed to be an ancestor of its head. -/
structure Context where
  actor : Actor
  now : Nat
  heldTokens : List Token := []
  main : Option Oid := none
  branchHead : Option Oid := none
  cleanHead : Option Oid := none
  ancestry : List Snapshot := []
  diffs : List Diff := []
  deriving BEq, Repr, ToJson, FromJson

inductive Command where
  | join (role : Role) (leaseSeconds : Nat) (token : Token) (takeover : Bool)
  | heartbeat
  | releaseCoordinator
  | plan (epic : EpicId) (goal : String) (paths : List String) (dependencies : List EpicId)
  | revise (epic : EpicId) (goal : String) (addPaths : List String)
  | instruct (epic : EpicId) (text : String)
  | assign (epic : EpicId) (agent : AgentId) (kind : AssignmentKind) (replace : Bool)
  | start (epic : EpicId) (kind : AssignmentKind) (token : Token)
  | note (epic : EpicId) (kind : AssignmentKind) (text : String) (blocked : Bool)
  | reopen (epic : EpicId) (reason : String)
  | unassign (epic : EpicId) (reason : String)
  | submit (epic : EpicId) (snapshot : Snapshot) (changedPaths : List String) (summary : String)
  | review (epic : EpicId) (kind : ReviewKind) (snapshot : Snapshot)
      (verdict : Verdict) (note : String)
  | reserve (epics : List EpicId) (token : Token)
  | land (candidates : List Candidate) (landed : Oid) (validation : String)
  | cancel
  deriving BEq, Repr, ToJson, FromJson

/-- A landing must publish both refs atomically and guard the exact old `main` OID. -/
inductive Publication where
  | boardOnly
  | atomicLanding (main landed : Oid)
  deriving BEq, Repr, ToJson, FromJson

inductive Checkout where
  | work (branch : String) (resume : Option String)
  | review (branch : String) (snapshot : Snapshot)
  deriving BEq, Repr, ToJson, FromJson

structure Outcome where
  state : State
  message : String
  publication : Publication := .boardOnly
  checkout : Option Checkout := none
  deriving BEq, Repr, ToJson, FromJson

def grace : Nat := 60

private def check (condition : Prop) [Decidable condition] (message : String) : Except String Unit :=
  if condition then pure () else throw message

private def validName (name : String) : Bool :=
  let lower (c : Char) := decide ('a' ≤ c ∧ c ≤ 'z')
  let digit (c : Char) := decide ('0' ≤ c ∧ c ≤ '9')
  let chars := name.toList
  chars.head?.any lower && decide (chars.length ≤ 64) &&
    chars.all (fun c => lower c || digit c || c == '-')

private def validScope (path : String) : Bool :=
  let parts := path.splitOn "/"
  !path.isEmpty && !path.startsWith "/" &&
    parts.all (fun part => !part.isEmpty && part != "." && part != "..") &&
    ![".git", ".lake", ".worktrees"].contains (parts.headD "")

def scopeContains (scope path : String) : Bool :=
  path == scope || path.startsWith (scope ++ "/")

def scopesOverlap (left right : String) : Bool :=
  scopeContains left right || scopeContains right left

/-- Root import files that `lake exe mk_all` regenerates; every landing may rewrite them. -/
def generatedRoots : List String := ["Complexity.lean", "ComplexityTests.lean"]

/-- Paths changed on both sides, apart from the regenerated roots. A landing by merge requires
this to be empty so that no reviewed content changes. -/
def overlappingPaths (left right : List String) : List String :=
  (left.filter fun path => right.contains path && !generatedRoots.contains path).eraseDups

/-- `older` is `newer` or was observed to be one of its ancestors. -/
def ancestorOf (ctx : Context) (older newer : Oid) : Bool :=
  older == newer || ctx.ancestry.contains { base := older, head := newer }

def Reviews.get (reviews : Reviews) : ReviewKind → ReviewSlot
  | .api => reviews.api
  | .correctness => reviews.correctness

def Reviews.set (reviews : Reviews) (kind : ReviewKind) (slot : ReviewSlot) : Reviews :=
  match kind with
  | .api => { reviews with api := slot }
  | .correctness => { reviews with correctness := slot }

theorem Reviews.get_set (reviews : Reviews) (kind : ReviewKind) (slot : ReviewSlot) :
    (reviews.set kind slot).get kind = slot := by
  cases kind <;> rfl

private def reviewKind : AssignmentKind → Option ReviewKind
  | .work => none
  | .api => some .api
  | .correctness => some .correctness

private def otherKind : ReviewKind → ReviewKind
  | .api => .correctness
  | .correctness => .api

private def slotAgent : ReviewSlot → Option AgentId
  | .unassigned => none
  | .assigned agent => some agent
  | .active lease _ _ => some lease.holder.agent
  | .finished review => some review.reviewer.agent

private def slotLease : ReviewSlot → Option Lease
  | .active lease _ _ => some lease
  | _ => none

private def findAgent (state : State) (id : AgentId) : Except String Agent :=
  match state.agents.find? (fun a => a.actor.agent == id) with
  | some agent => pure agent
  | none => throw "Agent has not joined"

private def findEpic (state : State) (id : EpicId) : Except String Epic :=
  match state.epics.find? (fun e => e.id == id) with
  | some epic => pure epic
  | none => throw "Unknown epic"

private def putAgent (state : State) (agent : Agent) : State :=
  if state.agents.any (fun a => a.actor.agent == agent.actor.agent) then
    { state with agents := state.agents.map fun a =>
        if a.actor.agent == agent.actor.agent then agent else a }
  else { state with agents := state.agents ++ [agent] }

private def putEpic (state : State) (epic : Epic) : State :=
  if state.epics.any (fun e => e.id == epic.id) then
    { state with epics := state.epics.map fun e => if e.id == epic.id then epic else e }
  else { state with epics := state.epics ++ [epic] }

private def validate (state : State) : Except String Unit := do
  check (state.version == 1) "Unsupported coordination schema"
  let agents := state.agents.map (·.actor.agent)
  let epics := state.epics.map (·.id)
  check (agents.eraseDups.length == agents.length) "Duplicate agent IDs in board"
  check (epics.eraseDups.length == epics.length) "Duplicate epic IDs in board"

private def actor (ctx : Context) (state : State) : Except String Agent := do
  let agent ← findAgent state ctx.actor.agent
  check (agent.actor == ctx.actor) "Session was replaced"
  check (ctx.now ≤ agent.expires) "Session expired; explicitly rejoin"
  pure agent

def holds (ctx : Context) (lease : Lease) : Bool :=
  lease.holder == ctx.actor && ctx.heldTokens.contains lease.token && decide (ctx.now ≤ lease.expires)

theorem holds_not_expired {ctx : Context} {lease : Lease} (h : holds ctx lease = true) :
    ctx.now ≤ lease.expires := by
  simp_all [holds]

private def requireHeld (ctx : Context) (lease : Option Lease) : Except String Lease := do
  let some lease := lease | throw "Claim is absent"
  check (holds ctx lease) "Claim generation is absent, expired or replaced"
  pure lease

private def coordinator (ctx : Context) (state : State) : Except String Agent := do
  let agent ← actor ctx state
  let _ ← requireHeld ctx state.coordinator
  pure agent

private def checkToken (ctx : Context) (token : Token) : Except String Unit := do
  check (!token.value.isEmpty && ctx.heldTokens.contains token)
    "Persist the pending claim token locally before publication"

private def makeLease (ctx : Context) (agent : Agent) (token : Token) : Lease :=
  { holder := ctx.actor, token, expires := ctx.now + agent.leaseSeconds }

private def replaceable (ctx : Context) (lease : Option Lease) (replace : Bool) : Bool :=
  lease.all (fun l => replace || decide (l.expires + grace < ctx.now))

private def acquire (ctx : Context) (lease : Option Lease) : Bool :=
  lease.all (fun l => holds ctx l || decide (l.expires + grace < ctx.now))

/-- Dependencies must have landed or precede the epic in the batch being landed. -/
private def dependenciesDone (state : State) (epic : Epic) (earlier : List EpicId := []) : Bool :=
  epic.dependencies.all fun id => earlier.contains id || state.epics.any fun e =>
    e.id == id && match e.phase with | .merged _ => true | _ => false

private def occupiesScope (epic : Epic) : Bool :=
  match epic.phase with
  | .working _ | .submitted _ => true
  | _ => false

private def scopeAvailable (state : State) (epic : Epic) : Bool :=
  state.epics.all fun other => other.id == epic.id || !occupiesScope other ||
    !(epic.paths.any fun a => other.paths.any (scopesOverlap a))

private def workOf (epic : Epic) : Except String Work :=
  match epic.phase with
  | .working work => pure work
  | _ => throw "Epic is not assigned for implementation; reopen a submission before editing"

private def submissionOf (epic : Epic) : Except String Submission :=
  match epic.phase with
  | .submitted submission => pure submission
  | _ => throw "Epic has no submitted snapshot"

private def clearIntegration (state : State) (epic : EpicId) : State :=
  if state.integration.any (fun i => i.candidates.any (·.epic == epic)) then
    { state with integration := none }
  else state

private def renewLease (ctx : Context) (expires : Nat) (lease : Lease) : Lease :=
  if holds ctx lease then { lease with expires } else lease

private def renewSlot (ctx : Context) (expires : Nat) : ReviewSlot → ReviewSlot
  | .active lease report blocked => .active (renewLease ctx expires lease) report blocked
  | slot => slot

private def renewEpic (ctx : Context) (expires : Nat) (epic : Epic) : Epic :=
  match epic.phase with
  | .working work =>
    let work := { work with lease := work.lease.map (renewLease ctx expires) }
    { epic with phase := .working work }
  | .submitted s =>
    let work := { s.work with lease := s.work.lease.map (renewLease ctx expires) }
    let reviews : Reviews := {
      api := renewSlot ctx expires s.reviews.api
      correctness := renewSlot ctx expires s.reviews.correctness }
    { epic with phase := .submitted { s with work, reviews } }
  | _ => epic

/-- The reviewed base is the observed `main` or one of its ancestors. -/
private def onMain (ctx : Context) (base : Oid) : Bool :=
  ctx.main.any (ancestorOf ctx base)

private def approved (ctx : Context) (state : State) (epic : Epic) (earlier : List EpicId := []) :
    Except String (Submission × Review × Review) := do
  let s ← submissionOf epic
  let .finished api := s.reviews.api | throw "Missing current API approval"
  let .finished correctness := s.reviews.correctness | throw "Missing current correctness approval"
  check (api.verdict == .approve && correctness.verdict == .approve)
    "Review requests changes"
  check (api.snapshot == s.snapshot && correctness.snapshot == s.snapshot)
    "Reviews concern a different base or head"
  check (api.reviewer.agent != correctness.reviewer.agent &&
    !epic.authors.contains api.reviewer.agent && !epic.authors.contains correctness.reviewer.agent)
    "Reviews must be independent of every author and each other"
  check (dependenciesDone state epic earlier) "A dependency has not landed"
  check (onMain ctx s.snapshot.base)
    "Reviewed base is not on main; reopen, merge main and obtain new reviews"
  pure (s, api, correctness)

/-- Every epic of a landing in its order, each approved exactly as submitted. -/
private def approvedBatch (ctx : Context) (state : State) (epics : List EpicId) :
    Except String (List (Epic × Submission × Review × Review)) := do
  check (!epics.isEmpty) "Name at least one epic to land"
  check (epics.eraseDups.length == epics.length) "An epic is listed twice"
  let mut batch := []
  for id in epics do
    let epic ← findEpic state id
    let (s, api, correctness) ← approved ctx state epic (batch.map (·.1.id))
    batch := batch ++ [(epic, s, api, correctness)]
  pure batch

private def observedDiff (ctx : Context) (range : Snapshot) (what : String) :
    Except String (List String) :=
  match ctx.diffs.find? (·.range == range) with
  | some diff => pure diff.paths
  | none => throw s!"{what} were not observed"

/-- Reviewed snapshots land together only when, apart from the regenerated roots, none changes a
path that `main` changed since its base or that an earlier snapshot of the landing changes. -/
private def disjoint (ctx : Context) (main : Oid) (candidates : List Candidate) :
    Except String Unit := do
  let mut earlier : List (EpicId × List String) := []
  for candidate in candidates do
    let name := candidate.epic.value
    let own ← observedDiff ctx candidate.snapshot s!"Paths changed by {name}"
    let moved ← if main == candidate.snapshot.base then pure [] else
      observedDiff ctx { base := candidate.snapshot.base, head := main } "Paths changed on main"
    let overlap := overlappingPaths moved own
    check overlap.isEmpty s!"Main moved on reviewed files of {name} ({", ".intercalate overlap}); \
      reopen, merge main and obtain new reviews"
    for (other, paths) in earlier do
      let overlap := overlappingPaths paths own
      check overlap.isEmpty s!"{other.value} and {name} both change {", ".intercalate overlap}; \
        land one, then reopen the other, merge main and obtain new reviews"
    earlier := earlier ++ [(candidate.epic, own)]

private def result (state : State) (message : String) : Outcome := { state, message }

/-- Apply one command to a freshly fetched board. IO must retry this transition on a new board
after a rejected push, retaining its pending identity and generation tokens. -/
def apply (ctx : Context) (state : State) (command : Command) : Except String Outcome := do
  validate state
  check (validName ctx.actor.agent.value && !ctx.actor.session.value.isEmpty) "Invalid actor ID"
  match command with
  | .join role seconds token takeover =>
    check (300 ≤ seconds ∧ seconds ≤ 86400) "Lease duration must be 300 to 86400 seconds"
    if let some previous := state.agents.find? (fun a => a.actor.agent == ctx.actor.agent) then
      if previous.actor == ctx.actor && previous.role == role && previous.leaseSeconds == seconds &&
          decide (ctx.now ≤ previous.expires) then
        if role == .coordinator then
          let lease ← requireHeld ctx state.coordinator
          check (lease.token == token) "Pending coordinator generation differs"
        return result state "Session already joined"
      check (takeover && decide (previous.expires + grace < ctx.now))
        "Agent name is in use; only explicit expired takeover is permitted"
      check (previous.actor != ctx.actor) "Expired takeover requires a new session identity"
    let agent : Agent := {
      actor := ctx.actor
      role := role
      expires := ctx.now + seconds
      leaseSeconds := seconds }
    let state := putAgent state agent
    if role == .coordinator then
      checkToken ctx token
      check (replaceable ctx state.coordinator takeover &&
        state.coordinator.all (fun l => decide (l.expires + grace < ctx.now)))
        "A coordinator is already active; takeover must be explicit"
      check (state.coordinator.isNone || takeover) "Coordinator takeover must be explicit"
      check (state.coordinator.all (fun l => l.holder != ctx.actor && l.token != token))
        "Coordinator takeover requires a new identity and generation"
      return result { state with coordinator := some (makeLease ctx agent token) } "Coordinator joined"
    return result state "Worker joined"
  | .heartbeat =>
    let agent ← actor ctx state
    let expires := ctx.now + agent.leaseSeconds
    let state := putAgent state { agent with expires }
    return result { state with
      coordinator := state.coordinator.map (renewLease ctx expires)
      integration := state.integration.map fun i => { i with lease := renewLease ctx expires i.lease }
      epics := state.epics.map (renewEpic ctx expires) } "Heartbeat renewed held generations"
  | .releaseCoordinator =>
    let _ ← coordinator ctx state
    check state.integration.isNone "Finish or cancel integration before releasing the coordinator"
    return result { state with coordinator := none }
      "Coordinator released; work and reviews preserved. A fresh coordinator may join now."
  | .plan id goal paths dependencies =>
    let _ ← coordinator ctx state
    check (validName id.value) "Invalid epic ID"
    check (!state.epics.any (fun e => e.id == id)) "Epic already exists"
    check (!goal.isEmpty && !paths.isEmpty && paths.all validScope) "Goal and canonical scopes required"
    check (dependencies.all fun d => state.epics.any (fun e => e.id == d)) "Unknown dependency"
    let epic : Epic := {
      id, goal
      paths := paths.eraseDups
      dependencies := dependencies.eraseDups }
    return result (putEpic state epic) "Epic planned"
  | .revise id goal addPaths =>
    let _ ← coordinator ctx state
    let epic ← findEpic state id
    match epic.phase with
    | .unassigned | .working _ => pure ()
    | _ => throw "Only unsubmitted plans can change; reopen a submission first"
    check (!goal.isEmpty && addPaths.all validScope) "Goal and canonical scopes required"
    let revised := { epic with goal, paths := (epic.paths ++ addPaths).eraseDups }
    check (!occupiesScope epic || scopeAvailable state revised) "Scopes overlap an assigned epic"
    return result (putEpic state revised) "Plan revised; existing scopes and claims preserved"
  | .instruct id text =>
    let _ ← coordinator ctx state
    let epic ← findEpic state id
    match epic.phase with
    | .merged _ => throw "Completed epic records are immutable"
    | _ => pure ()
    check (!text.isEmpty) "Coordinator guidance is required"
    return result (putEpic state { epic with report := text }) "Coordinator guidance recorded"
  | .assign id worker kind replace =>
    let _ ← coordinator ctx state
    let _ ← findAgent state worker
    let epic ← findEpic state id
    match reviewKind kind with
    | none =>
      let previous ← match epic.phase with
        | .unassigned => pure none
        | .working work => pure (some work)
        | _ => throw "Reopen a submission before changing its implementation assignment"
      check (replaceable ctx (previous.bind (·.lease)) replace) "Work claim is live; explicitly replace it"
      check (scopeAvailable state epic) "Scopes overlap an assigned epic"
      let branch := "work/" ++ id.value ++ "/" ++ worker.value
      let resume := match previous with
        | some work => if work.assignee == worker then work.resume else some work.branch
        | none => epic.resume
      let work : Work := { assignee := worker, branch, resume }
      return result (putEpic state { epic with phase := .working work }) "Implementation assigned"
    | some rk =>
      let s ← submissionOf epic
      check (!epic.authors.contains worker) "Contributing authors cannot review this epic"
      check (slotAgent (s.reviews.get (otherKind rk)) != some worker) "Use two distinct reviewers"
      check (replaceable ctx (slotLease (s.reviews.get rk)) replace) "Review claim is live; explicitly replace it"
      let s := { s with reviews := s.reviews.set rk (.assigned worker) }
      return result (putEpic state { epic with phase := .submitted s }) "Review assigned"
  | .start id kind token =>
    let agent ← actor ctx state
    checkToken ctx token
    let epic ← findEpic state id
    let lease := makeLease ctx agent token
    match reviewKind kind with
    | none =>
      let work ← workOf epic
      check (work.assignee == ctx.actor.agent) "Implementation is assigned to another worker"
      check (acquire ctx work.lease) "Another live generation holds the implementation"
      check (dependenciesDone state epic) "A dependency has not landed"
      let work := { work with lease := some lease }
      let authors := if epic.authors.contains ctx.actor.agent then epic.authors
        else epic.authors ++ [ctx.actor.agent]
      return {
        state := putEpic state { epic with authors, phase := .working work }
        message := "Implementation started"
        checkout := some (.work work.branch work.resume) }
    | some rk =>
      let s ← submissionOf epic
      check (slotAgent (s.reviews.get rk) == some ctx.actor.agent) "Review is assigned to another worker"
      check (!epic.authors.contains ctx.actor.agent) "Authors cannot review their work"
      check (acquire ctx (slotLease (s.reviews.get rk))) "Another live generation holds the review"
      let reviews := s.reviews.set rk (.active lease "" false)
      return {
        state := putEpic state { epic with phase := .submitted { s with reviews } }
        message := "Review started; any prior approval is revoked"
        checkout := some (.review s.work.branch s.snapshot) }
  | .note id kind text blocked =>
    let _ ← actor ctx state
    let epic ← findEpic state id
    match reviewKind kind with
    | none =>
      let work ← workOf epic
      let _ ← requireHeld ctx work.lease
      let work := { work with report := text, blocked }
      return result (putEpic state { epic with phase := .working work }) "Implementation report recorded"
    | some rk =>
      let s ← submissionOf epic
      let lease ← requireHeld ctx (slotLease (s.reviews.get rk))
      let s := { s with reviews := s.reviews.set rk (.active lease text blocked) }
      return result (putEpic state { epic with phase := .submitted s }) "Review report recorded"
  | .reopen id reason =>
    let _ ← coordinator ctx state
    let epic ← findEpic state id
    let work ← match epic.phase with
      | .working work => pure work
      | .submitted s => pure s.work
      | _ => throw "Only assigned or submitted work can be reopened"
    let work := { work with lease := none, report := reason, blocked := false }
    let epic := { epic with report := reason, phase := .working work }
    return result (clearIntegration (putEpic state epic) id) "Reopened; reviews and integration revoked"
  | .unassign id reason =>
    let _ ← coordinator ctx state
    let epic ← findEpic state id
    let resume ← match epic.phase with
      | .merged _ => throw "Completed work remains in the journal"
      | .working work => pure (some work.branch)
      | .submitted s => pure (some s.work.branch)
      | .unassigned => pure epic.resume
    let epic := { epic with resume, report := reason, phase := .unassigned }
    return result (clearIntegration (putEpic state epic) id) "Assignment released; authors and resume ref preserved"
  | .submit id snapshot changedPaths summary =>
    let _ ← actor ctx state
    let epic ← findEpic state id
    let work ← workOf epic
    let _ ← requireHeld ctx work.lease
    check (ctx.cleanHead == some snapshot.head && ctx.branchHead == some snapshot.head)
      "Clean worktree and pushed assigned branch must match the submitted head"
    check (onMain ctx snapshot.base && snapshot.base != snapshot.head &&
      ctx.ancestry.contains snapshot) "Submission must extend a commit of the observed current main"
    check (changedPaths.all fun path => generatedRoots.contains path ||
      epic.paths.any (fun scope => scopeContains scope path)) "Change exceeds assigned paths"
    check (!summary.isEmpty) "Submission summary is required"
    let s : Submission := { work, snapshot, summary }
    return result (putEpic state { epic with phase := .submitted s }) "Immutable snapshot submitted"
  | .review id rk snapshot verdict note =>
    let _ ← actor ctx state
    let epic ← findEpic state id
    let s ← submissionOf epic
    check (s.snapshot == snapshot) "Review snapshot was replaced"
    check (ctx.cleanHead == some snapshot.head) "Review worktree does not match the snapshot"
    let _ ← requireHeld ctx (slotLease (s.reviews.get rk))
    check (!epic.authors.contains ctx.actor.agent) "Authors cannot review their work"
    check (!note.isEmpty) "Review evidence is required"
    let review : Review := { reviewer := ctx.actor, snapshot, verdict, note, time := ctx.now }
    let s := { s with reviews := s.reviews.set rk (.finished review) }
    return result (putEpic state { epic with phase := .submitted s }) "Review evidence recorded"
  | .reserve epics token =>
    let agent ← coordinator ctx state
    checkToken ctx token
    let some main := ctx.main | throw "Main was not observed"
    let batch ← approvedBatch ctx state epics
    let candidates := batch.map fun (epic, s, _, _) => { epic := epic.id, snapshot := s.snapshot }
    disjoint ctx main candidates
    if let some previous := state.integration then
      if previous.candidates == candidates && holds ctx previous.lease then
        -- A retry after a failed validation integrates against the main observed now.
        let state := { state with integration := some { previous with main := some main } }
        return result state (if previous.main == some main then
          "Integration already reserved by this held generation"
          else "Integration reservation renewed against the current main")
      check (previous.lease.expires + grace < ctx.now) "Integration is reserved; finish or cancel it"
    let integration : Integration := { lease := makeLease ctx agent token, main := some main, candidates }
    return result { state with integration := some integration } "Integration reserved"
  | .land candidates landed validation =>
    let _ ← coordinator ctx state
    let some integration := state.integration | throw "Integration reservation is absent"
    check (holds ctx integration.lease) "Integration generation was lost"
    check (integration.candidates == candidates) "Integration reservation changed"
    let some reserved := integration.main
      | throw "Integration reservation does not record its main; cancel and land again"
    let some main := ctx.main | throw "Main was not observed"
    check (reserved == main) "Main moved since the integration reservation; cancel and land again"
    let batch ← approvedBatch ctx state (candidates.map (·.epic))
    check (ctx.cleanHead == some landed) "Validated clean head differs from the landing"
    check (landed != main && ancestorOf ctx main landed) "Landing must extend the reserved main"
    for (candidate, epic, s, _, _) in candidates.zip batch do
      check (s.snapshot == candidate.snapshot) "Reviewed snapshot changed after reservation"
      check (ctx.ancestry.contains candidate.snapshot && ancestorOf ctx candidate.snapshot.head landed)
        s!"Landing omits the reviewed head of {epic.id.value}"
    disjoint ctx main candidates
    check (!validation.isEmpty) "Validation evidence is required"
    let mut state := state
    for (epic, s, api, correctness) in batch do
      let completion : Completion := {
        snapshot := s.snapshot
        landed := some landed
        api, correctness, validation
        summary := s.summary
        landedBy := ctx.actor
        landedAt := ctx.now }
      state := putEpic state { epic with phase := .merged completion }
    return {
      state := { state with integration := none }
      message := "Publish completion and main atomically"
      publication := .atomicLanding main landed }
  | .cancel =>
    let _ ← coordinator ctx state
    if let some integration := state.integration then
      check (holds ctx integration.lease || decide (integration.lease.expires + grace < ctx.now))
        "Another live generation holds integration"
    return result { state with integration := none } "Integration cancelled; approvals preserved"

end Coordination
