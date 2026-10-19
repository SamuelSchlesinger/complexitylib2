/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (project coordination tooling)
import Coordination.Runtime

open Lean Coordination Coordination.Git Coordination.Runtime

private def usage : String := "Git coordination for Complexitylib (Lean executable)

  scripts/coordinate init
  scripts/coordinate join NAME [--coordinator] [--here] [--takeover] [--minutes N]
  scripts/coordinate status [--json]
  scripts/coordinate heartbeat
  scripts/coordinate release-coordinator
  scripts/coordinate plan EPIC GOAL PATH... [--after DEPENDENCY...]
  scripts/coordinate revise EPIC GOAL [ADDITIONAL_PATH...]
  scripts/coordinate instruct EPIC TEXT
  scripts/coordinate assign EPIC WORKER [work|api|correctness] [--replace]
  scripts/coordinate start EPIC [work|api|correctness]
  scripts/coordinate note EPIC work|api|correctness TEXT [--blocked]
  scripts/coordinate ready EPIC SUMMARY
  scripts/coordinate review EPIC api|correctness BASE HEAD approve|changes NOTE
  scripts/coordinate reopen EPIC REASON
  scripts/coordinate unassign EPIC REASON
  scripts/coordinate cancel
  scripts/coordinate land EPIC...

Coordinator: plan, revise, instruct, assign, reopen, unassign, cancel, land, release-coordinator.
Workers: commit and push the assigned branch before ready; never push main.
Global options: --repo PATH, --remote NAME (before the command).
"

private def kind (s : String) : IO AssignmentKind :=
  IO.ofExcept <| match s with
  | "work" => .ok .work
  | "api" => .ok .api
  | "correctness" => .ok .correctness
  | _ => .error "Expected work, api or correctness"

private def reviewKind (s : String) : IO ReviewKind :=
  IO.ofExcept <| match s with
  | "api" => .ok .api
  | "correctness" => .ok .correctness
  | _ => .error "Expected api or correctness"

private def verdict (s : String) : IO Verdict :=
  IO.ofExcept <| match s with
  | "approve" => .ok .approve
  | "changes" => .ok .changes
  | _ => .error "Expected approve or changes"

private def reviewStatus : ReviewSlot → String
  | .unassigned => "unassigned"
  | .assigned agent => s!"{agent.value}: assigned"
  | .active lease report blocked =>
    s!"{lease.holder.agent.value}: {if blocked then "blocked" else "reviewing"} {report}"
  | .finished review =>
    s!"{review.reviewer.agent.value}: {reprStr review.verdict}; {review.note}"

private def dashboard (state : State) : IO Unit := do
  let current ← now
  match state.coordinator with
  | none => IO.println "Coordinator: unassigned"
  | some lease => IO.println s!"Coordinator: {lease.holder.agent.value}{
      if current > lease.expires then " (expired)" else ""}"
  IO.println "Agents:"
  for agent in state.agents do
    IO.println s!"  {agent.actor.agent.value}: {reprStr agent.role}, {
      if current > agent.expires then "expired" else "active"}"
  IO.println "Epics:"
  for epic in state.epics do
    IO.println s!"  {epic.id.value}: {epic.goal}"
    IO.println s!"    scope: {String.intercalate ", " epic.paths}"
    unless epic.report.isEmpty do IO.println s!"    coordinator: {epic.report}"
    match epic.phase with
    | .unassigned => IO.println "    unassigned"
    | .working work =>
      IO.println s!"    {work.assignee.value}: {
        if work.blocked then "blocked" else if work.lease.isSome then "active" else "assigned"}"
      IO.println s!"    branch: {work.branch}; {work.report}"
      if let some resume := work.resume then IO.println s!"    continues: {resume}"
    | .submitted submitted =>
      IO.println s!"    submitted: {submitted.work.branch} @ {submitted.snapshot.head.value}"
      IO.println s!"    base: {submitted.snapshot.base.value}"
      IO.println s!"    {submitted.summary}"
      IO.println s!"    api: {reviewStatus submitted.reviews.api}"
      IO.println s!"    correctness: {reviewStatus submitted.reviews.correctness}"
    | .merged completed =>
      let landed := match completed.landed with
        | some landed => if landed == completed.snapshot.head then "" else s!" as {landed.value}"
        | none => ""
      IO.println s!"    merged: {completed.snapshot.head.value}{landed}; {completed.validation}"

private structure JoinOptions where
  role : Role := .worker
  here : Bool := false
  takeover : Bool := false
  minutes : Nat := 240

private def joinOptions : List String → JoinOptions → Except String JoinOptions
  | [], options => .ok options
  | "--coordinator" :: rest, options => joinOptions rest { options with role := .coordinator }
  | "--here" :: rest, options => joinOptions rest { options with here := true }
  | "--takeover" :: rest, options => joinOptions rest { options with takeover := true }
  | "--minutes" :: value :: rest, options => do
    let some minutes := value.toNat? | throw "Minutes must be a natural number"
    joinOptions rest { options with minutes }
  | _, _ => .error "Unknown join option; use --help"

private def command (repo : Repository) (args : List String) : IO Unit := do
  let outcome ← match args with
  | [] | ["--help"] | ["help"] => IO.println usage; return
  | ["init"] =>
    discard <| repo.update ({} : State) "initialize board" (fun state => do
      unless state.version == 1 do throw <| IO.userError "Unsupported coordination schema"
      return (state, none)) true
    IO.println "Coordination branch initialized"; return
  | "join" :: name :: options =>
    let options ← IO.ofExcept <| joinOptions options {}
    let path ← join repo ⟨name⟩ options.role options.here options.takeover (options.minutes * 60)
    IO.println s!"Registered {name}. Work inside: {path}"; return
  | ["status"] => dashboard (← readState repo); return
  | ["status", "--json"] => IO.println ((toJson (← readState repo)).pretty); return
  | ["heartbeat"] => run repo .heartbeat
  | ["release-coordinator"] => releaseCoordinator repo
  | "plan" :: id :: goal :: remaining =>
    let (paths, after) := remaining.span (· != "--after")
    run repo (.plan ⟨id⟩ goal paths (after.drop 1 |>.map EpicId.mk))
  | "revise" :: id :: goal :: addPaths => run repo (.revise ⟨id⟩ goal addPaths)
  | ["instruct", id, text] => run repo (.instruct ⟨id⟩ text)
  | "assign" :: id :: worker :: options =>
    let replace := options.contains "--replace"
    let kinds := options.filter (· != "--replace")
    let selected ← match kinds with
      | [] => pure .work
      | [value] => kind value
      | _ => throw <| IO.userError "Expected one assignment kind"
    run repo (.assign ⟨id⟩ ⟨worker⟩ selected replace)
  | ["start", id] => start repo ⟨id⟩ .work
  | ["start", id, selected] => start repo ⟨id⟩ (← kind selected)
  | ["note", id, selected, text] => run repo (.note ⟨id⟩ (← kind selected) text false)
  | ["note", id, selected, text, "--blocked"] => run repo (.note ⟨id⟩ (← kind selected) text true)
  | ["ready", id, summary] => ready repo ⟨id⟩ summary
  | ["review", id, selected, base, head, result, note] =>
    let submitted ← submission (← readState repo) ⟨id⟩
    unless submitted.snapshot.base.value == base && submitted.snapshot.head.value == head do
      throw <| IO.userError "The submitted base or head changed; review the current snapshot"
    run repo (.review ⟨id⟩ (← reviewKind selected) submitted.snapshot (← verdict result) note)
  | ["reopen", id, reason] => run repo (.reopen ⟨id⟩ reason)
  | ["unassign", id, reason] => run repo (.unassign ⟨id⟩ reason)
  | ["cancel"] => run repo .cancel
  | "land" :: ids@(_ :: _) => land repo (ids.map EpicId.mk)
  | _ => throw <| IO.userError "Unrecognized command; use scripts/coordinate --help"
  IO.println outcome.message

private def options (args : List String) (root : System.FilePath := ".") (remote := "origin") :
    IO Unit := do
  match args with
  | "--repo" :: path :: rest => options rest path remote
  | "--remote" :: name :: rest => options rest root name
  | rest =>
    let repo ← Repository.open root remote
    match rest with
    | [] | ["help"] | ["--help"] | "status" :: _ | "join" :: _ => command repo rest
    | _ => withLock repo (command repo rest)

def main (args : List String) : IO UInt32 := do
  try
    options args
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"coordination: {error}"
    return 1
