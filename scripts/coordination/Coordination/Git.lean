/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (project coordination tooling)
import Lean

/-! Git transport for the coordination journal. It never uses a worktree's index or
`FETCH_HEAD`. Updates are ordinary fast-forward pushes; landing couples the journal
update to an exactly guarded fast-forward of `main` in one atomic transaction. -/

namespace Coordination.Git

open Lean

/-- Argument-array process boundary, also used by fault-injection tests. -/
abbrev Runner := Array String → Option String → IO IO.Process.Output

structure Repository where
  root : System.FilePath
  remote : String := "origin"
  execute : Runner

def Repository.open (root : System.FilePath) (remote := "origin") : IO Repository := do
  unless !remote.isEmpty && remote.toList.all (fun c => c.isAlphanum || c == '-' ||
      c == '_' || c == '.') && !(remote.startsWith "-") do
    throw <| IO.userError "Invalid remote name"
  let root ← IO.FS.realPath root
  return { root, remote, execute := fun args input =>
    IO.Process.output { cmd := "git", args := #["-C", root.toString] ++ args } input }

def Repository.run (repo : Repository) (args : Array String)
    (input : Option String := none) : IO String := do
  let result ← repo.execute args input
  unless result.exitCode == 0 do
    throw <| IO.userError s!"git failed: {result.stderr}{result.stdout}"
  return result.stdout

/-- Trim only Git's line terminator; never use on NUL-delimited path lists. -/
def line (s : String) : String := s.dropEndWhile (· == '\n') |>.toString

def nonce : IO String := do
  let bytes ← IO.getRandomBytes 16
  return String.join <| bytes.data.toList.map (fun b =>
    let digits := "0123456789abcdef".toList.toArray
    String.ofList [digits[b.toNat / 16]!, digits[b.toNat % 16]!])

def Repository.fetch (repo : Repository) (ref : String)
    (required := true) : IO (Option String) := do
  let listed ← repo.execute #["ls-remote", "--exit-code", repo.remote, ref] none
  if listed.exitCode == 2 && !required then return none
  unless listed.exitCode == 0 do
    throw <| IO.userError s!"Cannot read {ref}: {listed.stderr}"
  let temporary := "refs/coordination-fetch/" ++ (← nonce)
  try
    -- An explicit destination still permits configured tracking-ref updates unless refmap is empty.
    discard <| repo.run #["fetch", "--quiet", "--no-tags", "--no-write-fetch-head",
      "--refmap=", repo.remote, s!"{ref}:{temporary}"]
    return some <| line (← repo.run #["rev-parse", "--verify", temporary ++ "^{commit}"])
  finally
    discard <| repo.execute #["update-ref", "-d", temporary] none

def Repository.ancestor (repo : Repository) (older newer : String) : IO Bool := do
  let result ← repo.execute #["merge-base", "--is-ancestor", older, newer] none
  if result.exitCode == 0 then return true
  if result.exitCode == 1 then return false
  throw <| IO.userError result.stderr

def Repository.head (repo : Repository) : IO String :=
  line <$> repo.run #["rev-parse", "HEAD"]

def Repository.clean (repo : Repository) (head : String) : IO Unit := do
  unless (← repo.head) == head do
    throw <| IO.userError "Worktree HEAD differs from the reviewed commit"
  unless (← repo.run #["--no-optional-locks", "status", "--porcelain"]).isEmpty do
    throw <| IO.userError "Use a clean, dedicated worktree"

def Repository.changedPaths (repo : Repository) (base head : String) : IO (List String) := do
  -- Disabling rename detection reports both old and new paths, preserving scope checks.
  let paths ← repo.run #["diff", "--name-only", "--no-renames", "-z", base, head]
  return (paths.splitOn "\x00").dropLast

def boardRef : String := "refs/heads/coordination"
def mainRef : String := "refs/heads/main"

structure Landing where
  base : String
  head : String
  deriving BEq

def Repository.readBoard (repo : Repository) (required := true) :
    IO (Option (String × Json)) := do
  let some head ← repo.fetch boardRef required | return none
  unless (← repo.run #["ls-tree", "--name-only", "-z", head]) == "state.json\x00" do
    throw <| IO.userError "Unexpected coordination tree; refusing to replace it"
  let state ← IO.ofExcept <| Json.parse (← repo.run #["show", head ++ ":state.json"])
  return some (head, state)

/-- Optimistic journal transaction. Each retry reruns all preconditions on fresh state.
A landing's expected main OID is checked by Git, even if main moves to an ancestor of
the candidate between validation and push. Unsupported atomic pushes fail closed. -/
def Repository.update {α : Type} [FromJson α] [ToJson α] (repo : Repository) (initial : α)
    (description : String) (edit : α → IO (α × Option Landing))
    (allowInit := false) : IO α := do
  let operation ← nonce
  for _ in [:8] do
    let previous ← repo.readBoard (!allowInit)
    let old ← match previous with
      | none => pure initial
      | some (_, json) => IO.ofExcept (fromJson? json)
    let (state, landing) ← edit old
    let encoded := (toJson state).pretty
    if previous.isSome && encoded == (toJson old).pretty && landing.isNone then return state
    let blob := line (← repo.run #["hash-object", "-w", "--stdin"] (some (encoded ++ "\n")))
    let tree := line (← repo.run #["mktree"] (some s!"100644 blob {blob}\tstate.json\n"))
    let parents := previous.toArray.flatMap (fun (head, _) => #["-p", head])
    let commit := line (← repo.run (#["commit-tree", tree] ++ parents)
      (some s!"chore(coordination): {description}\n\nOperation: {operation}\n"))
    let mut args := #["push", "--porcelain"]
    let mut refs := #[s!"{commit}:{boardRef}"]
    if let some landing := landing then
      unless (← repo.ancestor landing.base landing.head) do
        throw <| IO.userError "Landing must be a fast-forward"
      args := args ++ #["--atomic", s!"--force-with-lease={mainRef}:{landing.base}"]
      refs := refs.push s!"{landing.head}:{mainRef}"
    let pushed ← repo.execute (args ++ #[repo.remote] ++ refs) none
    if pushed.exitCode == 0 then return state
    let current ← repo.readBoard false
    -- A failed connection may have hidden an already accepted atomic transaction.
    if let some (head, _) := current then
      if ← repo.ancestor commit head then return state
    if current.map Prod.fst == previous.map Prod.fst then
      throw <| IO.userError s!"Push rejected: {pushed.stderr}{pushed.stdout}"
  throw <| IO.userError "Coordination branch stayed busy after eight retries; retry"

end Coordination.Git
