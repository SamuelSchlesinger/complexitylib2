/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (repository coordination tests)

import Coordination.Protocol
import Coordination.Git

/-! Board records as checkouts that predate batch landings read and write them. Only the
reservation and completion records changed; the other records are shared with the current
protocol. -/

namespace Coordination.Tests

open Lean

/-- The reservation record of checkouts that predate batch landings. -/
structure LegacyIntegration where
  epic : EpicId
  lease : Lease
  snapshot : Snapshot
  deriving BEq, ToJson, FromJson

/-- The completion record of checkouts that predate merge landings. -/
structure LegacyCompletion where
  snapshot : Snapshot
  summary : String
  api : Review
  correctness : Review
  validation : String
  landedBy : Actor
  landedAt : Nat
  deriving BEq, ToJson, FromJson

/-- The board of checkouts that predate batch landings. Epics use the current records, which
agree with the legacy ones except for the `landed` field of completed epics; `legacyHeartbeat`
clears that field as an older checkout's rewrite does. -/
structure LegacyState where
  version : Nat := 1
  agents : List Agent := []
  epics : List Epic := []
  coordinator : Option Lease := none
  integration : Option LegacyIntegration := none
  deriving ToJson, FromJson

/-- A heartbeat of `agent` from an older checkout: it decodes the board with the legacy records,
renews the agent and writes back only the legacy fields. -/
def legacyHeartbeat (repository : Git.Repository) (agent : AgentId) : IO Unit := do
  discard <| repository.update ({} : LegacyState) "older checkout heartbeat" fun state =>
    pure ({state with
      agents := state.agents.map fun a =>
        if a.actor.agent == agent then {a with expires := a.expires + 1} else a
      epics := state.epics.map fun epic => match epic.phase with
        | .merged completed => {epic with phase := .merged {completed with landed := none}}
        | _ => epic}, none)

end Coordination.Tests
