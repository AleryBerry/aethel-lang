import Aethel.Litmus.Types
import Aethel.Litmus.AliasingScopes
import Aethel.Litmus.InvalidationFacts
import Aethel.Litmus.BranchJoins
import Aethel.Litmus.OwnershipTransfer
import Aethel.Litmus.ReturnedOrigins
import Aethel.Litmus.ClosuresCaptures
import Aethel.Litmus.LayoutPacking
import Aethel.Litmus.ADTMatching
import Aethel.Litmus.IterationTermination

namespace Aethel.LitmusCorpus

open Litmus

/-- The 250 Lean litmus fixtures across nine domains. -/
def allFixtures : List Fixture :=
  AliasingScopes.fixtures ++
  InvalidationFacts.fixtures ++
  BranchJoins.fixtures ++
  OwnershipTransfer.fixtures ++
  ReturnedOrigins.fixtures ++
  ClosuresCaptures.fixtures ++
  LayoutPacking.fixtures ++
  ADTMatching.fixtures ++
  IterationTermination.fixtures

theorem corpus_size : allFixtures.length = 250 := by
  rfl

def runLitmusCorpus : IO Unit := do
  let total := allFixtures.length
  if total ≠ 250 then
    throw (IO.userError s!"Expected 250 litmus programs, found {total}")

  let mut passedCount := 0
  for f in allFixtures do
    if f.passed then
      passedCount := passedCount + 1
    else
      throw (IO.userError s!"Litmus test failed: {f.name} ({f.description})")

  IO.println s!"250 Lean litmus fixtures passed across nine domains"

end Aethel.LitmusCorpus
