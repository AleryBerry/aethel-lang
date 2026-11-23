import Aethel.BorrowGraph

namespace Aethel.BorrowGraph.Tests

def runBorrowGraphTests : IO Unit := do
  -- Test 1: Empty graph covers empty loan list
  let emptyGraph : BorrowSummary Nat := ⟨3, fun _ _ => .empty⟩
  if !emptyGraph.checkCovers [] then
    throw (IO.userError "empty graph should cover empty loan list")

  -- Test 2: Single-edge graph coverage
  let g0 : BorrowSummary Nat := BorrowSummary.refl 3
  let g1 := g0.addEdge 0 1 (.atom 10)
  let l1 : Loan Nat := ⟨0, 1, [10]⟩
  let lInvalid : Loan Nat := ⟨0, 1, [20]⟩
  if !g1.checkCovers [l1] then
    throw (IO.userError "g1 should cover loan [10]")
  if g1.checkCovers [lInvalid] then
    throw (IO.userError "g1 should reject loan [20]")

  -- Test 3: Add edge preserves existing loan
  let g2 := g1.addEdge 1 2 (.atom 20)
  if !g2.checkCovers [l1] then
    throw (IO.userError "g2 should still cover existing loan l1")

  -- Test 4: Add edge creates transitive path
  let lTransitive : Loan Nat := ⟨0, 2, [10, 20]⟩
  if !g2.checkCovers [lTransitive] then
    throw (IO.userError "g2 should cover transitive loan [10, 20]")

  -- Test 5: Release node makes it outbound safe
  let g3 := g2.releaseNode 0
  if !g3.checkOutbound 0 then
    throw (IO.userError "released node 0 should be outbound safe")

  -- Test 6: Release node preserves unrelated paths
  let lUnrelated : Loan Nat := ⟨1, 2, [20]⟩
  if !g3.checkCovers [lUnrelated] then
    throw (IO.userError "unrelated path 1 -> 2 should be preserved after releasing node 0")

  -- Test 7: OutboundSafe source with no loans is write safe
  if g3.checkCovers [l1] then
    throw (IO.userError "g3 should have cleared loan from node 0")

  -- Test 8: Disjoint path head write safety test
  let pWrite := [1, 2]
  let pBorrow := [2, 3]
  let hDisjoint := paths_head_ne_writeSafe (by decide : 1 ≠ 2)
  have _hSafety : ¬ (pWrite <+: pBorrow ∨ pBorrow <+: pWrite) := hDisjoint

  -- Test 9: Whole-variable borrow conflict
  have _hConflict : ([] : List Nat) <+: [1, 2] := whole_variable_borrow_conflicts [1, 2]

  -- Test 10: Multi-hop loan chain
  let gBase : BorrowSummary Nat := BorrowSummary.refl 4
  let gStep1 := gBase.addEdge 0 1 (.atom 1)
  let gStep2 := gStep1.addEdge 1 2 (.atom 2)
  let gStep3 := gStep2.addEdge 2 3 (.atom 3)
  let lChain : Loan Nat := ⟨0, 3, [1, 2, 3]⟩
  if !gStep3.checkCovers [lChain] then
    throw (IO.userError "chained edge additions should cover [1, 2, 3]")

  IO.println "10 borrow graph coverage, edge transfer, and write safety regressions passed"

end Aethel.BorrowGraph.Tests
