import Aethel.PermissionLattice
import Aethel.MultiPathViews
import Aethel.AffineIndex
import Aethel.StatefulCore

namespace Aethel.Phase1.Tests

open Aethel
open Aethel.Core
open Aethel.Permissions
open Aethel.AutomaticLayout
open Aethel.StatefulCore
open Aethel.Representation
open Aethel.CoreAST

private def require (msg : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError msg)

private def runPermissionLatticeTests : IO Unit := do
  let base0 : Core.State := ({} : Core.State).addAllocation 0 [10, 20]
  let ps0 : PermState := { base := base0 }
  -- 1. Reserve mutable two-phase borrow and concurrent shared read on byte 0
  let some ps1 := runPerm ps0
      [ .reserve 0 ⟨0, 0⟩ .reserved
      , .reserve 1 ⟨0, 0⟩ .shared
      , .read 1 ]
    | throw (IO.userError "two-phase reserved + shared reservation should succeed")
  require "shared reader during reserved phase observes initial byte 10"
    (ps1.base.observations == [10])
  -- 2. Activating exclusive while shared reader is still alive must fail
  require "activate blocked while concurrent shared view is active"
    (execPerm ps1 (.activate 0)).isNone
  -- 3. Release shared reader, activate exclusive, write 42, verify sibling byte 1 preserved
  let some ps2 := runPerm ps1
      [ .release 1
      , .activate 0
      , .write 0 42
      , .read 0 ]
    | throw (IO.userError "activate and write after shared release should succeed")
  require "activeExclusive write updates byte 0 to 42"
    (ps2.base.observations == [42, 10] && ps2.base.byte ⟨0, 0⟩ == some 42)
  require "activeExclusive write preserves sibling byte 1"
    (ps2.base.byte ⟨0, 1⟩ == some 20)
  -- 4. Freeze demotes activeExclusive to read-only frozen
  let some ps3 := runPerm ps2 [.freeze 0, .read 0]
    | throw (IO.userError "freeze and read should succeed")
  require "write after freeze is rejected"
    (execPerm ps3 (.write 0 99)).isNone
  require "read after freeze observes 42"
    (ps3.base.observations.head? == some 42)
  -- 5. Two simultaneous reserved borrows on the same byte conflict
  require "double reserved on same byte is rejected"
    (runPerm ps0 [.reserve 2 ⟨0, 0⟩ .reserved, .reserve 3 ⟨0, 0⟩ .reserved]).isNone

private def entitySchema : Schema :=
  .record [
    (.addressable, .integer (.unsigned .w32)), -- [0] pos
    (.addressable, .integer (.unsigned .w16)), -- [1] health
    (.addressable, .integer (.unsigned .w32))  -- [2] vel
  ]

private def entityValues : List Nat → Option IntegerBits
  | [0] => some ⟨.unsigned .w32, BitVec.ofNat 32 100⟩
  | [1] => some ⟨.unsigned .w16, 500⟩
  | [2] => some ⟨.unsigned .w32, BitVec.ofNat 32 25⟩
  | _ => none

private def packedSchema : Schema :=
  .record [
    (.mayShareByte, .integer (.unsigned .w1)),
    (.mayShareByte, .integer (.unsigned .w1))
  ]

private def packedValues : List Nat → Option IntegerBits
  | [0] => some ⟨.unsigned .w1, 1⟩
  | [1] => some ⟨.unsigned .w1, 0⟩
  | _ => none

private def runMultiPathViewTests : IO Unit := do
  let some (entityRec, st0) := allocateRecord .natural entitySchema {} 0 entityValues
    | throw (IO.userError "entity record allocation failed")
  -- Disjoint multi-path borrow ~>.{pos, vel}
  let some (mv, st1) := openMultiView entityRec st0 [[0], [2]] .exclusive
    | throw (IO.userError "multi-path view on pos and vel failed")
  require "multi-path view preserves requested paths"
    (mv.paths == [[0], [2]])
  require "pos and health are byte-disjoint"
    (pathsByteDisjoint entityRec.layout [0] [1] && pathsByteDisjoint entityRec.layout [2] [1])
  -- Sibling field health ([1]) remains exclusively borrowable concurrently!
  let some (healthView, st2) := openView entityRec st1 [1] .exclusive
    | throw (IO.userError "sibling health view should remain exclusively borrowable")
  let some st3 := closeView healthView st2
    | throw (IO.userError "closing health view failed")
  let some st4 := closeMultiView mv st3
    | throw (IO.userError "closing multi-path view failed")
  require "closing multi-path and sibling views restores empty active views"
    st4.views.isEmpty
  -- Negative: two bit-packed u1 fields sharing one byte cannot take exclusive multi-view
  let some (packedRec, pst0) := allocateRecord .natural packedSchema {} 1 packedValues
    | throw (IO.userError "packed record allocation failed")
  require "exclusive multi-view on packed siblings sharing a byte is rejected"
    (openMultiView packedRec pst0 [[0], [1]] .exclusive).isNone

private def runAffineIndexTests : IO Unit := do
  let env : OrderFactEnv := {
    base := { unequal := [(.value 0, .value 5)] },
    ltFacts := [(0, 1)], -- x0 < x1
    leFacts := [(2, 3)]  -- x2 <= x3
  }
  require "affine i != i + 1"
    (env.provesNe (.value 0) (.add (.value 0) (.const 1)))
  require "affine i + 1 != i + 3"
    (env.provesNe (.add (.value 0) (.const 1)) (.add (.value 0) (.const 3)))
  require "ordered x0 < x1 proves x0 + 2 != x1 + 5"
    (env.provesNe (.add (.value 0) (.const 2)) (.add (.value 1) (.const 5)))
  require "ordered x2 <= x3 proves x2 + 1 != x3 + 2"
    (env.provesNe (.add (.value 2) (.const 1)) (.add (.value 3) (.const 2)))
  require "half-open slice split [0..mid) and [mid..len) disjoint"
    (env.slicesDisjoint ⟨.const 0, .value 0⟩ ⟨.value 0, .value 1⟩)
  require "sliding window [i..i+4) and [i+4..i+8) disjoint"
    (env.slicesDisjoint
      ⟨.value 0, .add (.value 0) (.const 4)⟩
      ⟨.add (.value 0) (.const 4), .add (.value 0) (.const 8)⟩)
  require "unrelated indices x0 and x4 are not falsely proven unequal"
    (!env.provesNe (.value 0) (.value 4))
  require "x0 < x1 does not falsely prove x0 + 5 != x1 + 1"
    (!env.provesNe (.add (.value 0) (.const 5)) (.add (.value 1) (.const 1)))
  have hNoWrap : noWrapAdd 8 200 50 := by simp [noWrapAdd]
  have hExact : (200 + 50) % 2 ^ 8 = 250 := noWrapAdd_exact hNoWrap
  let _ := hExact

private def runStatefulCoreProofTests : IO Unit := do
  -- Witness a complete well-typed stateful execution trace preserving StateWellFormed
  let s0 : Core.State := {}
  have hWf0 : StateWellFormed s0 := stateWellFormed_empty
  have hCs1 : Core.Step s0 (.alloc 0 (List.replicate 2 7)) (s0.addAllocation 0 [7, 7]) :=
    Core.Step.alloc (by simp [s0])
  have hCs2 : Core.Step (s0.addAllocation 0 [7, 7]) (.alias 0 0 0 .exclusive)
      ((s0.addAllocation 0 [7, 7]).addHandle 0 ⟨⟨0, 0⟩, .exclusive⟩) :=
    Core.Step.alias rfl rfl
  let s1 := (s0.addAllocation 0 [7, 7]).addHandle 0 ⟨⟨0, 0⟩, .exclusive⟩
  have hStepAlloc : StatefulStep s0 (.alloc 0 0 2 7) s1 (.handleVal 0) :=
    .alloc_exec 0 0 2 7 (by decide) hCs1 hCs2
  have hWf1 : StateWellFormed s1 := hStepAlloc.preserves_state_wf hWf0
  have hTypedAlloc : SWellTyped [] (.alloc 0 0 2 7) .handle := .alloc [] 0 0 2 7
  have hPresAlloc : SWellTyped [] (.handleVal 0) .handle :=
    hStepAlloc.preservation hTypedAlloc
  -- Write byte 99 through handle 0 and verify HeapRepresents + preservation
  have hHd : s1.handle 0 = some ⟨⟨0, 0⟩, .exclusive⟩ := rfl
  have hLive : s1.byte ⟨0, 0⟩ = some 7 := rfl
  have hAvail : s1.Available ⟨0, 0⟩ .exclusive none := by intro v hv; cases hv
  have hWriteCs : Core.Step s1 (.write 0 99) (s1.store ⟨0, 0⟩ 99) :=
    Core.Step.write hHd hLive (Or.inr rfl) hAvail
  let s2 := s1.store ⟨0, 0⟩ 99
  have hStepWrite : StatefulStep s1 (.writeHandle 0 (.byte 99)) s2 .unit :=
    .writeHandle_exec 0 99 hWriteCs
  have hWf2 : StateWellFormed s2 := hStepWrite.preserves_state_wf hWf1
  have hOldRep : HeapRepresents s1 0 0 (.int false 8 (Int.ofNat (7 : UInt8).toNat)) CoreType.byte :=
    ⟨[7], .byte 7, fun i hi => by
      simp only [List.length_singleton] at hi
      have hi0 : i = 0 := by omega
      subst hi0
      rfl⟩
  have hNewRep := stateful_writeHandle_heap_simulation hHd hStepWrite hOldRep
  have hErasure := stateful_erasure_simulation hStepWrite
  have _ := hWf2
  have _ := hPresAlloc
  have _ := hNewRep
  have _ := hErasure

def run : IO Unit := do
  runPermissionLatticeTests
  runMultiPathViewTests
  runAffineIndexTests
  runStatefulCoreProofTests
  IO.println "Phase 1 borrow lattice, multi-path view, affine index, and stateful core regressions passed"

end Aethel.Phase1.Tests
