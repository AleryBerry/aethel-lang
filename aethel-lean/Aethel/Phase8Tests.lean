import Aethel.DynamicMemory
import Aethel.SegmentedAoSoA
import Aethel.StdContainers
import Aethel.MIRValidator

namespace Aethel.Phase8.Tests

open Aethel Aethel.Core Aethel.CacheLayout Aethel.DynamicMemory Aethel.StdContainers Aethel.MIRValidator

private def require (msg : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError msg)

private def runDynamicMemoryTests : IO Unit := do
  require "initial growCap 0 == 8" (growCap 0 == 8)
  require "double growCap 8 == 16" (growCap 8 == 16)
  require "aosoaTileCap 8 10 == 2" (aosoaTileCap 8 10 == 2)

  let stFree : Core.State := { allocations := [⟨0, [1, 2, 3, 4]⟩], issued := [0] }
  require "unreserved owner permits realloc/drop" (checkUnreserved stFree 0)

  let stPinned : Core.State :=
    { allocations := [⟨0, [1, 2, 3, 4]⟩], views := [⟨9, ⟨0, 1⟩, .shared⟩], issued := [0] }
  require "active view blocks realloc/drop" (!checkUnreserved stPinned 0)

  -- Three-way Perceus in-place push + migration across AoS, DynSoA, DynAoSoA(8)
  let initTbl : ScalarTable := fun _ _ => 0
  let row0 : Nat → Nat := fun f => f + 10
  let row1 : Nat → Nat := fun f => f + 20
  for lay in [CollectionLayout.aos, CollectionLayout.soa, CollectionLayout.aosoa 8] do
    let s0 : SlotStore := fun _ => 0
    let s1 := pushSlotInPlace lay 8 2 0 row0 s0
    let s2 := pushSlotInPlace lay 8 2 1 row1 s1
    require "in-place push writes row0 and row1"
      (s2 (dynVecSlot lay 8 2 0 0) == 10 &&
       s2 (dynVecSlot lay 8 2 0 1) == 11 &&
       s2 (dynVecSlot lay 8 2 1 0) == 20 &&
       s2 (dynVecSlot lay 8 2 1 1) == 21)
    let mig := migrateStore lay 8 16 2 2 s2 (fun _ => 0)
    require "realloc migration preserves all slots across growCap"
      (mig (dynVecSlot lay 16 2 0 0) == 10 &&
       mig (dynVecSlot lay 16 2 0 1) == 11 &&
       mig (dynVecSlot lay 16 2 1 0) == 20 &&
       mig (dynVecSlot lay 16 2 1 1) == 21)
    let _ := initTbl

  require "autoScopeDrop unmoved emits destroy" (emitScopeDrop false 3 == [.destroy 3])
  require "autoScopeDrop moved emits empty" (emitScopeDrop true 3 == [])

private def runSegmentedGrowthTests : IO Unit := do
  let row (value : UInt8) : SegmentedAoSoA.Row := fun field => value + UInt8.ofNat field
  let some (initial, one) := SegmentedAoSoA.push {} {} 2 2 0 (row 17)
    | throw (IO.userError "segmented growth allocates its first tile")
  for mode in [AccessMode.shared, .exclusive] do
    let some borrowed := Core.run initial [.alias 0 0 0 .exclusive, .reserve 0 0 mode]
      | throw (IO.userError "borrow an earlier row before append")
    let some (inTile, two) := SegmentedAoSoA.push borrowed one 2 2 1 (row 23)
      | throw (IO.userError "append to a spare lane with a live view")
    require "spare-lane append preserves the original view and initializes both fields"
      (two.tiles == #[0] && inTile.issued == [0] &&
        (execute inTile (.readView 0)).map State.observations == some [17] &&
        SegmentedAoSoA.get inTile two 2 2 1 0 == some 23 &&
        SegmentedAoSoA.get inTile two 2 2 1 1 == some 24)
    require "growth rejects a previously issued tile owner"
      ((SegmentedAoSoA.push inTile two 2 2 0 (row 42)).isNone)
    let some (grown, three) := SegmentedAoSoA.push inTile two 2 2 1 (row 42)
      | throw (IO.userError "append at a tile boundary with a live view")
    require "new-tile append preserves the original view and initializes the new row"
      (three.tiles == #[0, 1] && three.length == 3 &&
        (execute grown (.readView 0)).map State.observations == some [17] &&
        SegmentedAoSoA.get grown three 2 2 1 1 == some 24 &&
        SegmentedAoSoA.get grown three 2 2 2 1 == some 43)
    require "active views still block conflicting writes and destruction"
      ((execute grown (.write 0 99)).isNone && (execute grown (.destroy 0)).isNone)
    if mode == .exclusive then
      require "exclusive view still authorizes mutation after growth"
        ((execute grown (.writeView 0 99)).bind (fun state =>
          SegmentedAoSoA.get state three 2 2 0 0) == some 99)
  let some pinnedLane := Core.run initial [.alias 1 0 1 .exclusive, .reserve 1 1 .shared]
    | throw (IO.userError "reserve a spare byte through the raw byte machine")
  require "append rejects a write to a reserved spare byte"
    ((SegmentedAoSoA.push pinnedLane one 2 2 1 (row 23)).isNone)
  let some retired := Core.run {} [.alloc 6 [], .destroy 6]
    | throw (IO.userError "retire an allocation before append")
  require "growth rejects a retired allocation identity"
    ((SegmentedAoSoA.push retired {} 2 2 6 (row 17)).isNone)

private def runStdContainerTests : IO Unit := do
  require "SwissTable load 14/16 valid" (checkSwissLoad 14 16)
  require "SwissTable load 15/16 exceeds 7/8" (!checkSwissLoad 15 16)

  let m0 : FlatMap Nat Nat := FlatMap.empty
  let m1 := m0.insert 42 100
  let m2 := m1.insert 7 200
  let m3 := m2.remove 42
  require "FlatMap insert/lookup/remove semantics"
    (m2.lookup 42 == some 100 && m2.lookup 7 == some 200 &&
     m3.lookup 42 == none && m3.lookup 7 == some 200)

  let d0 : RingDeque Nat := RingDeque.empty
  let d1 := (d0.pushBack 10).pushBack 20
  let d2 := d1.pushFront 5
  require "RingDeque pushFront/popFront FIFO order"
    (match d2.popFront with
     | some (x, rest) => x == 5 && rest.popBack.map Prod.fst == some 20
     | none => false)
  require "ringIndex wraps within capacity" (ringIndex 14 16 3 == 1)

private def runDynVecMIRTests : IO Unit := do
  let validMir :=
    "mir_version 1\n" ++
    "dyn_vec Particles aosoa 8 3 8\n" ++
    "fn dyn_realloc_ok\n" ++
    "  alloc 0 8\n" ++
    "  alloc 1 16\n" ++
    "  destroy 0\n" ++
    "  destroy 1\n" ++
    "end_fn\n"
  match validateMIRText validMir with
  | .ok cert =>
    require "dyn_vec + realloc MIR accepted" (cert.functionCount == 1)
  | .error e =>
    throw (IO.userError s!"expected valid dyn_vec MIR, got error: {e}")

  let badReallocMir :=
    "mir_version 1\n" ++
    "dyn_vec Particles soa 2 8\n" ++
    "fn realloc_with_active_view\n" ++
    "  alloc 0 8\n" ++
    "  alias 0 0 0 shared\n" ++
    "  reserve 0 0 shared\n" ++
    "  destroy 0\n" ++
    "end_fn\n"
  match validateMIRText badReallocMir with
  | .ok _ => throw (IO.userError "expected realloc under active view to be rejected")
  | .error _ => pure ()

def run : IO Unit := do
  runDynamicMemoryTests
  runSegmentedGrowthTests
  runStdContainerTests
  runDynVecMIRTests

end Aethel.Phase8.Tests
