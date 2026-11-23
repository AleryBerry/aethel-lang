import Aethel.CoBorrowPacking
import Aethel.CacheLayout
import Aethel.ADTLayout

namespace Aethel.Phase2.Tests

open Aethel
open Aethel.AutomaticLayout
open Aethel.CoBorrowPacking
open Aethel.CacheLayout
open Aethel.ADTLayout

private def require (msg : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError msg)

private def runCoBorrowTests : IO Unit := do
  let fields : List Schema :=
    [ .integer (.unsigned .w1)
    , .integer (.unsigned .w1)
    , .integer (.unsigned .w1)
    , .integer (.unsigned .w1)
    , .integer (.unsigned .w1)
    , .integer (.unsigned .w1)
    , .integer (.unsigned .w32) ]
  -- Case 1: 0 conflicts -> all 6 u1 flags pack into 1 byte + 4-byte u32 = 8 bytes (vs 12 unpacked)
  let gFree : CoBorrowGraph := ⟨7, []⟩
  let some lFree := autoPlan .natural gFree fields
    | throw (IO.userError "conflict-free autoPlan failed")
  require "conflict-free 6x u1 + u32 packs to 8 bytes"
    (lFree.size == 8 && lFree.alignment == 4)
  -- Case 2: exclusive write/read conflict between fields 0 and 1
  let e0 : Effect := ⟨[], [[0]], []⟩
  let e1 : Effect := ⟨[[1]], [], []⟩
  let gConf := CoBorrowGraph.ofEffects 7 [(e0, e1)]
  require "CoBorrowGraph.ofEffects detects edge (0, 1)"
    (gConf.interferes 0 1 && !gConf.interferes 2 3)
  require "conflicting fields get addressable policy while unconflicting pack"
    (synthesizePolicy gConf 0 == .addressable &&
     synthesizePolicy gConf 1 == .addressable &&
     synthesizePolicy gConf 2 == .mayShareByte &&
     synthesizePolicy gConf 3 == .mayShareByte)
  let some lConf := autoPlan .natural gConf fields
    | throw (IO.userError "conflicting autoPlan failed")
  require "conflicting 2 addressable + 4 packed u1 + u32 still saves 4 bytes (8 bytes total)"
    (lConf.size == 8 && lConf.alignment == 4)
  match lConf with
  | .record _ _ placed =>
    match placed[0]?, placed[1]?, placed[2]?, placed[3]? with
    | some f0, some f1, some f2, some f3 =>
      require "conflicting fields 0 and 1 occupy distinct addressable bytes"
        (f0.1.bitOffset.isNone && f1.1.bitOffset.isNone &&
          f0.1.byteOffset != f1.1.byteOffset)
      require "non-conflicting flags 2 and 3 still pack into one shared byte"
        (f2.1.bitOffset.isSome && f3.1.bitOffset.isSome &&
          f2.1.byteOffset == f3.1.byteOffset)
    | _, _, _, _ => throw (IO.userError "unexpected field count in autoPlan result")
  | _ => throw (IO.userError "expected record layout from autoPlan")

private def runCacheLayoutTests : IO Unit := do
  let len := 20
  let fields := 3
  let table : ScalarTable := fun i f => i * 100 + f
  -- Check AoS, SoA, and Tiled AoSoA across tile widths 4, 8, 16
  for w in [4, 8, 16] do
    let aos := encodeAoS table fields
    let soa := encodeSoA table len
    let aosoa := encodeAoSoA table w fields
    for i in List.range len do
      for f in List.range fields do
        let vAos := aos (aosSlot fields i f)
        let vSoa := soa (soaSlot len i f)
        let vAoSoA := aosoa (aosoaSlot w fields i f)
        unless vAos == table i f && vSoa == table i f && vAoSoA == table i f do
          throw (IO.userError s!"three-way read mismatch at w={w} i={i} f={f}")
  -- Check unit-stride contiguity inside 8-element tile and 64-byte alignment
  for i in List.range 7 do
    for f in List.range fields do
      require "elements within a tile are contiguous in memory"
        (aosoaSlot 8 fields (i + 1) f == aosoaSlot 8 fields i f + 1)
  for tile in List.range 4 do
    for f in List.range fields do
      require "16-lane u32 tile start is 64-byte L1 cache aligned"
        ((aosoaSlot 16 fields (tile * 16) f * 4) % 64 == 0)
  -- Check ByteCollectionRep writes across all 3 collection layouts
  let bTable : Nat → Nat → UInt8 := fun i f => (i * 7 + f).toUInt8
  for lay in [CollectionLayout.aos, .soa, .aosoa 8] do
    let initBytes := (List.range 60).map fun addr =>
      match lay with
      | .aos => bTable (addr / 3) (addr % 3)
      | .soa => bTable (addr % 20) (addr / 20)
      | .aosoa w =>
        let tileSize := 3 * w
        let tile := addr / tileSize
        let rem := addr % tileSize
        bTable (tile * w + rem % w) (rem / w)
    let st0 : Core.State := ({} : Core.State).addAllocation 0 initBytes
    -- Write element 5, field 1 -> 222 and verify updated + sibling preserved
    let targetSlot := collectionSlot lay 20 3 5 1
    let st1 := st0.store ⟨0, targetSlot⟩ 222
    require "ByteCollectionRep write updates target slot"
      (st1.byte ⟨0, targetSlot⟩ == some 222)
    let sibSlot := collectionSlot lay 20 3 5 2
    require "ByteCollectionRep write preserves sibling slot"
      (st1.byte ⟨0, sibSlot⟩ == some (bTable 5 2))
  -- Check L1 cache-aware layout selector profiles
  require "small collection selects AoS"
    (selectCollectionLayout ⟨4, 2, 4, true, 4⟩ == .aos)
  require "large SIMD 4-byte field selects 16-wide AoSoA"
    (selectCollectionLayout ⟨4, 2, 1024, true, 4⟩ == .aosoa 16)
  require "large non-SIMD partial-field loop selects SoA"
    (selectCollectionLayout ⟨5, 1, 1024, false, 4⟩ == .soa)
  -- Check hot/cold field clustering
  let clustered := reorderHotFirst (fun idx => idx == 0 || idx == 3) [0, 1, 2, 3, 4]
  require "reorderHotFirst groups hot fields ahead of cold fields"
    (clustered == [0, 3, 1, 2, 4])

private def runADTLayoutTests : IO Unit := do
  -- Test all 22 valid inhabitants of statusCompactADT (1 idle + 4 moving + 16 poisoned + 1 dead)
  let mkVal (t p : Nat) (h : ∃ v ∈ statusCompactADT.variants, v.tag = t ∧ p < 2 ^ v.payloadBits) :
      CompactValue statusCompactADT := ⟨t, p, h⟩
  let idleVal := mkVal 0 0 ⟨⟨0, 0⟩, by simp [statusCompactADT], rfl, by decide⟩
  require "statusCompactADT idle round-trip"
    (statusCompactADT.decode (statusCompactADT.encode idleVal) == some (0, 0))
  for sp in List.range 4 do
    if h : sp < 4 then
      let mv := mkVal 1 sp ⟨⟨1, 2⟩, by simp [statusCompactADT], rfl, by simpa using h⟩
      require s!"statusCompactADT moving({sp}) round-trip"
        (statusCompactADT.decode (statusCompactADT.encode mv) == some (1, sp))
  for tk in List.range 16 do
    if h : tk < 16 then
      let pv := mkVal 2 tk ⟨⟨2, 4⟩, by simp [statusCompactADT], rfl, by simpa using h⟩
      require s!"statusCompactADT poisoned({tk}) round-trip"
        (statusCompactADT.decode (statusCompactADT.encode pv) == some (2, tk))
  let deadVal := mkVal 3 0 ⟨⟨3, 0⟩, by simp [statusCompactADT], rfl, by decide⟩
  require "statusCompactADT dead round-trip"
    (statusCompactADT.decode (statusCompactADT.encode deadVal) == some (3, 0))
  -- Invalid encodings rejected by decode
  require "idle with nonzero payload rejected"
    (statusCompactADT.decode 4).isNone
  require "moving with out-of-range speed=4 rejected"
    (statusCompactADT.decode (1 + 4 * 4)).isNone
  -- 3-variant and 8-variant ADT checks
  let adt3 : CompactADT := ⟨minTagBits 3, 3, [⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 3⟩]⟩
  let adt8 : CompactADT := ⟨minTagBits 8, 5, (List.range 8).map fun i => ⟨i, 5⟩⟩
  require "3-variant ADT fits in 5 bits and canShareByte"
    (adt3.totalBits == 5 && adt3.canShareByte)
  require "8-variant ADT needs 8 bits and cannot share byte"
    (adt8.totalBits == 8 && !adt8.canShareByte)

def run : IO Unit := do
  runCoBorrowTests
  runCacheLayoutTests
  runADTLayoutTests
  IO.println "Phase 2 co-borrow packing, L1 cache/Tiled-AoSoA, and compact ADT regressions passed"

end Aethel.Phase2.Tests
