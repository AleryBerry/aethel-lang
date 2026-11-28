import Aethel.CoBorrowPacking
import Aethel.IndexedBorrow
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
  -- Case 1: 0 conflicts -> u32 stays 4-byte aligned (defaultPackable = false), 6x u1 pack into 1 byte = 8 bytes
  let gFree : CoBorrowGraph := ⟨7, []⟩
  let some lFree := autoPlan .natural gFree fields
    | throw (IO.userError "conflict-free autoPlan failed")
  require "conflict-free 6x u1 + u32 keeps u32 aligned in 8 bytes"
    (lFree.size == 8 && lFree.alignment == 4)
  -- Case 2: exclusive write/read conflict between fields 0 and 1
  let e0 : Effect := ⟨[], [[0]], []⟩
  let e1 : Effect := ⟨[[1]], [], []⟩
  let gConf := CoBorrowGraph.ofEffects 7 [(e0, e1)]
  require "CoBorrowGraph.ofEffects detects edge (0, 1)"
    (gConf.interferes 0 1 && !gConf.interferes 2 3)
  require "conflicting fields get addressable policy, u32 stays addressable, non-conflicting sub-byte pack"
    (synthesizePolicy gConf 0 (.integer (.unsigned .w1)) == .addressable &&
     synthesizePolicy gConf 1 (.integer (.unsigned .w1)) == .addressable &&
     synthesizePolicy gConf 2 (.integer (.unsigned .w1)) == .mayShareByte &&
     synthesizePolicy gConf 3 (.integer (.unsigned .w1)) == .mayShareByte &&
     synthesizePolicy gConf 6 (.integer (.unsigned .w32)) == .addressable)
  let some lConf := autoPlan .natural gConf fields
    | throw (IO.userError "conflicting autoPlan failed")
  require "conflicting 2 addressable + 4 packed u1 + u32 fits in 8 bytes"
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
  -- Case 3: cross-byte u12 + u4 + u1 packing vs conflict / forced addressable separation
  let w12 : IntegerWidth := ⟨12, by decide, by decide⟩
  let crossFields : List Schema :=
    [ .integer (.unsigned w12)
    , .integer (.unsigned .w4)
    , .integer (.unsigned .w1) ]
  let some lCrossFree := autoPlan .natural ⟨3, []⟩ crossFields
    | throw (IO.userError "cross-byte conflict-free autoPlan failed")
  require "conflict-free u12 + u4 + u1 packs to 3 bytes with align 1"
    (lCrossFree.size == 3 && lCrossFree.alignment == 1)
  match lCrossFree with
  | .record _ _ [c0, c1, c2] =>
    require "u12 at 0:0, u4 at 1:4, u1 at 2:0"
      (c0.1 == ⟨0, some 0⟩ && c1.1 == ⟨1, some 4⟩ && c2.1 == ⟨2, some 0⟩)
  | _ => throw (IO.userError "unexpected field count in cross-byte autoPlan result")
  let some lCrossConf := autoPlan .natural ⟨3, [(0, 1)]⟩ crossFields
    | throw (IO.userError "cross-byte conflicting autoPlan failed")
  require "conflicting u12 and u4 separate into 4 bytes with align 2"
    (lCrossConf.size == 4 && lCrossConf.alignment == 2)
  let some lCrossForced := autoPlan .natural ⟨3, []⟩ crossFields [0]
    | throw (IO.userError "cross-byte forced-addressable autoPlan failed")
  require "L1-hot or address-taken u12 stays addressable in 4 bytes with align 2"
    (lCrossForced.size == 4 && lCrossForced.alignment == 2 &&
      shouldUnpackHotInL1 true (some 256) && !shouldUnpackHotInL1 true (some 65536))

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
  -- Check AoSoA(8) tiled SIMD pass + tail agrees with full 10-element sequential range
  let len10 := 10
  let fields2 := 2
  let t10 : Nat → Nat → UInt8 := fun i f => (i * 5 + f).toUInt8
  let init10 := (List.range (2 * 8 * fields2)).map fun addr =>
    let tile := addr / (fields2 * 8)
    let rem := addr % (fields2 * 8)
    let f := rem / 8
    let i := tile * 8 + rem % 8
    if i < len10 then t10 i f else 0
  let st10 : Core.State := ({} : Core.State).addAllocation 0 init10
  let simdOut := applyTiledSimdPass 0 (.aosoa 8) len10 fields2 8 0 (fun b => b + 10) st10
  let seqOut := applyRange 0 (.aosoa 8) len10 fields2 0 (fun b => b + 10) 0 len10 st10
  for i in List.range len10 do
    for f in List.range fields2 do
      let slot := collectionSlot (.aosoa 8) len10 fields2 i f
      require "applyTiledSimdPass matches sequential pass across AoSoA(8) tile + tail"
        (simdOut.byte ⟨0, slot⟩ == seqOut.byte ⟨0, slot⟩)

private def runIndexedCollectionTests : IO Unit := do
  let left : Functional.Term [.byte, .byte] .byte := .var (.there .here)
  let right : Functional.Term [.byte, .byte] .byte := .var .here
  let empty : Structured.BranchFacts [.byte, .byte] := []
  let bounded := (empty.learn (.byteLt left (.byte 3)) true).learn (.byteLt right (.byte 3)) true
  let facts := bounded.learn (.byteEq right left) false
  let env := (Functional.Env.empty.extend (ty := .byte) 0).extend (ty := .byte) 2
  let layouts : List { layout : CollectionLayout // layout.Valid } :=
    [⟨.aos, trivial⟩, ⟨.soa, trivial⟩, ⟨.aosoa 2, show 0 < 2 from by decide⟩]
  for layout in layouts do
    let collection : ByteCollection := ⟨7, layout.val, 3, 2, layout.property⟩
    let first : IndexedCell collection _ := ⟨left, 0, .exclusive⟩
    let second : IndexedCell collection _ := ⟨right, 0, .exclusive⟩
    let sibling : IndexedCell collection _ := ⟨left, 1, .exclusive⟩
    let held : IndexedCell collection _ := ⟨right, 1, .shared⟩
    let requests := [first, second, sibling]
    require "collection borrows use checked bounds, index inequality, and field separation"
      (checkIndexedBorrow facts requests &&
        !(checkIndexedBorrow bounded requests) &&
        checkIndexedBorrow bounded [first, sibling] &&
        !(checkIndexedBorrow facts [first, first]))
    require "index inequality also separates a new exclusive loan from the caller's shared loan"
      (checkScopedIndexedBorrow facts [held] requests &&
        checkIndexedBorrow bounded [sibling] &&
        !(checkScopedIndexedBorrow bounded [held] [sibling]) &&
        !(checkScopedIndexedBorrow facts [held] [{ held with mode := .exclusive }]))
    let table (row field : Nat) : UInt8 := UInt8.ofNat (13 + row * 10 + field)
    let expected : List UInt8 := match layout.val with
      | .aos => [13, 14, 23, 24, 33, 34]
      | .soa => [13, 23, 33, 14, 24, 34]
      | .aosoa _ => [13, 23, 14, 24, 33, 0, 34, 0]
    require "collection initialization uses the chosen physical layout and zeroes padding"
      (layout.val.encodeBytes 3 2 table == expected)
    let some initial := Core.run {} (collection.entry table) |
      throw (IO.userError "failed to initialize the collection borrow tests")
    let access := collection.dispatch left 1 fun handle => .read (.handle handle) .finish
    let guarded := Structured.Code.branch (.byteLt left (.byte 3)) access .finish
    require "an indexed collection load needs a dominating bound"
      (Structured.check initial.resources guarded && !(Structured.check initial.resources access))
    let some (_, loaded) := Structured.runCode env initial guarded |
      throw (IO.userError "checked indexed load failed")
    require "indexed read selects the intended field under each physical layout" (loaded.observations == [14])
    let temporary := initial.freshHandle
    let some state := Core.run initial
      [.alloc 8 [19], .alias temporary 8 0 .shared, .reserve 0 temporary .shared,
        .forget temporary, .reserve 1 (held.location env).offset .shared] |
      throw (IO.userError "failed to install the caller's views")
    let loans := Core.indexedViews state.freshView (indexedBorrowCells env requests)
    let entered := Core.acquireViews state.freshHandle loans
    let start := state.freshView
    let writes : Core.Program := [.writeView start 73, .writeView (start + 1) 91, .writeView (start + 2) 54]
    let some after := Core.run state (entered ++ writes ++ Core.releaseViews (loans.reverse.map Core.View.id)) |
      throw (IO.userError "valid indexed collection borrows failed in the byte machine")
    require "indexed stores update only their physical cells and restore caller loans"
      (after.byte (first.location env) == some 73 && after.byte (second.location env) == some 91 &&
        after.byte (sibling.location env) == some 54 &&
        after.byte (held.location env) == some 34 &&
        decide (after.resources = state.resources))

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
  require "17 variants require five tag bits and 257 variants require nine"
    (minTagBits 17 == 5 && minTagBits 257 == 9)

  let saturated : Sum (Fin 255) (Fin 1) := .inl 254
  let vacant : Sum (Fin 255) (Fin 1) := .inr 0
  require "255 payload values leave one byte code for the empty variant"
    ((packDenseSum saturated).toNat == 254 && (packDenseSum vacant).toNat == 255 &&
      unpackDenseSum 255 1 (packDenseSum vacant) == some vacant)
  require "unused dense codes and the uninhabited sum have no decoding"
    ((unpackDenseSum 2 1 (BitVec.ofNat 2 3)).isNone &&
      (unpackDenseSum 0 0 (BitVec.ofNat 0 0)).isNone)
  let field : DenseSumField 2 2 1 := ⟨7, by decide⟩
  let initial : AutomaticLayout.Image 2 := fun _ => BitVec.ofNat 8 255
  let changed := field.store initial (.inr 0)
  require "cross-byte dense variant store preserves both neighboring bit ranges"
    (field.load changed == some (.inr 0) &&
      (changed.readBits 0 7).toNat == 127 && (changed.readBits 9 7).toNat == 127)

def run : IO Unit := do
  runCoBorrowTests
  runCacheLayoutTests
  runIndexedCollectionTests
  runADTLayoutTests
  IO.println "Phase 2 co-borrow packing, L1 cache/Tiled-AoSoA, and compact ADT regressions passed"

end Aethel.Phase2.Tests
