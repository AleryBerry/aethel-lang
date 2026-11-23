import Aethel.CategoricalLNL
import Aethel.CategoricalFusion
import Aethel.CategoricalCombinators

namespace Aethel.Phase3.Tests

open Aethel
open Aethel.Core
open Aethel.AutomaticLayout
open Aethel.CacheLayout
open Aethel.CategoricalLNL
open Aethel.CategoricalFusion
open Aethel.CategoricalCombinators

private def require (msg : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError msg)

private def runLNLAndLensTests : IO Unit := do
  -- 1. LNL linear/non-linear proof witnesses
  have hDupCopy := copyable_pair_dup_accepted
  have hRejAff := affine_handle_dup_rejected
  have hRejLam := reusable_lam_cannot_capture_handle
  have hAccOnce := onceClosure_captures_handle_accepted
  have hRejDouble := onceClosure_double_call_rejected
  have hRejLamOnce := reusable_lam_cannot_capture_onceClosure
  have hAccViewOnce := onceClosure_captures_view_accepted
  have hDropOnce := onceClosure_unused_drop_accepted
  have hCartDup : CtxSplit [(0, .byte), (1, .bool)] [(0, .byte), (1, .bool)] [(0, .byte), (1, .bool)] :=
    CtxSplit.cartesian_dup (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> rfl)
  have _ := hDupCopy
  have _ := hRejAff
  have _ := hRejLam
  have _ := hAccOnce
  have _ := hRejDouble
  have _ := hRejLamOnce
  have _ := hAccViewOnce
  have _ := hDropOnce
  have _ := hCartDup

  -- 2. Byte-level Lens laws on Core.State
  let s0 : Core.State := ({} : Core.State).addAllocation 0 [10, 20]
  let l0 : ByteLocation := ⟨0, 0⟩
  let l1 : ByteLocation := ⟨0, 1⟩
  require "byte lens Put-Get" ((s0.store l0 55).byte l0 == some 55)
  require "byte lens Get-Put"
    ((s0.store l0 10).byte l0 == s0.byte l0 && (s0.store l0 10).byte l1 == s0.byte l1)
  require "byte lens Put-Put"
    (((s0.store l0 55).store l0 77).byte l0 == (s0.store l0 77).byte l0)
  require "byte lens Disjoint-Commute"
    (((s0.store l0 55).store l1 88).byte l0 == ((s0.store l1 88).store l0 55).byte l0 &&
     ((s0.store l0 55).store l1 88).byte l1 == ((s0.store l1 88).store l0 55).byte l1)

  -- 3. Bit-packed record leaf Lens laws (u4 + u4 + u1)
  let schema : Schema := .record
    [ (.mayShareByte, .integer (.unsigned .w4))
    , (.mayShareByte, .integer (.unsigned .w4))
    , (.mayShareByte, .integer (.unsigned .w1)) ]
  let some planned := planVerified .natural schema
    | throw (IO.userError "packed lens schema planning failed")
  let some f0 := resolveInteger planned.property [0]
    | throw (IO.userError "resolve [0] failed")
  let some f1 := resolveInteger planned.property [1]
    | throw (IO.userError "resolve [1] failed")
  let some f2 := resolveInteger planned.property [2]
    | throw (IO.userError "resolve [2] failed")
  if h0 : f0.kind = .unsigned .w4 then
    if h1 : f1.kind = .unsigned .w4 then
      if h2 : f2.kind = .unsigned .w1 then
        let img0 : Image planned.val.size := fun _ => BitVec.ofNat 8 0
        let v0 : BitVec f0.kind.bits := h0 ▸ BitVec.ofNat 4 9
        let v1 : BitVec f1.kind.bits := h1 ▸ BitVec.ofNat 4 5
        let v2 : BitVec f2.kind.bits := h2 ▸ BitVec.ofNat 1 1
        let imgA := f2.set (f1.set (f0.set img0 v0) v1) v2
        let imgB := f0.set (f2.set (f1.set img0 v1) v2) v0
        require "bit-packed leaf lenses commute across nibbles and flags"
          (f0.get imgA == v0 && f1.get imgA == v1 && f2.get imgA == v2 &&
           f0.get imgB == v0 && f1.get imgB == v1 && f2.get imgB == v2)
        let imgGetPut := f0.set imgA (f0.get imgA)
        require "bit-packed leaf Get-Put preserves all siblings"
          (f0.get imgGetPut == v0 && f1.get imgGetPut == v1 && f2.get imgGetPut == v2)
      else throw (IO.userError "unexpected kind at [2]")
    else throw (IO.userError "unexpected kind at [1]")
  else throw (IO.userError "unexpected kind at [0]")

private def initBuffer (lay : CollectionLayout) (len fields : Nat) (bTable : Nat → Nat → UInt8) :
    Core.State :=
  let bytes := (List.range (len * fields)).map fun addr =>
    match lay with
    | .aos => bTable (addr / fields) (addr % fields)
    | .soa => bTable (addr % len) (addr / len)
    | .aosoa w =>
      let tileSize := fields * w
      let tile := addr / tileSize
      let rem := addr % tileSize
      bTable (tile * w + rem % w) (rem / w)
  ({} : Core.State).addAllocation 0 bytes

private def runFusionTests : IO Unit := do
  let len := 20
  let fields := 3
  let bTable : Nat → Nat → UInt8 := fun i f => (i * 5 + f).toUInt8
  let fn1 : UInt8 → UInt8 := fun b => b + 1
  let fn2 : UInt8 → UInt8 := fun b => b * 2
  for lay in [CollectionLayout.aos, .soa, .aosoa 8] do
    let st0 := initBuffer lay len fields bTable
    let stId := mapFieldInPlace 0 lay len fields 0 id st0
    let stTwoPass := mapFieldInPlace 0 lay len fields 0 fn2 (mapFieldInPlace 0 lay len fields 0 fn1 st0)
    let stFused := mapFieldInPlace 0 lay len fields 0 (fn2 ∘ fn1) st0
    let stSeq2 := mapFieldInPlace 0 lay len fields 2 fn2 (mapFieldInPlace 0 lay len fields 0 fn1 st0)
    let stSwap2 := mapFieldInPlace 0 lay len fields 0 fn1 (mapFieldInPlace 0 lay len fields 2 fn2 st0)
    let stDual := mapTwoFieldsInPlace 0 lay len fields 0 2 fn1 fn2 st0
    for i in List.range len do
      for f in List.range fields do
        let loc : ByteLocation := ⟨0, collectionSlot lay len fields i f⟩
        require "functor identity law" (stId.byte loc == st0.byte loc)
        require "functor pipeline fusion law" (stTwoPass.byte loc == stFused.byte loc)
        require "disjoint field commute law" (stSeq2.byte loc == stSwap2.byte loc)
        require "dual-field single-pass fusion law" (stDual.byte loc == stSeq2.byte loc)
    -- Map-fold deforestation check
    let stAdd3 := mapFieldInPlace 0 lay len fields 1 (fun b => b + 3) st0
    let foldAfter := foldField 0 lay len fields 1 (0 : Nat) (fun acc b => acc + b.toNat) stAdd3
    let foldFused := foldField 0 lay len fields 1 (0 : Nat) (fun acc b => acc + (b + 3).toNat) st0
    require "map-fold deforestation matches" (foldAfter == foldFused)
    -- 3-stage pipeline fusion & fold deforestation
    let stages : List (UInt8 → UInt8) := [fn1, fn2, fun b => b + 7]
    let stPipe := runPipeline 0 lay len fields 0 stages st0
    let stPipeSingle := mapFieldInPlace 0 lay len fields 0 (composeStages stages) st0
    for i in List.range len do
      for f in List.range fields do
        let loc : ByteLocation := ⟨0, collectionSlot lay len fields i f⟩
        require "3-stage pipeline fusion matches" (stPipe.byte loc == stPipeSingle.byte loc)
    let foldPipe := foldField 0 lay len fields 0 (0 : Nat) (fun acc b => acc + b.toNat) stPipe
    let foldPipeDef := foldField 0 lay len fields 0 (0 : Nat) (fun acc b => acc + (composeStages stages b).toNat) st0
    require "3-stage pipeline-fold deforestation matches" (foldPipe == foldPipeDef)

private def exceptEq [BEq ε] [BEq α] : Except ε α → Except ε α → Bool
  | .ok a, .ok b => a == b
  | .error e1, .error e2 => e1 == e2
  | _, _ => false

private def runCombinatorTests : IO Unit := do
  -- Result / Option / Natural transformation laws
  require "resMap_id"
    (exceptEq (resMap id (Except.ok (7 : Nat) : Except String Nat)) (.ok (7 : Nat)))
  require "resMap_comp"
    (exceptEq
      (resMap ((· * 2) ∘ (· + 1)) (Except.ok (3 : Nat) : Except String Nat))
      (resMap (· * 2) (resMap (· + 1) (Except.ok (3 : Nat) : Except String Nat))))
  require "optionToResult_natural some"
    (exceptEq
      (resMap (· + 1) (optionToResult "missing" (some (5 : Nat))))
      (optionToResult "missing" (Option.map (· + 1) (some (5 : Nat)))))
  require "optionToResult_natural none"
    (exceptEq
      (resMap (· + 1) (optionToResult "missing" (none : Option Nat)))
      (optionToResult "missing" (Option.map (· + 1) (none : Option Nat))))
  -- Checked fallible in-place Kleisli pipeline fusion across all 3 collection layouts
  let len := 20
  let fields := 3
  let bTable : Nat → Nat → UInt8 := fun i f => (i * 5 + f).toUInt8
  let stepA : UInt8 → Except String UInt8 := fun b =>
    if b < 240 then .ok (b + 10) else .error "overflowA"
  let stepB : UInt8 → Except String UInt8 := fun b =>
    if b < 250 then .ok (b + 5) else .error "overflowB"
  for lay in [CollectionLayout.aos, .soa, .aosoa 8] do
    let st0 := initBuffer lay len fields bTable
    let rTwo := resAndThen (tryMapFieldInPlace 0 lay len fields 0 stepA st0)
      (tryMapFieldInPlace 0 lay len fields 0 stepB)
    let rFused := tryMapFieldInPlace 0 lay len fields 0 (kleisliCompose stepA stepB) st0
    match rTwo, rFused with
    | .ok sTwo, .ok sFused =>
      for i in List.range len do
        for f in List.range fields do
          let loc : ByteLocation := ⟨0, collectionSlot lay len fields i f⟩
          require "fallible Kleisli pipeline fusion matches" (sTwo.byte loc == sFused.byte loc)
    | _, _ => throw (IO.userError "checked in-place pipeline unexpectedly failed")
  -- Fail-fast rejection on overflow value 250
  let badSt : Core.State := ({} : Core.State).addAllocation 0 [1, 250, 3]
  let errMatched := match tryMapFieldInPlace 0 .aos 3 1 0 stepA badSt with
    | .error e => e == "overflowA"
    | .ok _ => false
  require "fallible in-place pipeline rejects out-of-range byte" errMatched
  require "optMap_unwrapOr some" ((Option.map (· * 3) (some (4 : Nat))).getD 9 == 12)
  require "optMap_unwrapOr none" ((Option.map (· * 3) (none : Option Nat)).getD 9 == 9)
  require "resMap_unwrapOr ok" (resUnwrapOr (resMap (· + 5) (Except.ok (4 : Nat) : Except String Nat)) 0 == 9)
  require "resMap_unwrapOr err" (resUnwrapOr (resMap (· + 5) (Except.error "bad" : Except String Nat)) 99 == 99)
  let optK : Nat → Option Nat := fun x => if x > 0 then some (x + 2) else none
  require "optToResult_andThen_natural"
    (exceptEq
      (resAndThen (optionToResult "missing" (some (5 : Nat))) (fun x => optionToResult "missing" (optK x)))
      (optionToResult "missing" (optAndThen (some (5 : Nat)) optK)))

def run : IO Unit := do
  runLNLAndLensTests
  runFusionTests
  runCombinatorTests
  IO.println "Phase 3 categorical LNL, lens, in-place fusion, and combinator regressions passed"

end Aethel.Phase3.Tests
