import Aethel.StructuredRecords
import Aethel.RecordScopes

namespace Aethel.AutomaticLayout.Tests

open Core

private def runtimeSchema : Schema :=
  .record [(.addressable, .integer (.unsigned .w8)),
    (.addressable, .record [(.mayShareByte, .integer (.unsigned .w4)),
      (.mayShareByte, .integer (.unsigned .w4)), (.mayShareByte, .integer (.unsigned .w1)),
      (.addressable, .integer (.unsigned .w16))]),
    (.addressable, .integer (.unsigned .w8))]

private def recordValues : List Nat → Option IntegerBits
  | [0] => some ⟨.unsigned .w8, 7⟩
  | [1, 0] => some ⟨.unsigned .w4, 10⟩
  | [1, 1] => some ⟨.unsigned .w4, 5⟩
  | [1, 2] => some ⟨.unsigned .w1, 1⟩
  | [1, 3] => some ⟨.unsigned .w16, 4660⟩
  | [2] => some ⟨.unsigned .w8, 8⟩
  | _ => none

private def ensureRuntime (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError name)

def runRecordRuntime : IO Unit := do
  let some (record, initial) := allocateRecord .natural runtimeSchema {} 3 recordValues
    | throw (IO.userError "record allocation failed")
  ensureRuntime "allocation initializes nested payload, flags and outer siblings"
    ((initial.allocation 3).map Allocation.bytes == some [52, 18, 90, 1, 7, 8])
  ensureRuntime "missing leaf rejects full initialization"
    (allocateRecord .natural runtimeSchema {} 3
      (fun path => if path = [1, 1] then none else recordValues path)).isNone
  ensureRuntime "same-width wrong signedness rejects initialization"
    (allocateRecord .natural runtimeSchema {} 3
      (fun path => if path = [1, 1] then some ⟨.signed .w4, 5⟩ else recordValues path)).isNone
  ensureRuntime "a record owner identity is never issued twice"
    (allocateRecord .natural runtimeSchema initial 3 recordValues).isNone
  ensureRuntime "an empty record can allocate without supplying any leaves"
    ((allocateRecord .natural (.record []) {} 0 (fun _ => none)).any fun (_, final) =>
      (final.allocation 0).map Allocation.bytes == some [])
  let some withHandles := Core.run initial ((List.range 6).map fun i => .alias i 3 i .exclusive)
    | throw (IO.userError "record handle setup failed")
  ensureRuntime "ordered per-byte handles permit a full UInt16 read"
    ((record.read withHandles [1, 3] [.handle 0, .handle 1]).any fun v => v.2.toNat == 4660)
  ensureRuntime "a wide access must authorize all its bytes"
    (record.read withHandles [1, 3] [.handle 0]).isNone
  ensureRuntime "a live handle with the wrong byte offset cannot substitute for a capability"
    (record.read withHandles [1, 3] [.handle 1, .handle 0]).isNone
  let some wordView := Core.execute withHandles (.reserve 11 1 .shared)
    | throw (IO.userError "could not reserve high byte")
  ensureRuntime "a shared view blocks a wide write to its high byte"
    (record.write wordView [1, 3] [.handle 0, .handle 1] ⟨.unsigned .w16, 255⟩).isNone
  let some flagView := Core.execute withHandles (.reserve 10 2 .exclusive)
    | throw (IO.userError "could not reserve packed byte")
  ensureRuntime "disjoint packed value bits cannot bypass an exclusive byte reservation"
    (record.write flagView [1, 1] [.handle 2] ⟨.unsigned .w4, 6⟩).isNone
  let some updated := record.write flagView [1, 1] [.view 10] ⟨.unsigned .w4, 6⟩
    | throw (IO.userError "exclusive view could not write the packed field")
  ensureRuntime "authorized packed write preserves its sibling"
    ((record.read updated [1, 0] [.view 10]).any fun v => v.2.toNat == 10)
  ensureRuntime "authorized packed write stores the requested value"
    ((record.read updated [1, 1] [.view 10]).any fun v => v.2.toNat == 6)
  let some outerUpdated := record.write updated [0] [.handle 4] ⟨.unsigned .w8, 21⟩
    | throw (IO.userError "an unrelated byte was blocked by the packed-byte reservation")
  ensureRuntime "read uses the actual allocation after a disjoint write"
    ((outerUpdated.allocation 3).map Allocation.bytes == some [52, 18, 106, 1, 21, 8])
  let some destroyed := Core.run outerUpdated [.release 10, .destroy 3]
    | throw (IO.userError "could not destroy the record after releasing its view")
  ensureRuntime "destroying the record invalidates both byte handles and record access"
    ((destroyed.handle 2).isNone && (record.read destroyed [1, 1] [.handle 2]).isNone)
  IO.println "14 initialized record runtime regressions passed"

open Aethel.Structured.Records

private def rejects (outcome : Except RecordError (List IntegerBits × State))
    (expected : RecordError) : Bool :=
  match outcome with
  | .error actual => decide (actual = expected)
  | .ok _ => false

def runSourceRecords : IO Unit := do
  let some (record, initial) := allocateRecord .natural runtimeSchema {} 3 recordValues
    | throw (IO.userError "record allocation failed")
  let some external := Core.run initial [.alias 50 3 5 .shared, .reserve 100 50 .shared]
    | throw (IO.userError "could not establish unrelated external scope")
  let code : RawRecordCode :=
    .withView [1] .exclusive
      (.load [1, 3] (.branch (.uint16Eq (.var 0) (.uint16 4660))
        (.store [1, 3] (.uint16 17185) .finish) .finish))
      (.withView [1, 3] .shared (.load [1, 3] .finish) .finish)
  let .ok (observed, final) := executeRecord record external code
    | throw (IO.userError "could not run the source program")
  ensureRuntime "typed load drives a branch and the inferred wide store updates both bytes"
    (observed.map (fun v => v.2.toNat) == [4660, 17185] &&
      (final.allocation 3).map Allocation.bytes == some [33, 67, 90, 1, 7, 8])
  ensureRuntime "leaving a view restores the existing handles and unrelated view IDs"
    (decide (final.handles = external.handles ∧ final.views = external.views))
  ensureRuntime "a store under a shared view is rejected during elaboration"
    (rejects (executeRecord record initial (.withView [1, 3] .shared
      (.store [1, 3] (.uint16 0) .finish) .finish)) (.outsideView [1, 3]))
  ensureRuntime "a packed byte capability never widens the lexical path"
    (rejects (executeRecord record initial (.withView [1, 0] .exclusive
      (.store [1, 1] (.integer (.unsigned .w4) 4) .finish) .finish))
      (.outsideView [1, 1]))
  let .ok (continuationRead, continuationState) := executeRecord record initial
      (.withView [1, 3] .shared .finish (.load [1, 3] .finish))
    | throw (IO.userError "continuation could not infer its own view after the earlier view ended")
  ensureRuntime "a later unscoped load acquires and releases a fresh view"
    (continuationRead.map (fun v => v.2.toNat) == [4660] && continuationState.views.isEmpty)
  ensureRuntime "source stores check the logical integer type"
    (rejects (executeRecord record initial (.withView [1, 3] .exclusive
      (.store [1, 3] (.byte 8) .finish) .finish))
      (.illTyped (.expected .uint16 .byte)))
  ensureRuntime "invalid nested paths fail during elaboration"
    (rejects (executeRecord record initial (.withView [1, 5] .shared .finish .finish))
      (.invalidPath [1, 5]))
  ensureRuntime "simultaneous exclusive packed sibling views overlap at the byte"
    (rejects (executeRecord record initial (.withView [1, 0] .exclusive
      (.withView [1, 1] .exclusive .finish .finish) .finish)) .borrowConflict)
  let shared : RawRecordCode := .withView [1, 0] .shared
    (.withView [1, 1] .shared (.load [1, 1] .finish) (.load [1, 0] .finish)) .finish
  let .ok (observed, _) := executeRecord record initial shared
    | throw (IO.userError "compatible shared packed views were rejected")
  ensureRuntime "shared packed siblings can overlap and the outer view survives the inner scope"
    (observed.map (fun v => v.2.toNat) == [5, 10])
  let some blocked := Core.run initial [.alias 99 3 1 .shared, .reserve 55 99 .shared]
    | throw (IO.userError "could not protect the high byte")
  ensureRuntime "a wide exclusive view requires the second byte as well as the first"
    (rejects (executeRecord record blocked (.withView [1, 3] .exclusive .finish .finish))
      .borrowConflict)
  let disjoint : RawRecordCode := .withView [1, 0] .exclusive
    (.withView [0] .exclusive (.store [0] (.byte 99) .finish) (.load [1, 0] .finish)) .finish
  let .ok (observed, separate) := executeRecord record initial disjoint
    | throw (IO.userError "disjoint sibling scope could not execute")
  ensureRuntime "disjoint sibling scopes allow mutation and release their temporary views"
    (observed.map (fun v => v.2.toNat) == [10] && separate.views.isEmpty &&
      (separate.allocation 3).map Allocation.bytes == some [52, 18, 90, 1, 99, 8])
  IO.println "11 structured record and inferred-view regressions passed"

def runInferredScopes : IO Unit := do
  let some (record, initial) := allocateRecord .natural runtimeSchema {} 3 recordValues
    | throw (IO.userError "record allocation failed")
  let automatic : RawRecordCode :=
    .load [1, 3] (.store [1, 3] (.uint16 17185)
      (.branch (.uint16Eq (.var 0) (.uint16 4660))
        (.store [1, 1] (.integer (.unsigned .w4) 6) (.load [1, 3] .finish))
        .finish))
  let .ok (loaded, result) := executeRecord record initial automatic
    | throw (IO.userError "automatic scope placement failed")
  ensureRuntime "a short load scope releases before the following store and retains a copied value"
    (loaded.map (fun v => v.2.toNat) == [4660, 17185] &&
      (result.allocation 3).map Allocation.bytes == some [33, 67, 106, 1, 7, 8] &&
      result.views.isEmpty && result.handles.isEmpty)

  let nested : RawRecordCode := .withView [1] .exclusive
    (.withView [1, 1] .exclusive
      (.store [1, 1] (.integer (.unsigned .w4) 6) (.load [1, 1] .finish))
      (.store [1, 3] (.uint16 17185) (.load [1, 0] .finish)))
    (.load [1, 3] .finish)
  let .ok (loaded, final) := executeRecord record initial nested
    | throw (IO.userError "reborrowing the packed field from an exclusive parent failed")
  ensureRuntime "exclusive child updates a shifted subspan and parent resumes with full authority"
    (loaded.map (fun v => v.2.toNat) == [6, 10, 17185] && final.views.isEmpty &&
      (final.allocation 3).map Allocation.bytes == some [33, 67, 106, 1, 7, 8])
  let sharedChild : RawRecordCode := .withView [1] .exclusive
    (.withView [1, 3] .shared (.load [1, 3] .finish)
      (.store [1, 3] (.uint16 17185) .finish)) .finish
  let .ok (loaded, final) := executeRecord record initial sharedChild
    | throw (IO.userError "shared child from an exclusive parent failed")
  ensureRuntime "a shared child may read, then its exclusive parent may write"
    (loaded.map (fun v => v.2.toNat) == [4660] &&
      (final.allocation 3).map Allocation.bytes == some [33, 67, 90, 1, 7, 8])
  ensureRuntime "shared reborrow cannot store even though the original kernel view is exclusive"
    (rejects (executeRecord record initial (.withView [1] .exclusive
      (.withView [1, 3] .shared (.store [1, 3] (.uint16 1) .finish) .finish) .finish))
      (.outsideView [1, 3]))
  ensureRuntime "nested reborrow cannot turn shared authority back into exclusive authority"
    (rejects (executeRecord record initial (.withView [1] .exclusive
      (.withView [1, 3] .shared (.withView [1, 3] .exclusive .finish .finish) .finish)
      .finish)) .borrowConflict)
  ensureRuntime "a reborrow suspends direct use of the parent's other paths"
    (rejects (executeRecord record initial (.withView [1] .exclusive
      (.withView [1, 0] .shared (.load [1, 3] .finish) .finish) .finish))
      (.outsideView [1, 3]))
  ensureRuntime "a fresh scope cannot bypass the suspended exclusive parent"
    (rejects (executeRecord record initial (.withView [1] .exclusive
      (.withView [1, 0] .shared (.withView [1, 3] .shared .finish .finish) .finish)
      .finish)) .borrowConflict)
  let some blocked := Core.run initial [.alias 50 3 1 .shared, .reserve 99 50 .shared]
    | throw (IO.userError "could not retain an external shared reservation")
  ensureRuntime "automatically inferred stores still check conflicting bytes"
    (rejects (executeRecord record blocked (.store [1, 3] (.uint16 123) .finish))
      .borrowConflict)
  let .ok (loaded, restored) := executeRecord record blocked (.load [1, 3] .finish)
    | throw (IO.userError "automatic read could not coexist with an external shared view")
  ensureRuntime "automatically inferred reads retain external handles and reservations"
    (loaded.map (fun v => v.2.toNat) == [4660] &&
      decide (restored.handles = blocked.handles ∧ restored.views = blocked.views))
  IO.println "9 automatic-scope and reborrow regressions passed"

def runScopeCoalescing : IO Unit := do
  let some (record, initial) := allocateRecord .natural runtimeSchema {} 3 recordValues
    | throw (IO.userError "record allocation failed")

  -- 1. Last-use early release allows access to disjoint sibling after view is dead
  let earlyReleaseCode : RawRecordCode :=
    .withView [1] .exclusive
      (.store [1, 0] (.integer (.unsigned .w4) 9)
        (.store [0] (.byte 42) .finish))
      .finish
  ensureRuntime "naive lexical scoping rejects disjoint access after last use"
    (rejects (executeRecord record initial earlyReleaseCode) (.outsideView [0]))
  let .ok (_, finalEarly) := executeWithScopes record initial earlyReleaseCode
    | throw (IO.userError "executeWithScopes failed on earlyReleaseCode")
  ensureRuntime "last-use early release allowed writing field 0 after releasing field 1"
    (finalEarly.views.isEmpty &&
      (finalEarly.allocation 3).map Allocation.bytes == some [52, 18, 89, 1, 42, 8])

  -- 2. Coalesced contiguous stores merge into one exclusive view and preserve leaf values
  let coalescedWrites : RawRecordCode :=
    .store [1, 0] (.integer (.unsigned .w4) 8)
      (.store [1, 1] (.integer (.unsigned .w4) 7)
        (.load [1, 0]
          (.store [0] (.byte 55) .finish)))
  let .ok (observedWrites, finalWrites) := executeWithScopes record initial coalescedWrites
    | throw (IO.userError "executeWithScopes failed on coalescedWrites")
  ensureRuntime "coalescing grouped field 1 operations and observed loaded value"
    (observedWrites.map (fun v => v.2.toNat) == [8] &&
      finalWrites.views.isEmpty &&
      (finalWrites.allocation 3).map Allocation.bytes == some [52, 18, 120, 1, 55, 8])

  -- 3. Coalesced shared loads merge into one shared view
  let sharedReads : RawRecordCode :=
    .load [1, 0] (.load [1, 1] .finish)
  let .ok (observedReads, finalReads) := executeWithScopes record initial sharedReads
    | throw (IO.userError "executeWithScopes failed on sharedReads")
  ensureRuntime "coalesced shared reads observed both values"
    (observedReads.map (fun v => v.2.toNat) == [10, 5] && finalReads.views.isEmpty)

  -- 4. Coalesced clusters on distinct prefixes execute sequentially without interference
  let sequentialClusters : RawRecordCode :=
    .store [1, 0] (.integer (.unsigned .w4) 3)
      (.store [1, 1] (.integer (.unsigned .w4) 4)
        (.store [0] (.byte 77)
          (.load [0] .finish)))
  let .ok (observedSeq, finalSeq) := executeWithScopes record initial sequentialClusters
    | throw (IO.userError "executeWithScopes failed on sequentialClusters")
  ensureRuntime "sequential coalesced clusters execute and observe correctly"
    (observedSeq.map (fun v => v.2.toNat) == [77] &&
      finalSeq.views.isEmpty &&
      (finalSeq.allocation 3).map Allocation.bytes == some [52, 18, 67, 1, 77, 8])

  -- 5. Coalescing preserves borrow conflict when external reservation is active
  let some blocked := Core.run initial [.alias 50 3 1 .shared, .reserve 99 50 .shared]
    | throw (IO.userError "could not retain an external shared reservation")
  ensureRuntime "coalesced store still detects external borrow conflicts"
    (rejects (executeWithScopes record blocked (.store [1, 3] (.uint16 999) (.store [1, 0] (.integer (.unsigned .w4) 1) .finish)))
      .borrowConflict)

  -- 6. Coalesced scopes reject type mismatch during elaboration
  ensureRuntime "type mismatch in coalesced cluster is rejected during elaboration"
    (rejects (executeWithScopes record initial (.store [1, 0] (.byte 5) (.store [1, 1] (.integer (.unsigned .w4) 6) .finish)))
      (.illTyped (.expected (.integer (.unsigned .w4)) .byte)))

  -- 7. Coalesced scopes reject invalid field paths during elaboration
  ensureRuntime "invalid field path in coalesced candidate is rejected during elaboration"
    (rejects (executeWithScopes record initial (.load [1, 9] (.load [1, 0] .finish)))
      (.invalidPath [1, 9]))

  IO.println "7 scope coalescing and last-use regressions passed"

end Aethel.AutomaticLayout.Tests
