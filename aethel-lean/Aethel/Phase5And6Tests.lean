import Aethel.MIRValidator
import Aethel.ScopedForkJoin
import Aethel.RustFFI

namespace Aethel.Phase5And6.Tests

open Aethel Aethel.Core Aethel.AutomaticLayout Aethel.CacheLayout Aethel.Permissions
open Aethel.MIRValidator Aethel.ScopedForkJoin Aethel.RustFFI

private def require (msg : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError msg)

private def runMIRTests : IO Unit := do
  match validateMIR sampleValidMIR with
  | .ok cert =>
    require "MIR valid certificate" (cert == ⟨1, [("EntityFlags", 8)], 1⟩)
  | .error _ =>
    throw (IO.userError "valid MIR unexpectedly failed")

  match validateMIR sampleForgedSizeMIR with
  | .error (.staleLayoutSize "EntityFlags" 999 8) => pure ()
  | _ => throw (IO.userError "forged layout size MIR was not rejected")

  match validateMIR sampleLeakedViewMIR with
  | .error (.invalidResources "leak_fn") => pure ()
  | _ => throw (IO.userError "leaked view MIR was not rejected")

  match validateMIR { sampleValidMIR with version := 2 } with
  | .error (.unsupportedVersion 2 1) => pure ()
  | _ => throw (IO.userError "stale MIR version was not rejected")

  let frameBad : MIRModule :=
    { version := 1
      functions :=
        [ { name := "frame_bad"
            effects := ⟨[], [[0]], []⟩
            preserves := [[0]]
            body := [] } ] }
  match validateMIR frameBad with
  | .error (.frameViolation "frame_bad") => pure ()
  | _ => throw (IO.userError "frame violation MIR was not rejected")

  let validText :=
    "# Sample versioned Aethel MIR\n" ++
    "mir_version 1\n" ++
    "record Player 8\n" ++
    "  field u32\n" ++
    "  field u1\n" ++
    "  field u1\n" ++
    "end_record\n" ++
    "collection Entities aosoa 8 4\n" ++
    "fn move_pos\n" ++
    "  effect_write 0\n" ++
    "  preserves 2\n" ++
    "  alloc 0 16\n" ++
    "  alias 0 0 0 exclusive\n" ++
    "  reserve 0 0 exclusive\n" ++
    "  write_view 0 9\n" ++
    "  release 0\n" ++
    "  forget 0\n" ++
    "  destroy 0\n" ++
    "end_fn\n"
  match validateMIRText validText with
  | .ok cert =>
    require "MIR text parser certificate" (cert == ⟨1, [("Player", 8)], 1⟩)
  | .error err =>
    throw (IO.userError s!"valid MIR text failed: {err}")

  let staleText := "mir_version 99\n"
  match validateMIRText staleText with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "stale MIR text unexpectedly passed")

private def runForkJoinTests : IO Unit := do
  let fpA : TaskFootprint := ⟨[⟨0, 0⟩], [⟨0, 1⟩]⟩
  let fpB : TaskFootprint := ⟨[⟨0, 0⟩], [⟨0, 2⟩]⟩
  require "disjoint fork tasks permitted" (checkForkDisjoint fpA fpB)
  require "read-write fork overlap rejected"
    (!checkForkDisjoint ⟨[⟨0, 0⟩], []⟩ ⟨[], [⟨0, 0⟩]⟩)
  require "write-write fork overlap rejected"
    (!checkForkDisjoint ⟨[], [⟨0, 1⟩]⟩ ⟨[], [⟨0, 1⟩]⟩)

  let st0 : Core.State := ({} : Core.State).addAllocation 0 [10, 20, 30, 40]
  let wsA : TaskWrites := [(⟨0, 1⟩, 77)]
  let wsB : TaskWrites := [(⟨0, 2⟩, 88)]
  let ab := applyTaskWrites (applyTaskWrites st0 wsA) wsB
  let ba := applyTaskWrites (applyTaskWrites st0 wsB) wsA
  for off in [0, 1, 2, 3] do
    let loc : ByteLocation := ⟨0, off⟩
    require "concurrent disjoint writes commute" (ab.byte loc == ba.byte loc)
  require "shared read loc unchanged after child write"
    ((applyTaskWrites st0 wsB).byte ⟨0, 0⟩ == some 10)

  let parent : PermState :=
    { base := st0
      pviews := [⟨0, ⟨0, 0⟩, .shared⟩] }
  let childViews : List PermView :=
    [ ⟨1, ⟨0, 1⟩, .activeExclusive⟩
    , ⟨2, ⟨0, 0⟩, .shared⟩ ]
  match forkAcquire parent childViews with
  | none => throw (IO.userError "valid forkAcquire failed")
  | some child =>
    let restored := joinRelease child (childViews.map PermView.id)
    require "joinRelease restores exact parent PermState" (restored == parent)

private def runRustFFITests : IO Unit := do
  let st0 : Core.State := ({} : Core.State).addAllocation 0 [1, 2, 3, 4, 5, 6, 7, 8]
  require "valid exclusive aligned Rust slice accepted"
    (checkRustSlice st0 ⟨0, 0, 2, 4, 4, .exclusive, false⟩)
  require "valid empty Rust slice accepted"
    (checkRustSlice ({} : Core.State) ⟨0, 0, 0, 4, 4, .exclusive, false⟩)
  require "sub-byte packed Rust slice rejected"
    (!checkRustSlice st0 ⟨0, 0, 4, 1, 1, .shared, true⟩)
  require "unaligned Rust slice rejected"
    (!checkRustSlice st0 ⟨0, 3, 1, 4, 4, .shared, false⟩)
  require "disjoint mutable SoA slices compatible"
    (checkRustSlicePairCompatible
      ⟨0, 0, 4, 1, 1, .exclusive, false⟩
      ⟨0, 4, 4, 1, 1, .exclusive, false⟩)
  require "overlapping shared slices compatible"
    (checkRustSlicePairCompatible
      ⟨0, 0, 4, 1, 1, .shared, false⟩
      ⟨0, 0, 4, 1, 1, .shared, false⟩)
  require "overlapping mut+shared slices rejected"
    (!checkRustSlicePairCompatible
      ⟨0, 0, 4, 1, 1, .exclusive, false⟩
      ⟨0, 2, 4, 1, 1, .shared, false⟩)

  let stWithView : Core.State := st0.addView ⟨1, ⟨0, 0⟩, .shared⟩
  let callViews : List Core.View := [⟨10, ⟨0, 4⟩, .exclusive⟩, ⟨11, ⟨0, 5⟩, .exclusive⟩]
  require "rustCall bracket restores existing views"
    (popCallViews (pushCallViews stWithView callViews) [10, 11] == stWithView)

  require "RustOwn alive use succeeds"
    (rustOwnStep .alive .useHandle == some .alive)
  require "RustOwn drop consumes ownership"
    (rustOwnStep .alive .dropHandle == some .dropped)
  require "RustOwn double drop rejected"
    ((rustOwnStep .dropped .dropHandle).isNone)
  require "RustOwn use after drop rejected"
    ((rustOwnStep .dropped .useHandle).isNone)

def run : IO Unit := do
  runMIRTests
  runForkJoinTests
  runRustFFITests
  IO.println "Phase 5 & 6 MIR validator, scoped fork/join, and Rust FFI regressions passed"

end Aethel.Phase5And6.Tests
