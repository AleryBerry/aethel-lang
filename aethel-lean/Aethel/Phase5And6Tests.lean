import Aethel.MIRValidator
import Aethel.ScopedForkJoin
import Aethel.RustFFI
import Aethel.RustBorrowedCall
import Aethel.SourceMIR

namespace Aethel.Phase5And6.Tests

open Aethel Aethel.Core Aethel.AutomaticLayout Aethel.CacheLayout Aethel.Permissions
open Aethel.MIRValidator Aethel.ScopedForkJoin Aethel.RustFFI

private def require (msg : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError msg)

private def runMIRTests : IO Unit := do
  match validateMIR sampleValidMIR with
  | .ok cert =>
    require "MIR valid certificate" (cert == ⟨1, [("EntityFlags", 8)], 1, 0⟩)
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

  let records := sampleValidMIR.records ++
    (sampleValidMIR.records.map fun r => { r with name := "Second" })
  match validateMIR { sampleValidMIR with records := records } with
  | .ok cert =>
    require "MIR certificate preserves record order"
      (cert.recordSizes == [("EntityFlags", 8), ("Second", 8)])
  | .error _ => throw (IO.userError "ordered record list unexpectedly failed")

  let badCollections : List MIRCollectionDecl := [⟨"first", .aosoa 0, 1⟩, ⟨"second", .soa, 0⟩]
  match validateMIR { sampleLeakedViewMIR with collections := badCollections } with
  | .error (.invalidCollectionLayout "first") => pure ()
  | _ => throw (IO.userError "MIR validation must report the first error")

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
    require "MIR text parser certificate" (cert == ⟨1, [("Player", 8)], 1, 0⟩)
  | .error err =>
    throw (IO.userError s!"valid MIR text failed: {err}")

  let staleText := "mir_version 99\n"
  match validateMIRText staleText with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "stale MIR text unexpectedly passed")

  let stageAValidText :=
    "mir_version 1\n" ++
    "fn two_phase_and_disjoint\n" ++
    "  perm_alloc 8\n" ++
    "  perm_reserve 0 0 reserved\n" ++
    "  perm_reserve 1 0 shared\n" ++
    "  perm_read 1\n" ++
    "  perm_release 1\n" ++
    "  perm_activate 0\n" ++
    "  perm_write 0 42\n" ++
    "  perm_release 0\n" ++
    "  disjoint_idx ne:v0,v1 v0 v1\n" ++
    "  disjoint_idx none v0 v0+1\n" ++
    "  disjoint_slice none 0 v0 v0 v1\n" ++
    "end_fn\n"
  match validateMIRText stageAValidText with
  | .ok cert =>
    require "Stage A two-phase + disjoint MIR text certificate" (cert == ⟨1, [], 1, 0⟩)
  | .error err =>
    throw (IO.userError s!"Stage A valid MIR text failed: {err}")

  let stageABadActivate :=
    "mir_version 1\n" ++
    "fn bad_activate\n" ++
    "  perm_alloc 8\n" ++
    "  perm_reserve 0 0 reserved\n" ++
    "  perm_reserve 1 0 shared\n" ++
    "  perm_activate 0\n" ++
    "  perm_release 1\n" ++
    "  perm_release 0\n" ++
    "end_fn\n"
  match validateMIRText stageABadActivate with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "activating reserved view while shared view is live was not rejected")

  let stageABadDisjoint :=
    "mir_version 1\n" ++
    "fn bad_disjoint\n" ++
    "  disjoint_idx none v0 v1\n" ++
    "end_fn\n"
  match validateMIRText stageABadDisjoint with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unguarded disjoint_idx v0 v1 was not rejected")

  let stageDValidLaws :=
    "mir_version 1\n" ++
    "fn countdown_fn\n" ++
    "  decreases 2 lt 0 v0 lt 0 v1 v0 sub v0 v1\n" ++
    "  decreases 1 ne v0 0 v0 sub v0 1\n" ++
    "end_fn\n" ++
    "law_always damage_recovery\n" ++
    "  hyp le v1 v0\n" ++
    "  goal eq add sub v0 v1 v1 v0\n" ++
    "end_law\n" ++
    "law_never bounded_damage\n" ++
    "  goal lt v0 sub v0 v1\n" ++
    "end_law\n"
  match validateMIRText stageDValidLaws with
  | .ok cert =>
    require "Stage D MIR laws & decreases certificate" (cert == ⟨1, [], 1, 2⟩)
  | .error err =>
    throw (IO.userError s!"Stage D valid MIR laws failed: {err}")

  let stageDBadDecreases :=
    "mir_version 1\n" ++
    "fn nonterm_fn\n" ++
    "  decreases 0 v0 add v0 1\n" ++
    "end_fn\n"
  match validateMIRText stageDBadDecreases with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "non-decreasing 'decreases' certificate was not rejected")

  let stageDBadLaw :=
    "mir_version 1\n" ++
    "law_never buggy_damage\n" ++
    "  goal lt v0 add v0 v1\n" ++
    "end_law\n"
  match validateMIRText stageDBadLaw with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "falsifiable constitutional law in MIR was not rejected")

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

  -- Check 3-way OS-thread permutation determinism across distinct schedules
  let tA : ForkTask :=
    ⟨⟨[⟨0, 3⟩], [⟨0, 0⟩]⟩, [(⟨0, 0⟩, 11)], fun _ h => by simp at h; subst h; simp⟩
  let tB : ForkTask :=
    ⟨⟨[⟨0, 3⟩], [⟨0, 1⟩]⟩, [(⟨0, 1⟩, 22)], fun _ h => by simp at h; subst h; simp⟩
  let tC : ForkTask :=
    ⟨⟨[⟨0, 3⟩], [⟨0, 2⟩]⟩, [(⟨0, 2⟩, 33)], fun _ h => by simp at h; subst h; simp⟩
  let resABC := runForkSchedule st0 [tA, tB, tC]
  let resCAB := runForkSchedule st0 [tC, tA, tB]
  let resBCA := runForkSchedule st0 [tB, tC, tA]
  for off in [0, 1, 2, 3] do
    let loc : ByteLocation := ⟨0, off⟩
    require "3-thread @parallel fork permutations produce identical bytes"
      (resABC.byte loc == resCAB.byte loc && resABC.byte loc == resBCA.byte loc)

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
  require "empty mutable Rust span inside a long range is disjoint"
    (checkRustSlicePairCompatible
      ⟨0, 0, isizeMax64, 1, 1, .exclusive, false⟩
      ⟨0, 24, 0, 1, 1, .exclusive, false⟩)
  require "long mutable Rust ranges overlap by their endpoints"
    (!checkRustSlicePairCompatible
      ⟨0, 0, isizeMax64, 1, 1, .exclusive, false⟩
      ⟨0, isizeMax64 - 1, 1, 1, 1, .shared, false⟩)

  let stWithView : Core.State := st0.addView ⟨1, ⟨0, 0⟩, .shared⟩
  let callViews : List Core.View := [⟨10, ⟨0, 4⟩, .exclusive⟩, ⟨11, ⟨0, 5⟩, .exclusive⟩]
  require "rustCall bracket restores existing views"
    (popCallViews (pushCallViews stWithView callViews) [10, 11] == stWithView)
  let writable : RustSliceSpec := ⟨0, 4, 2, 1, 1, .exclusive, false⟩
  let readable : RustSliceSpec := ⟨0, 1, 2, 1, 1, .shared, false⟩
  let empty := { writable with len := 0 }
  let slices := [writable, empty, readable]
  require "Rust borrow plan releases the exact caller state after an empty trace"
    (checkRustBorrowPlan stWithView slices &&
      runRustBorrowedCall stWithView slices [] == some stWithView)
  require "Rust borrow plan rejects duplicate exclusive argument occurrences"
    (!checkRustBorrowPlan stWithView [writable, writable])
  let atCallerView := { readable with byteOffset := 0, len := 1 }
  require "Rust shared arguments may overlap a live shared caller view"
    (checkRustBorrowPlan stWithView [atCallerView, atCallerView])
  let firstShared := stWithView.freshView
  let sharedReaders := [.readView (firstShared + 1), .readView firstShared]
  require "Rust shared arguments can each read a byte already shared by the caller"
    ((runRustBorrowedCall stWithView [atCallerView, atCallerView] sharedReaders).any fun returned =>
      returned.views == stWithView.views && returned.observations == [1, 1])
  require "Rust borrow plan accepts the byte just beyond a caller reservation"
    (checkRustBorrowPlan stWithView [{ atCallerView with byteOffset := 1, mode := .exclusive }])
  let grants := rustCallViews stWithView slices
  let some written := grants[0]? | throw (IO.userError "missing mutable Rust loan")
  let some read := grants[3]? | throw (IO.userError "missing last shared Rust loan")
  let some after := runRustBorrowedCall stWithView slices
      [.writeView written.id 99, .readView read.id, .readView written.id] |
    throw (IO.userError "valid Rust borrowed trace rejected")
  require "Rust trace writes the borrowed byte and reads the current contents"
    (after.byte ⟨0, 4⟩ == some 99 && after.observations == [99, 3])
  require "Rust trace restores caller permissions and keeps unrelated bytes"
    (decide (after.resources = stWithView.resources) && after.byte ⟨0, 7⟩ == some 8)
  require "Rust trace cannot write through a shared slice"
    (runRustBorrowedCall stWithView slices [.writeView read.id 20]).isNone
  require "A denied Rust write rejects a trace containing an earlier authorized write"
    (runRustBorrowedCall stWithView slices [.writeView written.id 92, .writeView read.id 20]).isNone
  require "Rust trace rejects the ID just after the last granted byte"
    (runRustBorrowedCall stWithView slices [.readView (read.id + 1)]).isNone
  require "A zero-length Rust slice grants no byte IDs"
    (runRustBorrowedCall stWithView [empty] [.readView stWithView.freshView]).isNone
  require "Rust trace cannot use the caller's separate view"
    (runRustBorrowedCall stWithView [writable] [.readView 1]).isNone
  require "Rust mut slice cannot overlap a live caller shared reservation"
    (runRustBorrowedCall stWithView [⟨0, 0, 1, 1, 1, .exclusive, false⟩] []).isNone
  require "Rust call rejects two overlapping slice arguments without executing accesses"
    (runRustBorrowedCall stWithView [writable, ⟨0, 5, 1, 1, 1, .shared, false⟩] []).isNone

  let access : List RustAdapterAccess := [⟨⟨0, 1⟩, some 83⟩, ⟨⟨2, 1⟩, none⟩]
  require "Argument-relative Rust trace translates a byte past an empty argument"
    ((runRustAdapterTrace stWithView slices access).any fun returned =>
      returned.byte ⟨0, 4⟩ == some 5 && returned.byte ⟨0, 5⟩ == some 83 &&
      returned.observations == [3] && decide (returned.resources = stWithView.resources))
  require "Argument-relative Rust trace rejects even the first byte of an empty argument"
    (runRustAdapterTrace stWithView slices [⟨⟨1, 0⟩, none⟩]).isNone

  require "RustOwn alive use succeeds"
    (rustOwnStep .alive .useHandle == some .alive)
  require "RustOwn drop consumes ownership"
    (rustOwnStep .alive .dropHandle == some .dropped)
  require "RustOwn double drop rejected"
    ((rustOwnStep .dropped .dropHandle).isNone)
  require "RustOwn use after drop rejected"
    ((rustOwnStep .dropped .useHandle).isNone)

private def runReferenceAccessTests : IO Unit := do
  let state := (({} : Core.State).addAllocation 0 [14, 27]).addView ⟨0, ⟨0, 0⟩, .exclusive⟩
  let matching : SourceVerification.Operations := .assign (.view 0 0) 82 .done
  let forged : SourceVerification.Operations := .assign (.view 0 1) 82 .done
  let exit : SourceVerification.Continuation := fun _ => .instruction (.release 0) .finish
  require "A reference store checks and writes the byte of its actual exclusive reservation"
    (matching.check 1 state.resources && (matching.run 1 state).any (fun after =>
      after.byte ⟨0, 0⟩ == some 82 && after.byte ⟨0, 1⟩ == some 27))
  require "An independent reference program cannot claim a sibling's offset for its view store"
    (!forged.check 1 state.resources && (forged.run 1 state).isNone &&
      Structured.check state.resources (matching.toCode 1 exit []) &&
      !Structured.check state.resources (forged.toCode 1 exit []))
  let forgedRead : SourceVerification.Operations := .discard (.view 0 1) .done
  require "A reference load cannot claim a sibling's offset for its live view"
    (!forgedRead.check 1 state.resources && (forgedRead.run 1 state).isNone &&
      !Structured.check state.resources (forgedRead.toCode 1 exit []))
  let guard : SourceVerification.Operations := .branch (.view 0 0) .less (.place (.field 1)) .done .done .done
  let ready := state.addHandle 1 ⟨⟨0, 1⟩, .exclusive⟩
  require "A two-operand branch observes the left byte once before the right byte"
    ((guard.run 1 ready).any (fun after => after.observations == [27, 14]))
  let samePlace := SourceVerification.Place.view 0 0
  let constant : SourceVerification.Operations := .branch samePlace .equal (.place samePlace)
    .done (.assign (.field 0) 96 .done) .done
  require "A statically determined comparison still observes both authorized reads"
    (constant.check 1 ready.resources &&
      (constant.run 1 ready).any (fun after => after.observations == [14, 14]))
  let emptyRange := SourceVerification.Operations.range (.place (.field 1)) (.place samePlace) .done .done
  require "An empty dynamic range still evaluates both endpoints once in order"
    ((emptyRange.run 1 ready).any (fun after => after.observations == [14, 27]))

def run : IO Unit := do
  runMIRTests
  runForkJoinTests
  runRustFFITests
  runReferenceAccessTests
  IO.println "Phase 5 & 6 MIR validator, scoped fork/join, and Rust FFI regressions passed"

end Aethel.Phase5And6.Tests
