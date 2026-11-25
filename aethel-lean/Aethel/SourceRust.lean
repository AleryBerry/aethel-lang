import Aethel.SourceLayout
import Aethel.RustBorrowedCall

namespace Aethel.SourceVerification

open Core AutomaticLayout RustFFI

def SourceMIR.rustFieldSpec (mir : SourceMIR) (field : Fin mir.fields.length) (mode : AccessMode) :
    RustSliceSpec :=
  ⟨0, field.val, 1, 1, 1, mode, false⟩

theorem SourceMIR.rustFieldSpec_layout (mir : SourceMIR) (field : Fin mir.fields.length) (mode : AccessMode) :
    let argument := mir.rustFieldSpec field mode
    ∃ placement, resolve (mir.byteLayout TargetIntegerABI.natural) [field.val] = some placement ∧
      argument.byteOffset = placement.1.byteOffset ∧
      argument.elemSize = placement.bytes ∧ argument.elemAlign = placement.2.alignment ∧
      argument.isSubBytePacked = placement.1.bitOffset.isSome :=
  ⟨_, mir.byteLayout_resolve _ field.isLt, rfl, rfl, rfl, rfl⟩

private theorem byte_abi_valid {state : State} {location : ByteLocation} {value : UInt8}
    (live : state.byte location = some value) (mode : AccessMode) :
    RustSliceAbiValid state ⟨location.allocation, location.offset, 1, 1, 1, mode, false⟩ := by
  refine ⟨rfl, Nat.zero_lt_succ 0, (show Nat.isPowerOfTwo 1 = true from by decide), Nat.mod_one _,
    Nat.mod_one 1, (show 1 ≤ isizeMax64 from by decide), Or.inr ?_⟩
  simp only [State.byte, bind, Option.bind_eq_some_iff] at live
  obtain ⟨allocation, found, initialized⟩ := live
  exact ⟨allocation, found, Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp initialized).choose, trivial⟩

theorem Verified.rustField_initialized {input : String} (accepted : Verified input)
    (field : Fin accepted.mir.fields.length) (mode : AccessMode)
    {name : String} {value : UInt8} {entry : State}
    (declared : accepted.source.fields[field.val]? = some (name, value))
    (entered : Core.run {} accepted.mir.entry = some entry) :
    RustSliceAbiValid entry (accepted.mir.rustFieldSpec field mode) ∧
      entry.handle field.val = some ⟨⟨0, field.val⟩, .exclusive⟩ ∧
      entry.byte ⟨0, field.val⟩ = some value := by
  have matching := (congrArg (fun fields : List (String × UInt8) => fields[field.val]?)
    accepted.lowers.initialBytes).trans declared
  obtain ⟨found, initialized⟩ := accepted.mir.entry_initialized entered matching
  exact ⟨byte_abi_valid initialized mode, found, initialized⟩

/-- A byte field remains a valid borrowed argument after any checked block
that restores entry resources, even when the block changed its value. -/
theorem SourceMIR.rustField_at_restored_resources (mir : SourceMIR)
    (field : Fin mir.fields.length) (mode : AccessMode) {entry current : State}
    (entered : Core.run {} mir.entry = some entry) (restored : current.resources = entry.resources) :
    ∃ value, RustSliceAbiValid current (mir.rustFieldSpec field mode) ∧
      current.handle field.val = some ⟨⟨0, field.val⟩, .exclusive⟩ ∧
      current.byte ⟨0, field.val⟩ = some value := by
  obtain ⟨found, initialized⟩ := mir.entry_initialized entered (List.getElem?_eq_getElem field.isLt)
  have live : (current.byte ⟨0, field.val⟩).isSome := by
    rw [← State.resources_live, restored, State.resources_live, initialized]
    rfl
  obtain ⟨value, currentByte⟩ := Option.isSome_iff_exists.mp live
  have currentHandles := congrArg ResourceState.handles restored
  change current.handles = entry.handles at currentHandles
  exact ⟨value, byte_abi_valid currentByte mode, by
    simpa only [State.handle, currentHandles] using found, currentByte⟩

def SourceMIR.rustFieldArguments (mir : SourceMIR) (fields : List (Fin mir.fields.length × AccessMode)) :
    List RustSliceSpec :=
  fields.map fun (index, mode) => mir.rustFieldSpec index mode

private theorem rustFieldArguments_write {mir : SourceMIR} {fields : List (Fin mir.fields.length × AccessMode)}
    {field : Fin mir.fields.length}
    (written : RustCallWrites (mir.rustFieldArguments fields) ⟨0, field.val⟩) :
    (field, .exclusive) ∈ fields := by
  obtain ⟨slice, argument, within, write⟩ := written
  obtain ⟨⟨index, mode⟩, declared, rfl⟩ := List.mem_map.mp argument
  have location := ((mir.rustFieldSpec index mode).mem_locations ⟨0, field.val⟩).mp within
  have same : field = index := Fin.ext (by
    have extent := location.2
    simp only [RustSliceSpec.interval, Interval.Contains, SourceMIR.rustFieldSpec,
      RustSliceSpec.byteLen, Nat.mul_one] at extent
    omega)
  subst index
  cases write
  exact declared

private theorem SourceMIR.rustCall_frames_field (mir : SourceMIR)
    {fields : List (Fin mir.fields.length × AccessMode)} {field : Fin mir.fields.length}
    {current returned : State} {trace : Program} (compatible : current.ViewsCompatible)
    (outside : (field, .exclusive) ∉ fields)
    (finished : runRustBorrowedCall current (mir.rustFieldArguments fields) trace = some returned) :
    returned.resources = current.resources ∧ returned.byte ⟨0, field.val⟩ = current.byte ⟨0, field.val⟩ := by
  have typed := (runRustBorrowedCall_correct ..).mp finished
  obtain ⟨restored, frame⟩ := typed.restores_scope compatible
  exact ⟨restored, frame ⟨0, field.val⟩ (fun wrote => outside (rustFieldArguments_write wrote))⟩

theorem Verified.rustCall_preserves_field {input : String} (accepted : Verified input)
    {fields : List (Fin accepted.mir.fields.length × AccessMode)}
    {field : Fin accepted.mir.fields.length} {name : String} {value : UInt8} {entry returned : State}
    {trace : Program} (declared : accepted.source.fields[field.val]? = some (name, value))
    (entered : Core.run {} accepted.mir.entry = some entry)
    (outside : (field, .exclusive) ∉ fields)
    (finished : runRustBorrowedCall entry (accepted.mir.rustFieldArguments fields) trace = some returned) :
    returned.resources = entry.resources ∧ returned.byte ⟨0, field.val⟩ = some value := by
  have compatible := (Core.run_sound entered).views_compatible State.empty_views_compatible
  obtain ⟨restored, frame⟩ := accepted.mir.rustCall_frames_field compatible outside finished
  exact ⟨restored, frame.trans (accepted.rustField_initialized field .shared declared entered).2.2⟩

theorem Verified.rustCall_after_body {input : String} (accepted : Verified input)
    {fields : List (Fin accepted.mir.fields.length × AccessMode)} {field : Fin accepted.mir.fields.length}
    {entry current returned : State} {trace : Program}
    (entered : Core.run {} accepted.mir.entry = some entry)
    (bodyRan : accepted.mir.body.run 0 entry = some current)
    (outside : (field, .exclusive) ∉ fields)
    (finished : runRustBorrowedCall current (accepted.mir.rustFieldArguments fields) trace = some returned) :
    (∀ slice ∈ accepted.mir.rustFieldArguments fields, RustSliceAbiValid current slice) ∧
      returned.resources = current.resources ∧ returned.byte ⟨0, field.val⟩ = current.byte ⟨0, field.val⟩ := by
  have bodyOK := SourceMIR.body_checked accepted.checked entered
  obtain ⟨after, computed, restored⟩ := Operations.run_preserves_resources bodyOK
  obtain rfl := Option.some.inj (computed.symm.trans bodyRan)
  have entryCompatible := (Core.run_sound entered).views_compatible State.empty_views_compatible
  have sameViews : after.views = entry.views := congrArg ResourceState.views restored
  have compatible : after.ViewsCompatible := by
    simpa only [State.ViewsCompatible, sameViews] using entryCompatible
  refine ⟨?_, accepted.mir.rustCall_frames_field compatible outside finished⟩
  intro slice member
  obtain ⟨⟨index, mode⟩, _, rfl⟩ := List.mem_map.mp member
  obtain ⟨_, valid, _, _⟩ := accepted.mir.rustField_at_restored_resources index mode entered restored
  exact valid

end Aethel.SourceVerification
