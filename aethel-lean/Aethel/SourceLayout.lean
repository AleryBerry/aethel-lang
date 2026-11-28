import Aethel.SourceVerification
import Aethel.AutomaticLayout

namespace Aethel.SourceVerification

open Core AutomaticLayout

private def byteType : IntegerType := .unsigned .w8

def SourceMIR.byteSchema (mir : SourceMIR) : Schema :=
  .record (List.replicate mir.fields.length (.addressable, .integer byteType))

private def bytePlacement (abi : TargetIntegerABI) (offset : Nat) : Field :=
  (⟨offset, none⟩, .integer byteType (abi.slot byteType))

/-- Declaration indices are physical offsets in the reference byte record.
Each field occupies one addressable byte under the supported target slot. -/
def SourceMIR.byteLayout (mir : SourceMIR) (abi : TargetIntegerABI) : Layout :=
  .record mir.fields.length 1 ((List.range mir.fields.length).map (bytePlacement abi))

theorem SourceMIR.byteLayout_conforms (mir : SourceMIR) (abi : TargetIntegerABI)
    (slotValid : (abi.slot byteType).Valid byteType)
    (byteSize : (abi.slot byteType).size = 1)
    (byteAlignment : (abi.slot byteType).alignment = 1) :
    Conforms abi mir.byteSchema (mir.byteLayout abi) := by
  apply Conforms.record ⟨0, rfl⟩ (Nat.mod_one _) (by simp)
  · apply List.pairwise_iff_getElem.mpr
    intro left right hLeft hRight ordered
    simp [bytePlacement, Field.Separate, Field.bytes, Layout.size, byteSize]
    omega
  · intro pair member
    obtain ⟨offset, within, placed⟩ := List.mem_map.mp (List.of_mem_zip member).2
    have bound := List.mem_range.mp within
    rw [← placed]
    simp [bytePlacement, Field.Valid, Field.bytes, Layout.size, Layout.alignment, byteSize, byteAlignment]
    omega
  · intro pair member
    have ⟨field, placed⟩ := List.of_mem_zip member
    obtain ⟨offset, _, actual⟩ := List.mem_map.mp placed
    have declared : pair.1 = (.addressable, .integer byteType) := List.eq_of_mem_replicate field
    rw [declared, ← actual]
    exact .integer slotValid

theorem SourceMIR.byteLayout_resolve (mir : SourceMIR) (abi : TargetIntegerABI)
    {offset : Nat} (within : offset < mir.fields.length) :
    resolve (mir.byteLayout abi) [offset] = some (bytePlacement abi offset) := by
  simp [SourceMIR.byteLayout, resolve, within, bind]

private theorem field_geometry {mir : SourceMIR} {abi : TargetIntegerABI}
    {size alignment : Nat} {fields : List Field} {field : Field}
    (conforms : Conforms abi mir.byteSchema (.record size alignment fields))
    (byteSize : (abi.slot byteType).size = 1) (member : field ∈ fields) :
    field.bytes = 1 ∧ field.1.bitOffset = none ∧ field.1.byteOffset < size := by
  obtain ⟨index, within, found⟩ := List.mem_iff_getElem.mp member
  obtain ⟨policy, child, declared, placed, conformsChild⟩ :=
    conforms.field (List.getElem?_eq_some_iff.mpr ⟨within, found⟩)
  have exactType : (policy, child) = (.addressable, .integer byteType) :=
    List.eq_of_mem_replicate (List.mem_of_getElem? declared)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj exactType
  rcases field with ⟨location, layout⟩
  cases conformsChild with
  | integer _ =>
    cases packed : location.bitOffset with
    | none =>
      have bound := placed.1
      simp only [Field.bytes, packed, Option.isSome_none, Bool.false_eq_true, ite_false, Layout.size,
        byteSize] at bound ⊢
      exact ⟨trivial, trivial, by omega⟩
    | some bit =>
      simp [Field.Valid, packed] at placed

/-- With exactly one byte per addressable field, nonoverlap forces any
conforming layout to occupy at least as many bytes as the reference layout. -/
theorem SourceMIR.byteLayout_minimal (mir : SourceMIR) (abi : TargetIntegerABI)
    (byteSize : (abi.slot byteType).size = 1) {candidate : Layout}
    (conforms : Conforms abi mir.byteSchema candidate) :
    (mir.byteLayout abi).size ≤ candidate.size := by
  cases candidate with
  | integer _ _ | fixed _ _ => cases conforms
  | record size alignment fields =>
    let offsets := fields.map fun field => field.1.byteOffset
    have geometry := fun {field} member => field_geometry conforms byteSize (field := field) member
    have count : fields.length = mir.fields.length := by
      cases conforms with
      | record _ _ count _ _ _ => simpa using count.symm
    have distinct : offsets.Nodup := by
      apply List.pairwise_map.mpr
      have separated : fields.Pairwise Field.Separate := by
        cases conforms with
        | record _ _ _ separated _ _ => exact separated
      apply separated.imp_of_mem
      intro left right hLeft hRight separate
      obtain ⟨leftSize, leftBit, _⟩ := geometry hLeft
      obtain ⟨rightSize, rightBit, _⟩ := geometry hRight
      simp [Field.Separate, leftSize, rightSize, leftBit, rightBit] at separate
      omega
    have inside : offsets ⊆ List.range size := by
      intro offset member
      obtain ⟨field, hField, address⟩ := List.mem_map.mp member
      exact List.mem_range.mpr (address ▸ (geometry hField).2.2)
    simpa [offsets, SourceMIR.byteLayout, Layout.size, count] using distinct.length_le_of_subset inside

theorem SourceMIR.byteLayout_natural (mir : SourceMIR) :
    Conforms TargetIntegerABI.natural mir.byteSchema (mir.byteLayout TargetIntegerABI.natural) :=
  mir.byteLayout_conforms _ (TargetIntegerABI.natural_valid _) (by decide) (by decide)

private theorem validate_integer {abi : TargetIntegerABI} {kind : IntegerType} {layout : Layout}
    (conforms : Conforms abi (.integer kind) layout) :
    validate abi 1 (.integer kind) layout = true := by
  cases conforms with
  | integer valid => simp [validate, valid]

theorem SourceMIR.byteLayout_validates (mir : SourceMIR) :
    validate TargetIntegerABI.natural 2 mir.byteSchema (mir.byteLayout TargetIntegerABI.natural) = true := by
  have conforms := mir.byteLayout_natural
  cases conforms with
  | record aligned stride count separate placements children =>
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true ⟨aligned, stride, count, separate⟩, List.all_eq_true.mpr ?_⟩
    intro pair member
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true (placements pair member), ?_⟩
    have declared : pair.1 = (.addressable, .integer byteType) :=
      List.eq_of_mem_replicate (List.of_mem_zip member).1
    have field := children pair member
    rw [declared] at field ⊢
    exact validate_integer field

theorem Verified.field_placement {input : String} (accepted : Verified input) (abi : TargetIntegerABI)
    {offset : Nat} {field : String} {initial : UInt8}
    (declared : accepted.source.fields[offset]? = some (field, initial)) :
    resolve (accepted.mir.byteLayout abi) [offset] = some (bytePlacement abi offset) := by
  apply accepted.mir.byteLayout_resolve
  rw [accepted.lowers.initialBytes]
  exact (List.getElem?_eq_some_iff.mp declared).choose

theorem SourceMIR.byteLayout_handle (mir : SourceMIR) (abi : TargetIntegerABI)
    {state : State} (addresses : RecordAddresses state) {offset : Nat}
    {handle : Handle} (found : state.handle offset = some handle) (within : offset < mir.fields.length) :
    ∃ field, resolve (mir.byteLayout abi) [offset] = some field ∧
      handle.location = ⟨0, field.1.byteOffset⟩ ∧ field.1.bitOffset = none :=
  ⟨bytePlacement abi offset, mir.byteLayout_resolve abi within, addresses offset handle found, rfl⟩

theorem Verified.initialized_layout_field {input : String} (accepted : Verified input)
    {offset : Nat} {name : String} {initial : UInt8}
    (declared : accepted.source.fields[offset]? = some (name, initial)) :
    ∃ state field, Core.run {} accepted.mir.entry = some state ∧
      resolve (accepted.mir.byteLayout TargetIntegerABI.natural) [offset] = some field ∧
      field.1.bitOffset = none ∧ state.handle offset = some ⟨⟨0, field.1.byteOffset⟩, .exclusive⟩ ∧
      state.byte ⟨0, field.1.byteOffset⟩ = some initial := by
  obtain ⟨entered, ran⟩ := SourceMIR.entry_runs accepted.checked
  have matching : accepted.mir.fields[offset]? = some (name, initial) := by
    rw [accepted.lowers.initialBytes]
    exact declared
  obtain ⟨handle, live⟩ := accepted.mir.entry_initialized ran matching
  exact ⟨entered, _, ran, accepted.field_placement TargetIntegerABI.natural declared, rfl, handle, live⟩

end Aethel.SourceVerification
