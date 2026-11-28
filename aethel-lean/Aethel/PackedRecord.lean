import Aethel.PackedMachine
import Aethel.RecordViews

namespace Aethel.AutomaticLayout

open Core Structured

/-- The logical type of each value remains attached to its declaration path.
The layout calculator only needs the codec width and its addressable slot. -/
inductive PackedSchema where
  | value (ty : PackedType) (slot : IntegerSlot)
  | record (fields : List (StoragePolicy × PackedSchema))
  | flatRecord (fields : List (StoragePolicy × PackedSchema))
  deriving Repr

private def PackedSchema.storage (declared : StoragePolicy) : PackedSchema → StoragePolicy
  | .value ty _ => if ty.requiredAddresses.isEmpty then declared else .addressable
  | _ => declared

def PackedSchema.geometry : PackedSchema → Schema
  | .value ty slot => .fixed ty.width slot
  | .record fields | .flatRecord fields =>
    .record (fields.attach.map fun field => (storage field.val.1 field.val.2, geometry field.val.2))
termination_by schema => sizeOf schema
decreasing_by all_goals
  have smaller := List.sizeOf_lt_of_mem field.property
  have childSmaller : sizeOf field.val.2 < sizeOf field.val := by
    cases field.val
    simp
    omega
  simp_wf
  omega

def PackedSchema.typeAt (schema : PackedSchema) (path : List Nat) : Option PackedType :=
  match path, schema with
  | [], .value ty _ => some ty
  | index :: rest, .record fields | index :: rest, .flatRecord fields =>
    fields[index]?.bind fun field => field.2.typeAt rest
  | _, _ => none

def PackedSchema.paths : PackedSchema → List (List Nat)
  | .value .. => [[]]
  | .record fields | .flatRecord fields =>
    fields.attach.zipIdx.flatMap fun (field, index) =>
      (paths field.val.2).map (List.cons index)
termination_by schema => sizeOf schema
decreasing_by all_goals
  have smaller := List.sizeOf_lt_of_mem field.property
  have childSmaller : sizeOf field.val.2 < sizeOf field.val := by
    cases field.val
    simp
    omega
  simp_wf
  omega

theorem PackedSchema.paths_nodup (schema : PackedSchema) : schema.paths.Nodup := by
  cases schema with
  | value ty slot => simp [paths]
  | record fields | flatRecord fields =>
    rw [paths]
    apply List.pairwise_flatMap.mpr
    constructor
    · intro entry member
      exact (paths_nodup entry.1.val.2).map _ (fun _ _ different same => different (List.cons.inj same).2)
    · apply List.pairwise_iff_getElem.mpr
      intro i j hi hj ordered
      intro x inX y inY same
      obtain ⟨a, _, ax⟩ := List.mem_map.mp inX
      obtain ⟨b, _, equalY⟩ := List.mem_map.mp inY
      have heads := List.cons.inj (ax.trans (same.trans equalY.symm)) |>.1
      simp only [List.get_eq_getElem, List.getElem_zipIdx, Nat.zero_add] at heads
      omega
termination_by sizeOf schema
decreasing_by all_goals
  have smaller := List.sizeOf_lt_of_mem entry.1.property
  have childSmaller : sizeOf entry.1.val.2 < sizeOf entry.1.val := by
    cases entry.1.val
    simp
    omega
  simp_wf
  omega

private def PackedSchema.isFlat : PackedSchema → Bool
  | .flatRecord _ => true
  | _ => false

def PackedSchema.flatPaths (schema : PackedSchema) : List (List Nat) :=
  match schema with
  | .value .. => []
  | .record fields | .flatRecord fields =>
    let nested := fields.attach.zipIdx.flatMap fun (field, index) =>
      (flatPaths field.val.2).map (List.cons index)
    if schema.isFlat then [] :: nested else nested
termination_by sizeOf schema
decreasing_by all_goals
  have smaller := List.sizeOf_lt_of_mem field.property
  have childSmaller : sizeOf field.val.2 < sizeOf field.val := by
    cases field.val
    simp
    omega
  simp_wf
  omega

inductive PackedSchema.FlatAt : PackedSchema → List Nat → Prop where
  | root : FlatAt (.flatRecord fields) []
  | record (declared : fields[index]? = some child) (below : FlatAt child.2 rest) :
      FlatAt (.record fields) (index :: rest)
  | flatRecord (declared : fields[index]? = some child) (below : FlatAt child.2 rest) :
      FlatAt (.flatRecord fields) (index :: rest)

private theorem PackedSchema.mem_nestedFlatPaths {fields : List (StoragePolicy × PackedSchema)}
    {index : Nat} {child : StoragePolicy × PackedSchema} {rest : List Nat}
    (declared : fields[index]? = some child) (below : rest ∈ child.2.flatPaths) :
    index :: rest ∈ fields.attach.zipIdx.flatMap (fun (field, i) =>
      field.val.2.flatPaths.map (List.cons i)) := by
  obtain ⟨within, equal⟩ := List.getElem?_eq_some_iff.mp declared
  have inside : index < fields.attach.zipIdx.length := by simpa using within
  rw [List.mem_flatMap]
  refine ⟨fields.attach.zipIdx[index], List.getElem_mem _, ?_⟩
  simp only [List.getElem_zipIdx, Nat.zero_add, List.mem_map]
  exact ⟨rest, by simpa only [List.getElem_attach, equal] using below, rfl⟩

theorem PackedSchema.FlatAt.mem_flatPaths {schema : PackedSchema} {path : List Nat}
    (declared : schema.FlatAt path) : path ∈ schema.flatPaths := by
  induction declared with
  | root => simp [flatPaths, isFlat]
  | record found _ ih => simpa [flatPaths, isFlat] using mem_nestedFlatPaths found ih
  | flatRecord found _ ih =>
    rw [flatPaths]
    exact List.mem_cons_of_mem _ (mem_nestedFlatPaths found ih)

theorem PackedSchema.mem_paths {schema : PackedSchema} {path : List Nat} {ty : PackedType}
    (found : schema.typeAt path = some ty) : path ∈ schema.paths := by
  induction path generalizing schema with
  | nil => cases schema <;> simp_all [typeAt, paths]
  | cons index rest ih =>
    cases schema with
    | value _ _ => simp [typeAt] at found
    | record fields | flatRecord fields =>
      cases indexed : fields[index]? with
      | none => simp [typeAt, indexed] at found
      | some field =>
        obtain ⟨within, equal⟩ := List.getElem?_eq_some_iff.mp indexed
        have withinZip : index < fields.attach.zipIdx.length := by simpa using within
        have member : fields.attach.zipIdx[index] ∈ fields.attach.zipIdx := List.getElem_mem _
        rw [paths, List.mem_flatMap]
        refine ⟨_, member, ?_⟩
        simp only [List.getElem_zipIdx, Nat.zero_add, List.mem_map]
        refine ⟨rest, ?_, rfl⟩
        simpa only [List.getElem_attach, equal] using ih (by simpa [typeAt, indexed, bind] using found)

theorem PackedSchema.typeAt_of_mem_paths {schema : PackedSchema} {path : List Nat}
    (member : path ∈ schema.paths) : ∃ ty, schema.typeAt path = some ty := by
  induction path generalizing schema with
  | nil =>
    cases schema with
    | value ty slot => exact ⟨ty, rfl⟩
    | record fields | flatRecord fields =>
      simp [paths, List.mem_flatMap] at member
  | cons index rest ih =>
    cases schema with
    | value ty slot => simp [paths] at member
    | record fields | flatRecord fields =>
      rw [paths, List.mem_flatMap] at member
      obtain ⟨⟨entry, ordinal⟩, indexed, below⟩ := member
      change index :: rest ∈ (entry.val.2.paths.map (List.cons ordinal)) at below
      obtain ⟨suffix, below, equal⟩ := List.mem_map.mp below
      obtain ⟨sameIndex, sameSuffix⟩ := List.cons.inj equal
      subst ordinal
      subst suffix
      obtain ⟨ty, found⟩ := ih below
      have attached := List.mk_mem_zipIdx_iff_getElem?.mp indexed
      have source : fields[index]? = some entry.val := by
        have erased := congrArg (Option.map Subtype.val) attached
        simpa only [← List.getElem?_map, List.attach_map_subtype_val, Option.map_some] using erased
      exact ⟨ty, by simp [typeAt, source, found]⟩

theorem PackedSchema.typeAt_geometry {schema : PackedSchema} {path : List Nat} {ty : PackedType}
    (declared : schema.typeAt path = some ty) :
    ∃ slot, schema.geometry.resolve path = some (.fixed ty.width slot) := by
  induction path generalizing schema with
  | nil =>
    cases schema with
    | value actual slot =>
      cases Option.some.inj declared
      exact ⟨slot, by simp [geometry, Schema.resolve]⟩
    | record _ | flatRecord _ => simp [typeAt] at declared
  | cons index rest ih =>
    cases schema with
    | value ty slot => simp [typeAt] at declared
    | record fields | flatRecord fields =>
      cases indexed : fields[index]? with
      | none => simp [typeAt, indexed] at declared
      | some entry =>
        obtain ⟨slot, found⟩ := ih (by simpa [typeAt, indexed] using declared)
        refine ⟨slot, ?_⟩
        have children :
            (fields.attach.map fun field => (storage field.val.1 field.val.2, geometry field.val.2)) =
              fields.map (fun field => (storage field.1 field.2, geometry field.2)) :=
          List.attach_map_val (f := fun field : StoragePolicy × PackedSchema =>
            (storage field.1 field.2, geometry field.2))
        simp [geometry, children, Schema.resolve, indexed, found]

private theorem PackedSchema.typeAt_leaf {schema : PackedSchema} {path : List Nat} {ty : PackedType}
    (found : schema.typeAt path = some ty) (index : Nat) (rest : List Nat) :
    schema.typeAt (path ++ index :: rest) = none := by
  induction path generalizing schema with
  | nil =>
    cases schema <;> simp_all [typeAt]
  | cons head tail ih =>
    cases schema with
    | value _ _ => simp [typeAt] at found
    | record fields | flatRecord fields =>
      cases atIndex : fields[head]? with
      | none => simp [typeAt, atIndex] at found
      | some field =>
        simp [typeAt, atIndex] at found
        simp [typeAt, atIndex, ih found]

theorem PackedSchema.paths_incomparable {schema : PackedSchema} {left right : List Nat}
    {a b : PackedType} (first : schema.typeAt left = some a) (second : schema.typeAt right = some b)
    (distinct : left ≠ right) : ¬ left <+: right ∧ ¬ right <+: left := by
  constructor
  · rintro ⟨rest, rfl⟩
    cases rest with
    | nil => exact distinct (List.append_nil _).symm
    | cons index rest => rw [typeAt_leaf first index rest] at second; contradiction
  · rintro ⟨rest, rfl⟩
    cases rest with
    | nil => exact distinct (List.append_nil _)
    | cons index rest => rw [typeAt_leaf second index rest] at first; contradiction

def PackedType.decodeCode (ty : PackedType) (code : Nat) : Option ty.Value :=
  if fits : code < 2 ^ ty.width then ty.codec.decode (BitVec.ofNatLT code fits)
  else none

theorem PackedType.decodeCode_complete {ty : PackedType} {code : Nat}
    (fits : code < 2 ^ ty.width) (valid : ty.Represents code) :
    ∃ value, ty.decodeCode code = some value ∧ value.val.toNat = code := by
  let value : ty.Value := ⟨BitVec.ofNatLT code fits, by simpa using valid⟩
  refine ⟨value, ?_, rfl⟩
  unfold decodeCode
  rw [dite_eq_left fits]
  exact ty.codec.decode_encode value

theorem PackedType.product_decodeCode {left right : PackedType} {first second : Nat}
    (firstFits : first < 2 ^ left.width) (secondFits : second < 2 ^ right.width)
    (firstValid : left.Represents first) (secondValid : right.Represents second) :
    ∃ value, (PackedType.product left right).decodeCode (first + second * 2 ^ left.width) = some value ∧
      value.val.toNat = first + second * 2 ^ left.width :=
  decodeCode_complete (product_code_fits firstFits secondFits)
    (product_represents firstFits firstValid secondValid)

theorem PackedType.padding_decodeCode {payload : PackedType} {code before after : Nat}
    (fits : code < 2 ^ payload.width) (valid : payload.Represents code) :
    ∃ value, (PackedType.padding before after payload).decodeCode (code * 2 ^ before) = some value ∧
      value.val.toNat = code * 2 ^ before :=
  decodeCode_complete (padding_code_fits fits) (padding_represents fits valid)

theorem PackedType.tagged_decodeCode {variants : List PackedType} {tag code : Nat}
    {payload : PackedType} (selected : variants[tag]? = some payload)
    (fits : code < 2 ^ payload.width) (valid : payload.Represents code) :
    ∃ value, (PackedType.tagged variants).decodeCode
        (tag + code * 2 ^ ADTLayout.minTagBits variants.length) = some value ∧
      value.val.toNat = tag + code * 2 ^ ADTLayout.minTagBits variants.length :=
  decodeCode_complete (tagged_code_fits selected fits) (tagged_represents selected valid)

theorem PackedType.decodeCode_sound {ty : PackedType} {code : Nat} {value : ty.Value}
    (decoded : ty.decodeCode code = some value) : value.val.toNat = code := by
  unfold decodeCode at decoded
  split at decoded
  · rename_i fits
    have codeEq := ty.codec.encode_decode decoded
    exact (congrArg BitVec.toNat codeEq).trans (BitVec.toNat_ofNatLT _ fits)
  · contradiction

def PackedSchema.AlignedValues (schema : PackedSchema) (layout : Layout) : Prop :=
  ∀ path ty, schema.typeAt path = some ty → ∀ offset alignment, ty.RequiresAddress offset alignment →
    ∃ place leaf, resolve layout path = some (place, leaf) ∧ place.bitOffset = none ∧
      alignment.isPowerOfTwo ∧ layout.alignment % alignment = 0 ∧
      (place.bitStart + offset) % (alignment * 8) = 0

private def PackedSchema.checkAlignedValues (schema : PackedSchema) (layout : Layout) : Bool :=
  schema.paths.all fun path =>
    match schema.typeAt path with
    | none => false
    | some ty =>
      match ty.requiredAddresses with
      | [] => true
      | address :: rest =>
        match resolve layout path with
        | none => false
        | some (place, _) => place.bitOffset.isNone && (address :: rest).all fun (offset, align) =>
          decide (align.isPowerOfTwo ∧ layout.alignment % align = 0 ∧
            (place.bitStart + offset) % (align * 8) = 0)

private theorem PackedSchema.checkAlignedValues_sound {schema : PackedSchema} {layout : Layout}
    (checked : schema.checkAlignedValues layout = true) : schema.AlignedValues layout := by
  intro path ty declared offset alignment required
  have included := required.mem_requiredAddresses
  have found := List.all_eq_true.mp checked path (schema.mem_paths declared)
  simp only [declared] at found
  cases addresses : ty.requiredAddresses with
  | nil => simp [addresses] at included
  | cons first rest =>
    simp only [addresses] at found included
    cases projected : resolve layout path with
    | none => simp [projected] at found
    | some loc =>
      obtain ⟨place, leaf⟩ := loc
      simp only [projected, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true,
        decide_eq_true_eq] at found
      exact ⟨place, leaf, rfl, found.1, found.2 _ included⟩

structure PackedRecord (abi : TargetIntegerABI) (schema : PackedSchema) where
  private mk ::
  owner : OwnerId
  layout : Layout
  conforms : Conforms abi schema.geometry layout
  respectsFlat : layout.RespectsFlat schema.flatPaths
  alignedValues : schema.AlignedValues layout

def PackedRecord.plan (abi : TargetIntegerABI) (schema : PackedSchema) (owner : OwnerId) :
    Option (PackedRecord abi schema) :=
  match planned : planWithFlat abi schema.geometry schema.flatPaths with
  | some layout =>
    let valid := planWithFlat_sound planned
    if checked : schema.checkAlignedValues layout = true then
      some ⟨owner, layout, valid.1, valid.2, PackedSchema.checkAlignedValues_sound checked⟩
    else none
  | none => none

theorem PackedRecord.resolveFlat {record : PackedRecord abi schema} {path : List Nat}
    (declared : schema.FlatAt path) : ∃ offset size align fields,
    resolve record.layout path = some (⟨offset, none⟩, .record size align fields) ∧
    (Layout.record size align fields).FlatTree :=
  record.respectsFlat path declared.mem_flatPaths

def PackedRecord.field (record : PackedRecord abi schema) (path : List Nat) :
    Option (Σ ty : PackedType, PackedValueField record.layout.size ty.width) := do
  let ty ← schema.typeAt path
  let placement ← PackedValueField.resolve record.conforms path ty.width
  return ⟨ty, placement⟩

theorem PackedRecord.resolve_leaf (record : PackedRecord abi schema)
    {path : List Nat} {ty : PackedType} (declared : schema.typeAt path = some ty) :
    ∃ placement slot, AutomaticLayout.resolve record.layout path = some (placement, .fixed ty.width slot) := by
  obtain ⟨slot, shape⟩ := PackedSchema.typeAt_geometry declared
  obtain ⟨⟨placement, leaf⟩, located, conforms⟩ := resolve_complete record.conforms shape
  cases conforms
  exact ⟨placement, slot, located⟩

theorem PackedRecord.field_complete (record : PackedRecord abi schema)
    {path : List Nat} {ty : PackedType} (declared : schema.typeAt path = some ty) :
    ∃ field, record.field path = some ⟨ty, field⟩ := by
  obtain ⟨placement, slot, located⟩ := record.resolve_leaf declared
  unfold field
  rw [declared]
  simp only [bind, Option.bind_some, pure]
  unfold PackedValueField.resolve
  split
  · rename_i actualPlace actualWidth actualSlot projected
    rw [located] at projected
    cases projected
    simp
  · rename_i rejected
    exact False.elim (rejected placement ty.width slot located)

private theorem PackedRecord.field_coordinates {record : PackedRecord abi schema} {path : List Nat}
    {ty : PackedType} {field : PackedValueField record.layout.size ty.width}
    (found : record.field path = some ⟨ty, field⟩) :
    schema.typeAt path = some ty ∧
      ∃ place slot, AutomaticLayout.resolve record.layout path = some (place, .fixed ty.width slot) ∧
        field.start = place.bitStart ∧ ty.width ≤ Field.bitExtent (place, .fixed ty.width slot) := by
  simp only [PackedRecord.field, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at found
  obtain ⟨inferred, declared, projected, located, equal⟩ := found
  cases equal
  exact ⟨declared, PackedValueField.resolve_coordinates record.conforms located⟩

theorem PackedRecord.field_alignedSubvalue {record : PackedRecord abi schema} {path : List Nat}
    {ty : PackedType} {field : PackedValueField record.layout.size ty.width} {offset alignment : Nat}
    (found : record.field path = some ⟨ty, field⟩) (required : ty.RequiresAddress offset alignment) :
    alignment.isPowerOfTwo ∧ record.layout.alignment % alignment = 0 ∧
      (field.start + offset) % (alignment * 8) = 0 ∧ field.start + offset ≤ record.layout.size * 8 := by
  obtain ⟨declared, place, slot, projected, start, _⟩ := field_coordinates found
  obtain ⟨_, _, resolved, _, power, base, aligned⟩ := record.alignedValues path ty declared _ _ required
  rw [projected] at resolved
  cases resolved
  exact ⟨power, base, start ▸ aligned, Nat.le_trans (Nat.add_le_add_left required.within _) field.fits⟩

theorem PackedRecord.fields_disjoint {record : PackedRecord abi schema} {left right : List Nat}
    {a b : PackedType} {first : PackedValueField record.layout.size a.width}
    {second : PackedValueField record.layout.size b.width}
    (foundA : record.field left = some ⟨a, first⟩)
    (foundB : record.field right = some ⟨b, second⟩)
    (distinct : left ≠ right) (aSize : 0 < a.width) (bSize : 0 < b.width) :
    first.start + a.width ≤ second.start ∨ second.start + b.width ≤ first.start := by
  obtain ⟨declaredA, placeA, _, projectedA, startA, widthA⟩ := field_coordinates foundA
  obtain ⟨declaredB, placeB, _, projectedB, startB, widthB⟩ := field_coordinates foundB
  have apart := resolve_disjoint_paths record.conforms projectedA projectedB
    (PackedSchema.paths_incomparable declaredA declaredB distinct) (by omega) (by omega)
  change placeA.bitStart + _ ≤ placeB.bitStart ∨ placeB.bitStart + _ ≤ placeA.bitStart at apart
  omega

def PackedRecord.readImage (record : PackedRecord abi schema) (image : Image record.layout.size)
    (path : List Nat) : Option Nat := do
  let ⟨ty, field⟩ ← record.field path
  let value ← field.load ty.codec image
  return value.val.toNat

def PackedRecord.writeImage (record : PackedRecord abi schema) (image : Image record.layout.size)
    (path : List Nat) (code : Nat) : Option (Image record.layout.size) := do
  let ⟨ty, field⟩ ← record.field path
  let value ← ty.decodeCode code
  return field.store ty.codec image value

theorem PackedRecord.writeImage_complete (record : PackedRecord abi schema)
    (before : Image record.layout.size) {path : List Nat} {ty : PackedType} {code : Nat}
    (declared : schema.typeAt path = some ty) (fits : code < 2 ^ ty.width) (valid : ty.Represents code) :
    ∃ after, record.writeImage before path code = some after := by
  obtain ⟨field, found⟩ := record.field_complete declared
  obtain ⟨value, decoded, _⟩ := PackedType.decodeCode_complete fits valid
  exact ⟨field.store ty.codec before value, by simp [writeImage, found, decoded, bind, pure]⟩

theorem PackedRecord.readImage_typed {record : PackedRecord abi schema} {image : Image record.layout.size}
    {path : List Nat} {code : Nat} {ty : PackedType} (declared : schema.typeAt path = some ty)
    (read : record.readImage image path = some code) : code < 2 ^ ty.width ∧ ty.Represents code := by
  simp only [readImage, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at read
  obtain ⟨⟨actual, field⟩, found, value, _, rfl⟩ := read
  have equal := Option.some.inj ((field_coordinates found).1.symm.trans declared)
  cases equal
  exact ⟨value.val.isLt, value.property⟩

theorem PackedRecord.readImage_declared {record : PackedRecord abi schema} {image : Image record.layout.size}
    {path : List Nat} {code : Nat} (read : record.readImage image path = some code) :
    ∃ ty, schema.typeAt path = some ty := by
  obtain ⟨⟨ty, field⟩, found, _⟩ := Option.bind_eq_some_iff.mp read
  exact ⟨ty, (field_coordinates found).1⟩

theorem PackedRecord.readImage_after_write {record : PackedRecord abi schema}
    {before after : Image record.layout.size} {path : List Nat} {code : Nat}
    (written : record.writeImage before path code = some after) :
    record.readImage after path = some code := by
  simp only [writeImage, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at written
  obtain ⟨⟨ty, field⟩, found, value, decoded, rfl⟩ := written
  simp [readImage, found, bind, field.load_store, PackedType.decodeCode_sound decoded]

theorem PackedRecord.writeImage_frame {record : PackedRecord abi schema}
    {before after : Image record.layout.size} {path other : List Nat} {code : Nat}
    (written : record.writeImage before path code = some after) (distinct : path ≠ other) :
    record.readImage after other = record.readImage before other := by
  simp only [writeImage, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at written
  obtain ⟨⟨a, first⟩, foundA, value, _, rfl⟩ := written
  cases foundB : record.field other with
  | none => simp [readImage, foundB, bind]
  | some result =>
    obtain ⟨b, second⟩ := result
    simp only [readImage, foundB, bind, Option.bind_some]
    have frame : second.load b.codec (first.store a.codec before value) = second.load b.codec before := by
      by_cases sizeA : 0 < a.width
      · by_cases sizeB : 0 < b.width
        · exact first.load_store_other second a.codec b.codec before value
            (fields_disjoint foundA foundB distinct sizeA sizeB)
        · have zero : b.width = 0 := by omega
          unfold PackedValueField.load
          congr 1
          exact BitVec.eq_of_getLsbD_eq (fun i hi => (by omega : False).elim)
      · have zero : a.width = 0 := by omega
        have unchanged : first.store a.codec before value = before := by
          funext byte
          simp [PackedValueField.store, Image.writeBytes, zero]
        rw [unchanged]
    rw [frame]

private def PackedRecord.writeInitial (record : PackedRecord abi schema)
    (values : List Nat → Option Nat) (before : Image record.layout.size) (path : List Nat) :
    Option (Image record.layout.size) := do
  record.writeImage before path (← values path)

/-- Canonical initializer images start at zero and insert the represented
code of each declaration at its resolved bit interval. -/
inductive PackedRecord.InitialBits (record : PackedRecord abi schema)
    (values : List Nat → Option Nat) :
    Image record.layout.size → List (List Nat) → Image record.layout.size → Prop where
  | nil : InitialBits record values image [] image
  | cons {field : PackedValueField record.layout.size ty.width}
      (located : record.field path = some ⟨ty, field⟩) (supplied : values path = some code)
      (fits : code < 2 ^ ty.width) (valid : ty.Represents code)
      (rest : InitialBits record values
        (before.writeBits field.start (BitVec.ofNatLT code fits)) paths after) :
      InitialBits record values before (path :: paths) after

private theorem PackedRecord.writeInitial_correct (record : PackedRecord abi schema)
    (values : List Nat → Option Nat) (paths : List (List Nat))
    (before after : Image record.layout.size) :
    paths.foldlM (record.writeInitial values) before = some after ↔ record.InitialBits values before paths after := by
  constructor
  · intro written
    induction paths generalizing before with
    | nil => cases written; exact .nil
    | cons path paths ih =>
      rw [List.foldlM_cons] at written
      obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp written
      obtain ⟨code, supplied, update⟩ := Option.bind_eq_some_iff.mp first
      simp only [writeImage, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at update
      obtain ⟨⟨ty, field⟩, located, value, decoded, rfl⟩ := update
      have same := PackedType.decodeCode_sound decoded
      subst code
      refine .cons located supplied value.val.isLt value.property (ih _ ?_)
      have encoded : ty.codec.encode value = BitVec.ofNatLT _ value.val.isLt :=
        BitVec.eq_of_toNat_eq rfl
      simpa only [PackedValueField.store, Image.writeBytes_refines, encoded] using rest
  · intro written
    induction written with
    | nil => rfl
    | cons located supplied fits valid _ ih =>
      obtain ⟨value, decoded, exactCode⟩ := PackedType.decodeCode_complete fits valid
      have exactBits : value.val = BitVec.ofNatLT _ fits := BitVec.eq_of_toNat_eq exactCode
      rw [List.foldlM_cons]
      apply Option.bind_eq_some_iff.mpr
      refine ⟨_, ?_, ih⟩
      simp [writeInitial, supplied, writeImage, located, decoded, bind, pure,
        PackedValueField.store, Image.writeBytes_refines]
      rw [← exactBits]
      rfl

private theorem PackedRecord.writeInitial_refines (record : PackedRecord abi schema)
    (values : List Nat → Option Nat) (paths : List (List Nat))
    {before after : Image record.layout.size}
    (written : paths.foldlM (record.writeInitial values) before = some after) :
    (∀ key ∈ paths, ∃ code, values key = some code ∧ record.readImage after key = some code) ∧
      ∀ key ∉ paths, record.readImage after key = record.readImage before key := by
  induction paths generalizing before with
  | nil => cases written; simp
  | cons path rest ih =>
    rw [List.foldlM_cons] at written
    obtain ⟨middle, first, tail⟩ := Option.bind_eq_some_iff.mp written
    obtain ⟨code, lookup, update⟩ := Option.bind_eq_some_iff.mp first
    obtain ⟨covered, framed⟩ := ih tail
    constructor
    · intro key member
      by_cases inTail : key ∈ rest
      · exact covered key inTail
      · have same := (List.mem_cons.mp member).resolve_right inTail
        subst key
        exact ⟨code, lookup, (framed path inTail).trans (readImage_after_write update)⟩
    · intro key absent
      rw [List.mem_cons, not_or] at absent
      exact (framed key absent.2).trans (writeImage_frame update (Ne.symm absent.1))

private theorem PackedRecord.writeInitial_complete (record : PackedRecord abi schema)
    (values : List Nat → Option Nat) (paths : List (List Nat)) (before : Image record.layout.size)
    (typed : ∀ path ∈ paths, ∃ ty code, schema.typeAt path = some ty ∧ values path = some code ∧
      code < 2 ^ ty.width ∧ ty.Represents code) :
    ∃ after, paths.foldlM (record.writeInitial values) before = some after := by
  induction paths generalizing before with
  | nil => exact ⟨before, rfl⟩
  | cons path rest ih =>
    obtain ⟨ty, code, declared, lookup, fits, valid⟩ := typed path (by simp)
    obtain ⟨middle, stored⟩ := record.writeImage_complete before declared fits valid
    obtain ⟨after, written⟩ := ih middle (fun key member => typed key (by simp [member]))
    exact ⟨after, by simp [List.foldlM_cons, writeInitial, lookup, stored, written, bind]⟩

def PackedRecord.initialize (record : PackedRecord abi schema) (state : State)
    (values : List Nat → Option Nat) : Option State := do
  let image ← schema.paths.foldlM (record.writeInitial values) (fun _ => 0)
  execute state (.alloc record.owner image.toBytes)

theorem PackedRecord.initialize_sound (record : PackedRecord abi schema)
    {state next : State} {values : List Nat → Option Nat}
    (initialized : record.initialize state values = some next) :
    ∃ image : Image record.layout.size,
      Step state (.alloc record.owner image.toBytes) next ∧
      ∀ path ty, schema.typeAt path = some ty →
        ∃ value, values path = some value ∧ record.readImage image path = some value := by
  obtain ⟨image, written, ran⟩ := Option.bind_eq_some_iff.mp initialized
  exact ⟨image, execute_sound ran, fun path _ declared =>
    (record.writeInitial_refines values schema.paths written).1 path (PackedSchema.mem_paths declared)⟩

/-- A supplied code for every declared leaf and a fresh owner suffice to allocate
an initialized packed record. The typed representation of each value is independent
of the image construction and covers zero-width fields. -/
theorem PackedRecord.initialize_complete (record : PackedRecord abi schema) (state : State)
    (values : List Nat → Option Nat) (fresh : record.owner ∉ state.issued)
    (typed : ∀ path ty, schema.typeAt path = some ty →
      ∃ code, values path = some code ∧ code < 2 ^ ty.width ∧ ty.Represents code) :
    ∃ next, record.initialize state values = some next := by
  obtain ⟨image, written⟩ := record.writeInitial_complete values schema.paths (fun _ => 0) (by
    intro path member
    obtain ⟨ty, declared⟩ := PackedSchema.typeAt_of_mem_paths member
    obtain ⟨code, lookup, fits, valid⟩ := typed path ty declared
    exact ⟨ty, code, declared, lookup, fits, valid⟩)
  exact ⟨state.addAllocation record.owner image.toBytes,
    Option.bind_eq_some_iff.mpr ⟨image, written, execute_complete (.alloc fresh)⟩⟩

private def PackedRecord.readAs (record : PackedRecord abi schema) (state : State) (path : List Nat)
    (targets : List AccessTarget) (project : (ty : PackedType) → ty.Value → α) : Option α := do
  let ⟨ty, field⟩ ← record.field path
  let value ← field.readMachine ty.codec state record.owner targets
  return project ty value

private def PackedRecord.read (record : PackedRecord abi schema) (state : State) (path : List Nat)
    (targets : List AccessTarget) : Option Nat :=
  record.readAs state path targets (fun _ value => value.val.toNat)

private def PackedRecord.write (record : PackedRecord abi schema) (state : State) (path : List Nat)
    (targets : List AccessTarget) (code : Nat) : Option State := do
  let ⟨ty, field⟩ ← record.field path
  let value ← ty.decodeCode code
  field.writeMachine ty.codec state record.owner targets value

structure PackedRecord.Scope where
  view : RecordView
  parent : Option Nat := none

/-- Variant generations are tied to the record identity and logical field.
An epoch changes on each replacement, including replacement by the same tag. -/
structure PackedRecord.Memory (record : PackedRecord abi schema) where
  private mk ::
  heap : State
  generation : List Nat → Nat
  scopes : List (Nat × PackedRecord.Scope) := []
  nextScope : Nat := 0

private def PackedRecord.Memory.seed {record : PackedRecord abi schema} (heap : State) : record.Memory :=
  { heap, generation := fun _ => 0 }

def PackedRecord.allocate (record : PackedRecord abi schema) (state : State)
    (values : List Nat → Option Nat) : Option record.Memory :=
  (record.initialize state values).map Memory.seed

def PackedRecord.Initialized (record : PackedRecord abi schema) (state : State)
    (values : List Nat → Option Nat) (memory : record.Memory) : Prop :=
  ∃ image, record.InitialBits values (fun _ => 0) schema.paths image ∧
    Step state (.alloc record.owner image.toBytes) memory.heap ∧ memory = Memory.seed memory.heap

theorem PackedRecord.allocate_correct (record : PackedRecord abi schema) (state : State)
    (values : List Nat → Option Nat) (memory : record.Memory) :
    record.allocate state values = some memory ↔ record.Initialized state values memory := by
  constructor
  · intro allocated
    obtain ⟨heap, ran, rfl⟩ := Option.map_eq_some_iff.mp allocated
    obtain ⟨image, written, allocated⟩ := Option.bind_eq_some_iff.mp ran
    exact ⟨image, (record.writeInitial_correct values schema.paths _ _).mp written, execute_sound allocated, rfl⟩
  · intro initialized
    obtain ⟨image, written, created, canonical⟩ := initialized
    exact Option.map_eq_some_iff.mpr ⟨memory.heap, Option.bind_eq_some_iff.mpr
      ⟨image, (record.writeInitial_correct values schema.paths _ _).mpr written, execute_complete created⟩,
      canonical.symm⟩

theorem PackedRecord.allocate_complete (record : PackedRecord abi schema) (state : State)
    (values : List Nat → Option Nat) (fresh : record.owner ∉ state.issued)
    (typed : ∀ path ty, schema.typeAt path = some ty →
      ∃ code, values path = some code ∧ code < 2 ^ ty.width ∧ ty.Represents code) :
    ∃ memory, record.allocate state values = some memory := by
  obtain ⟨heap, initialized⟩ := record.initialize_complete state values fresh typed
  exact ⟨_, Option.map_eq_some_iff.mpr ⟨heap, initialized, rfl⟩⟩

theorem PackedRecord.allocate_on_image {record : PackedRecord abi schema} {state : State}
    {values : List Nat → Option Nat} {memory : record.Memory}
    (allocated : record.allocate state values = some memory) :
    ∃ image, image.InAllocation record.owner memory.heap ∧
      ∀ path ty, schema.typeAt path = some ty →
        ∃ value, values path = some value ∧ record.readImage image path = some value := by
  obtain ⟨heap, initialized, equal⟩ := Option.map_eq_some_iff.mp allocated
  obtain ⟨image, created, contents⟩ := record.initialize_sound initialized
  cases equal
  exact ⟨image, Image.inAllocation_of_alloc created, contents⟩

theorem PackedRecord.allocate_kernel {record : PackedRecord abi schema} {state : State}
    {values : List Nat → Option Nat} {memory : record.Memory}
    (allocated : record.allocate state values = some memory) :
    ∃ image : Image record.layout.size, Step state (.alloc record.owner image.toBytes) memory.heap := by
  obtain ⟨_, initialized, equal⟩ := Option.map_eq_some_iff.mp allocated
  cases equal
  obtain ⟨image, created, _⟩ := record.initialize_sound initialized
  exact ⟨image, created⟩

def PackedRecord.Memory.allocationInstruction {record : PackedRecord abi schema} (memory : record.Memory) :
    Option Instruction :=
  (memory.heap.allocation record.owner).map fun allocation => .alloc record.owner allocation.bytes

theorem PackedRecord.allocationInstruction_correct {record : PackedRecord abi schema} {state : State}
    {values : List Nat → Option Nat} {memory : record.Memory}
    (allocated : record.allocate state values = some memory) :
    ∃ instruction, memory.allocationInstruction = some instruction ∧ Step state instruction memory.heap := by
  obtain ⟨image, created⟩ := PackedRecord.allocate_kernel allocated
  have located {next : State} (step : Step state (.alloc record.owner image.toBytes) next) :
      next.allocation record.owner = some ⟨record.owner, image.toBytes⟩ := by
    cases step
    simp [State.allocation, State.addAllocation]
  exact ⟨_, by simp [PackedRecord.Memory.allocationInstruction, located created], created⟩

private def PackedRecord.Memory.write {record : PackedRecord abi schema} (memory : record.Memory)
    (path : List Nat) (targets : List AccessTarget) (code : Nat) : Option record.Memory := do
  let heap ← record.write memory.heap path targets code
  return { memory with heap, generation := fun key =>
    if key = path then memory.generation path + 1 else memory.generation key }

def PackedRecord.Memory.openScope {record : PackedRecord abi schema} (memory : record.Memory)
    (path : List Nat) (mode : AccessMode) : Option (Nat × record.Memory) := do
  let (scope, heap) ← openLayoutView record.owner record.layout memory.heap path mode
  let id := memory.nextScope
  let opened := { memory with
    heap
    scopes := (id, ⟨scope, none⟩) :: memory.scopes
    nextScope := id + 1 }
  return (id, opened)

private def PackedRecord.Memory.activeScope? {record : PackedRecord abi schema}
    (memory : record.Memory) (id : Nat) : Option PackedRecord.Scope :=
  if memory.scopes.any (fun entry => entry.2.parent == some id) then none
  else (memory.scopes.find? fun entry => entry.1 == id).map Prod.snd

private def PackedRecord.Memory.scope? {record : PackedRecord abi schema} (memory : record.Memory)
    (id : Nat) : Option RecordView :=
  (memory.activeScope? id).map Scope.view

def PackedRecord.Memory.scopeActive {record : PackedRecord abi schema} (memory : record.Memory)
    (id : Nat) : Bool :=
  (memory.scope? id).isSome

def PackedRecord.Memory.reborrowScope {record : PackedRecord abi schema} (memory : record.Memory)
    (parent : Nat) (path : List Nat) (mode : AccessMode) : Option (Nat × record.Memory) := do
  let view ← memory.scope? parent
  let child ← reborrowLayoutView view record.owner record.layout memory.heap path mode
  let id := memory.nextScope
  let opened := { memory with
    scopes := (id, ⟨child, some parent⟩) :: memory.scopes
    nextScope := id + 1 }
  return (id, opened)

def PackedRecord.Memory.closeScope {record : PackedRecord abi schema} (memory : record.Memory)
    (id : Nat) : Option record.Memory := do
  let scope ← memory.activeScope? id
  let heap ← if scope.parent.isSome then some memory.heap else closeView scope.view memory.heap
  return { memory with heap, scopes := memory.scopes.filter fun entry => entry.1 != id }

theorem PackedRecord.Memory.openScope_allocations {record : PackedRecord abi schema}
    {memory next : record.Memory} {path : List Nat} {mode : AccessMode} {id : Nat}
    (opened : memory.openScope path mode = some (id, next)) :
    next.heap.allocations = memory.heap.allocations := by
  obtain ⟨⟨scope, heap⟩, acquired, equal⟩ := Option.bind_eq_some_iff.mp opened
  cases equal
  exact openLayoutView_allocations acquired

theorem PackedRecord.Memory.reborrowScope_heap {record : PackedRecord abi schema}
    {memory next : record.Memory} {parent id : Nat} {path : List Nat} {mode : AccessMode}
    (opened : memory.reborrowScope parent path mode = some (id, next)) :
    next.heap = memory.heap := by
  obtain ⟨_, _, child⟩ := Option.bind_eq_some_iff.mp opened
  obtain ⟨_, _, equal⟩ := Option.bind_eq_some_iff.mp child
  cases equal
  rfl

theorem PackedRecord.Memory.reborrowScope_allocations {record : PackedRecord abi schema}
    {memory next : record.Memory} {parent id : Nat} {path : List Nat} {mode : AccessMode}
    (opened : memory.reborrowScope parent path mode = some (id, next)) :
    next.heap.allocations = memory.heap.allocations :=
  congrArg State.allocations (reborrowScope_heap opened)

theorem PackedRecord.Memory.closeScope_allocations {record : PackedRecord abi schema}
    {memory next : record.Memory} {id : Nat} (closed : memory.closeScope id = some next) :
    next.heap.allocations = memory.heap.allocations := by
  obtain ⟨scope, _, restored⟩ := Option.bind_eq_some_iff.mp closed
  split at restored
  · cases restored
    rfl
  · obtain ⟨heap, released, equal⟩ := Option.bind_eq_some_iff.mp restored
    cases equal
    exact closeView_allocations released

def PackedRecord.Memory.openScopeProgram {record : PackedRecord abi schema} (memory next : record.Memory) :
    Option Program :=
  next.scopes.head?.map fun (_, scope) => scope.view.startTrace record.owner memory.heap.freshHandle

def PackedRecord.Memory.closeScopeProgram {record : PackedRecord abi schema}
    (memory : record.Memory) (id : Nat) : Option Program :=
  (memory.activeScope? id).map fun scope => if scope.parent.isSome then [] else scope.view.stopTrace

theorem PackedRecord.Memory.openScopeProgram_keepsExtents {record : PackedRecord abi schema}
    {memory next : record.Memory} {program : Program}
    (compiled : memory.openScopeProgram next = some program) :
    program.all Instruction.keepsExtents = true := by
  obtain ⟨⟨_, scope⟩, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
  simp [RecordView.startTrace, acquireViews, View.acquire, Instruction.keepsExtents, Function.comp_def]

theorem PackedRecord.Memory.closeScopeProgram_keepsExtents {record : PackedRecord abi schema}
    {memory : record.Memory} {id : Nat} {program : Program}
    (compiled : memory.closeScopeProgram id = some program) :
    program.all Instruction.keepsExtents = true := by
  obtain ⟨scope, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
  split <;> simp [RecordView.stopTrace, releaseViews, Instruction.keepsExtents, Function.comp_def]

theorem PackedRecord.Memory.openScope_kernel {record : PackedRecord abi schema}
    {memory next : record.Memory} {path : List Nat} {mode : AccessMode} {id : Nat}
    (opened : memory.openScope path mode = some (id, next)) :
    ∃ program, memory.openScopeProgram next = some program ∧ Runs memory.heap program next.heap := by
  obtain ⟨⟨_, _⟩, acquired, equal⟩ := Option.bind_eq_some_iff.mp opened
  cases equal
  exact ⟨_, rfl, (openLayoutView_sound acquired).2.2.2.1⟩

theorem PackedRecord.Memory.closeScope_kernel {record : PackedRecord abi schema}
    {memory next : record.Memory} {id : Nat} (closed : memory.closeScope id = some next) :
    ∃ program, memory.closeScopeProgram id = some program ∧ Runs memory.heap program next.heap := by
  obtain ⟨_, found, restored⟩ := Option.bind_eq_some_iff.mp closed
  split at restored
  · rename_i child
    cases restored
    exact ⟨[], by simp [closeScopeProgram, found, child], .nil⟩
  · rename_i root
    obtain ⟨_, released, equal⟩ := Option.bind_eq_some_iff.mp restored
    cases equal
    exact ⟨_, by simp [closeScopeProgram, found, root], closeView_sound released⟩

private def PackedRecord.Memory.scopeTargets {record : PackedRecord abi schema} (memory : record.Memory)
    (id : Nat) (path : List Nat) (mode : AccessMode) : Option (List AccessTarget) := do
  let scope ← memory.scope? id
  let ⟨_, field⟩ ← record.field path
  scope.targetsFor path mode field.byteOffsets

theorem PackedRecord.Memory.scopeTargets_sound {record : PackedRecord abi schema}
    {memory : record.Memory} {id : Nat} {path : List Nat} {mode : AccessMode}
    {targets : List AccessTarget} (granted : memory.scopeTargets id path mode = some targets) :
    ∃ scope, memory.scope? id = some scope ∧ scope.path <+: path ∧ scope.mode.Allows mode := by
  obtain ⟨scope, found, available⟩ := Option.bind_eq_some_iff.mp granted
  obtain ⟨field, _, used⟩ := Option.bind_eq_some_iff.mp available
  exact ⟨scope, found, RecordView.targetsFor_scope used⟩

def PackedRecord.Memory.readInScope {record : PackedRecord abi schema} (memory : record.Memory)
    (id : Nat) (path : List Nat) : Option Nat := do
  let targets ← memory.scopeTargets id path .shared
  record.read memory.heap path targets

def PackedRecord.Memory.writeInScope {record : PackedRecord abi schema} (memory : record.Memory)
    (id : Nat) (path : List Nat) (code : Nat) : Option record.Memory := do
  let targets ← memory.scopeTargets id path .exclusive
  memory.write path targets code

private theorem PackedRecord.read_on_image {record : PackedRecord abi schema}
    {heap : State} {code : Nat} {path : List Nat} {targets : List AccessTarget} {before : Image record.layout.size}
    (represented : before.InAllocation record.owner heap) (ran : record.read heap path targets = some code) :
    record.readImage before path = some code := by
  simp only [PackedRecord.read, PackedRecord.readAs, bind, pure, Option.bind_eq_some_iff,
    Option.some.injEq] at ran
  obtain ⟨⟨ty, field⟩, found, value, read, rfl⟩ := ran
  have loaded := field.readMachine_on_image ty.codec represented read
  simp [PackedRecord.readImage, found, loaded, bind]

theorem PackedRecord.Memory.readInScope_on_image {record : PackedRecord abi schema}
    {memory : record.Memory} {id code : Nat} {path : List Nat} {before : Image record.layout.size}
    (represented : before.InAllocation record.owner memory.heap)
    (ran : memory.readInScope id path = some code) :
    record.readImage before path = some code := by
  obtain ⟨_, _, read⟩ := Option.bind_eq_some_iff.mp ran
  exact PackedRecord.read_on_image represented read

private theorem PackedRecord.read_kernel {record : PackedRecord abi schema}
    {state : State} {path : List Nat} {targets : List AccessTarget} {code : Nat}
    (read : record.read state path targets = some code) :
    RunsOnStorage state (targets.map AccessTarget.readInstruction) state := by
  simp only [PackedRecord.read, PackedRecord.readAs, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at read
  obtain ⟨⟨ty, field⟩, _, _, loaded, _⟩ := read
  exact field.readMachine_on_storage ty.codec loaded

def PackedRecord.Memory.readInScopeProgram {record : PackedRecord abi schema}
    (memory : record.Memory) (id : Nat) (path : List Nat) : Option Program :=
  (memory.scopeTargets id path .shared).map (List.map AccessTarget.readInstruction)

def PackedRecord.Memory.writeInScopeProgram {record : PackedRecord abi schema}
    (memory : record.Memory) (id : Nat) (path : List Nat) (code : Nat) : Option Program := do
  let targets ← memory.scopeTargets id path .exclusive
  let ⟨ty, field⟩ ← record.field path
  let value ← ty.decodeCode code
  field.writeProgram ty.codec memory.heap record.owner targets value

def PackedRecord.Memory.writeInScopeProgramFromSamples {record : PackedRecord abi schema}
    (memory : record.Memory) (id : Nat) (path : List Nat) (code : Nat)
    (samples : List (BitVec 8)) : Option Program := do
  let targets ← memory.scopeTargets id path .exclusive
  let ⟨ty, field⟩ ← record.field path
  let value ← ty.decodeCode code
  (field.writeInstructionsFromSamples ty.codec record.owner targets value samples).map
    (field.mergeTrace targets ++ ·)

theorem PackedRecord.Memory.writeInScopeProgram_eq_fromSamples {record : PackedRecord abi schema}
    {memory : record.Memory} {id code : Nat} {path : List Nat} {ty : PackedType}
    {field : PackedValueField record.layout.size ty.width} {image : Image record.layout.size}
    {samples : List (BitVec 8)} (found : record.field path = some ⟨ty, field⟩)
    (represented : image.InAllocation record.owner memory.heap) (observed : samples = image.bytesAt field.mergeOffsets) :
    memory.writeInScopeProgram id path code = memory.writeInScopeProgramFromSamples id path code samples := by
  cases access : memory.scopeTargets id path .exclusive <;> cases value : ty.decodeCode code <;>
    simp [writeInScopeProgram, writeInScopeProgramFromSamples, access, found, value, bind,
      field.writeProgram_eq_fromSamples ty.codec represented observed]

theorem PackedRecord.Memory.writeInScopeProgram_sampling {record : PackedRecord abi schema}
    {memory next : record.Memory} {id code : Nat} {path : List Nat} {program : Program}
    (ran : memory.writeInScope id path code = some next)
    (compiled : memory.writeInScopeProgram id path code = some program) :
    ∃ reads writes samples, program = reads ++ writes ∧
      (∀ op ∈ reads, ∃ location, op.byteAccess memory.heap.resources = some (.read location)) ∧
      (∀ op ∈ writes, ∃ location byte, op.byteAccess memory.heap.resources = some (.write location byte)) ∧
      reads.mapM (Instruction.readSample memory.heap) = some samples ∧
      memory.writeInScopeProgramFromSamples id path code samples = some program := by
  simp only [writeInScope, PackedRecord.Memory.write, PackedRecord.write, bind, pure,
    Option.bind_eq_some_iff, Option.some.injEq] at ran
  obtain ⟨targets, accessed, _, ⟨⟨ty, field⟩, found, value, decoded, stored⟩, _⟩ := ran
  have compiledField : field.writeProgram ty.codec memory.heap record.owner targets value = some program := by
    simpa [writeInScopeProgram, accessed, found, decoded, bind] using compiled
  obtain ⟨samples, writes, parts, readable, writable, snapshot, rebuilt⟩ :=
    field.writeProgram_sampling ty.codec stored compiledField
  exact ⟨_, writes, samples, parts, readable, writable, snapshot,
    by simp [writeInScopeProgramFromSamples, accessed, found, decoded, rebuilt, parts, bind]⟩

theorem PackedRecord.Memory.readInScopeProgram_accesses {record : PackedRecord abi schema}
    {memory : record.Memory} {id : Nat} {path : List Nat} {program : Program}
    (compiled : memory.readInScopeProgram id path = some program) :
    program.all Instruction.isByteAccess = true := by
  obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp compiled
  exact readInstructions_are_byteAccesses _

theorem PackedRecord.Memory.writeInScopeProgram_accesses {record : PackedRecord abi schema}
    {memory : record.Memory} {id code : Nat} {path : List Nat} {program : Program}
    (compiled : memory.writeInScopeProgram id path code = some program) :
    program.all Instruction.isByteAccess = true := by
  simp only [writeInScopeProgram, bind, Option.bind_eq_some_iff] at compiled
  obtain ⟨_, _, ⟨ty, field⟩, _, _, _, writes⟩ := compiled
  exact field.writeProgram_accesses ty.codec writes

theorem PackedRecord.Memory.readInScope_kernel {record : PackedRecord abi schema}
    {memory : record.Memory} {id code : Nat} {path : List Nat}
    (ran : memory.readInScope id path = some code) :
    ∃ program, memory.readInScopeProgram id path = some program ∧
      RunsOnStorage memory.heap program memory.heap := by
  obtain ⟨_, accessed, read⟩ := Option.bind_eq_some_iff.mp ran
  exact ⟨_, by simp [readInScopeProgram, accessed], PackedRecord.read_kernel read⟩

theorem PackedRecord.Memory.writeInScope_kernel {record : PackedRecord abi schema}
    {memory next : record.Memory} {id code : Nat} {path : List Nat}
    (ran : memory.writeInScope id path code = some next) :
    ∃ program, memory.writeInScopeProgram id path code = some program ∧ Runs memory.heap program next.heap := by
  simp only [writeInScope, PackedRecord.Memory.write, PackedRecord.write, bind, pure,
    Option.bind_eq_some_iff, Option.some.injEq] at ran
  obtain ⟨_, accessed, _, ⟨⟨ty, field⟩, found, _, decoded, stored⟩, rfl⟩ := ran
  obtain ⟨_, compiled, traced⟩ := field.writeProgram_correct ty.codec stored
  exact ⟨_, by simp [writeInScopeProgram, accessed, found, decoded, compiled, bind], traced⟩

theorem PackedRecord.Memory.readInScopeProgram_footprint {record : PackedRecord abi schema}
    {memory : record.Memory} {id code : Nat} {path : List Nat} {program : Program}
    {ty : PackedType} {field : PackedValueField record.layout.size ty.width}
    (found : record.field path = some ⟨ty, field⟩)
    (ran : memory.readInScope id path = some code)
    (compiled : memory.readInScopeProgram id path = some program) :
    ScopedForkJoin.TaskFootprint.ofProgram memory.heap.resources program =
      some (field.footprint record.owner .shared) := by
  simp only [readInScope, PackedRecord.read, PackedRecord.readAs, found, bind, pure, Option.bind_eq_some_iff,
    Option.some.injEq] at ran
  obtain ⟨targets, accessed, _, rfl, value, loaded, _⟩ := ran
  simp only [readInScopeProgram, accessed, Option.map_some, Option.some.injEq] at compiled
  subst program
  exact field.readProgram_footprint (field.readMachine_authorized ty.codec loaded)

theorem PackedRecord.Memory.writeInScopeProgram_footprint {record : PackedRecord abi schema}
    {memory next : record.Memory} {id code : Nat} {path : List Nat} {program : Program}
    {ty : PackedType} {field : PackedValueField record.layout.size ty.width}
    (found : record.field path = some ⟨ty, field⟩)
    (ran : memory.writeInScope id path code = some next)
    (compiled : memory.writeInScopeProgram id path code = some program) :
    ScopedForkJoin.TaskFootprint.ofProgram memory.heap.resources program =
      some (field.footprint record.owner .exclusive) := by
  simp only [writeInScope, PackedRecord.Memory.write, PackedRecord.write, found, bind, pure,
    Option.bind_eq_some_iff, Option.some.injEq] at ran
  obtain ⟨targets, accessed, updated, ⟨_, rfl, value, decoded, stored⟩, _⟩ := ran
  have allowed := (field.writeMachine_refines ty.codec stored).1
  exact field.writeProgram_footprint ty.codec allowed (value := value) (by
    simpa [writeInScopeProgram, accessed, found, decoded, bind] using compiled)

theorem PackedRecord.Memory.writeInScope_on_image {record : PackedRecord abi schema}
    {memory next : record.Memory} {id code : Nat} {path : List Nat} {before : Image record.layout.size}
    (represented : before.InAllocation record.owner memory.heap)
    (ran : memory.writeInScope id path code = some next) :
    ∃ after, record.writeImage before path code = some after ∧
      after.InAllocation record.owner next.heap := by
  simp only [writeInScope, PackedRecord.Memory.write, PackedRecord.write, bind, pure,
    Option.bind_eq_some_iff, Option.some.injEq] at ran
  obtain ⟨_, _, _, ⟨⟨ty, field⟩, found, value, decoded, written⟩, rfl⟩ := ran
  exact ⟨field.store ty.codec before value, by simp [PackedRecord.writeImage, found, decoded, bind],
    field.writeMachine_on_image ty.codec represented written⟩

/-- Metadata that authorizes an access. Byte contents and the generation
counters for typed projections are irrelevant to ordinary leaf authority. -/
def PackedRecord.Memory.authority {record : PackedRecord abi schema} (memory : record.Memory) :
    List (Nat × PackedRecord.Scope) × Nat × ResourceState :=
  (memory.scopes, memory.nextScope, memory.heap.resources)

private theorem PackedRecord.Memory.scopeTargets_of_authority {record : PackedRecord abi schema}
    {memory next : record.Memory} (same : next.authority = memory.authority)
    (id : Nat) (path : List Nat) (mode : AccessMode) :
    next.scopeTargets id path mode = memory.scopeTargets id path mode := by
  have scopes : next.scopes = memory.scopes := congrArg Prod.fst same
  simp only [scopeTargets, scope?, activeScope?, scopes]

theorem PackedRecord.Memory.sampledProgram_of_authority {record : PackedRecord abi schema}
    {memory next : record.Memory} (same : next.authority = memory.authority)
    (id : Nat) (path : List Nat) (code : Nat) (samples : List (BitVec 8)) :
    next.writeInScopeProgramFromSamples id path code samples =
      memory.writeInScopeProgramFromSamples id path code samples := by
  simp only [writeInScopeProgramFromSamples, scopeTargets_of_authority same id path .exclusive]

theorem PackedRecord.Memory.writeInScope_preserves_authority {record : PackedRecord abi schema}
    {memory next : record.Memory} {id code : Nat} {path : List Nat}
    (ran : memory.writeInScope id path code = some next) : next.authority = memory.authority := by
  simp only [writeInScope, PackedRecord.Memory.write, PackedRecord.write, bind, pure,
    Option.bind_eq_some_iff, Option.some.injEq] at ran
  obtain ⟨_, _, _, ⟨⟨ty, field⟩, _, value, _, written⟩, rfl⟩ := ran
  simp only [authority, field.writeMachine_preserves_resources ty.codec written]

theorem PackedRecord.Memory.writeInScope_generation {record : PackedRecord abi schema}
    {memory next : record.Memory} {id code : Nat} {path : List Nat}
    (ran : memory.writeInScope id path code = some next) (key : List Nat) :
    next.generation key = memory.generation key + (if key = path then 1 else 0) := by
  simp only [writeInScope, PackedRecord.Memory.write, bind, pure,
    Option.bind_eq_some_iff, Option.some.injEq] at ran
  obtain ⟨_, _, _, _, rfl⟩ := ran
  by_cases same : key = path <;> simp [same]

theorem PackedRecord.Memory.readInScope_transfer {record : PackedRecord abi schema}
    {memory next : record.Memory} {id oldCode code : Nat} {path : List Nat}
    {image : Image record.layout.size} (same : next.authority = memory.authority)
    (ran : memory.readInScope id path = some oldCode)
    (represented : image.InAllocation record.owner next.heap)
    (loaded : record.readImage image path = some code) : next.readInScope id path = some code := by
  simp only [readInScope, PackedRecord.read, PackedRecord.readAs, bind, pure, Option.bind_eq_some_iff,
    Option.some.injEq] at ran
  obtain ⟨_, available, ⟨ty, field⟩, found, _, read, _⟩ := ran
  simp only [PackedRecord.readImage, found, bind, pure, Option.bind_eq_some_iff,
    Option.some.injEq] at loaded
  obtain ⟨_, rfl, value, decoded, rfl⟩ := loaded
  have fetched := field.readMachine_transfer ty.codec read (congrArg (fun a => a.2.2) same)
    represented decoded
  simp [readInScope, scopeTargets_of_authority same id path .shared, PackedRecord.read, PackedRecord.readAs,
    available, found, fetched, bind]

theorem PackedRecord.Memory.writeInScope_transfer {record : PackedRecord abi schema}
    {memory next final : record.Memory} {id code : Nat} {path : List Nat}
    {image : Image record.layout.size} (same : next.authority = memory.authority)
    (ran : memory.writeInScope id path code = some final)
    (represented : image.InAllocation record.owner next.heap) :
    ∃ result, next.writeInScope id path code = some result := by
  simp only [writeInScope, PackedRecord.Memory.write, PackedRecord.write, bind, pure,
    Option.bind_eq_some_iff, Option.some.injEq] at ran
  obtain ⟨_, available, _, ⟨⟨ty, field⟩, found, _, decoded, written⟩, _⟩ := ran
  obtain ⟨_, updated⟩ := field.writeMachine_transfer ty.codec written
    (congrArg (fun a => a.2.2) same) represented
  simp [writeInScope, scopeTargets_of_authority same id path .exclusive,
    PackedRecord.Memory.write, PackedRecord.write, available, found, decoded, updated, bind, pure]

structure PackedRecord.PayloadRef (record : PackedRecord abi schema) where
  private mk ::
  path : List Nat
  generation : Nat
  tag : Nat

private def PackedRecord.Memory.taggedCode {record : PackedRecord abi schema}
    (memory : record.Memory) (path : List Nat) (targets : List AccessTarget) :
    Option (PackedType × Nat × Nat) := do
  let (ty, code) ← record.readAs memory.heap path targets (fun ty value => (ty, value.val.toNat))
  let (tag, data) ← ty.splitTag code
  return (ty, tag, data)

private theorem PackedRecord.Memory.taggedCode_source {record : PackedRecord abi schema}
    {memory : record.Memory} {path : List Nat} {targets : List AccessTarget}
    {ty : PackedType} {tag data : Nat} (ran : memory.taggedCode path targets = some (ty, tag, data)) :
    ∃ code, schema.typeAt path = some ty ∧ record.read memory.heap path targets = some code ∧
      ty.Represents code ∧ ty.splitTag code = some (tag, data) := by
  simp only [taggedCode, PackedRecord.readAs, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at ran
  obtain ⟨⟨_, _⟩, ⟨⟨ty, field⟩, found, value, loaded, equal⟩, ⟨_, _⟩, split, result⟩ := ran
  cases equal
  cases result
  exact ⟨value.val.toNat, (field_coordinates found).1,
    by simp [PackedRecord.read, PackedRecord.readAs, found, loaded, bind, pure], value.property, split⟩

private theorem PackedRecord.Memory.taggedCode_of_read {record : PackedRecord abi schema}
    {memory : record.Memory} {path : List Nat} {targets : List AccessTarget}
    {ty : PackedType} {code tag data : Nat} (declared : schema.typeAt path = some ty)
    (loaded : record.read memory.heap path targets = some code)
    (split : ty.splitTag code = some (tag, data)) :
    memory.taggedCode path targets = some (ty, tag, data) := by
  simp only [PackedRecord.read, PackedRecord.readAs, bind, pure, Option.bind_eq_some_iff,
    Option.some.injEq] at loaded
  obtain ⟨⟨actual, field⟩, found, value, loaded, rfl⟩ := loaded
  have same := Option.some.inj ((field_coordinates found).1.symm.trans declared)
  cases same
  simp [taggedCode, PackedRecord.readAs, found, loaded, split, bind, pure]

private def PackedRecord.Memory.openPayload {record : PackedRecord abi schema}
    (memory : record.Memory) (path : List Nat) (targets : List AccessTarget) : Option record.PayloadRef := do
  let (_, tag, _) ← memory.taggedCode path targets
  return ⟨path, memory.generation path, tag⟩

private def PackedRecord.Memory.readPayload {record : PackedRecord abi schema} (memory : record.Memory)
    (payload : record.PayloadRef) (targets : List AccessTarget) : Option (PackedType × Nat) := do
  if payload.generation = memory.generation payload.path then
    let (ty, tag, value) ← memory.taggedCode payload.path targets
    if tag = payload.tag then some (ty, value) else none
  else none

def PackedRecord.Memory.openPayloadInScope {record : PackedRecord abi schema} (memory : record.Memory)
    (id : Nat) (path : List Nat) : Option record.PayloadRef := do
  let targets ← memory.scopeTargets id path .shared
  memory.openPayload path targets

private def PackedRecord.Memory.readPayloadWithType {record : PackedRecord abi schema}
    (memory : record.Memory) (id : Nat) (payload : record.PayloadRef) : Option (PackedType × Nat) := do
  let targets ← memory.scopeTargets id payload.path .shared
  memory.readPayload payload targets

def PackedRecord.Memory.readPayloadInScope {record : PackedRecord abi schema}
    (memory : record.Memory) (id : Nat) (payload : record.PayloadRef) : Option Nat :=
  (memory.readPayloadWithType id payload).map Prod.snd

private theorem PackedRecord.Memory.readPayloadWithType_source {record : PackedRecord abi schema}
    {memory : record.Memory} {id data : Nat} {ty : PackedType} {payload : record.PayloadRef}
    (read : memory.readPayloadWithType id payload = some (ty, data)) :
    ∃ targets code, memory.scopeTargets id payload.path .shared = some targets ∧
      payload.generation = memory.generation payload.path ∧ schema.typeAt payload.path = some ty ∧
      record.read memory.heap payload.path targets = some code ∧
      ty.Represents code ∧ ty.splitTag code = some (payload.tag, data) := by
  simp only [readPayloadWithType, readPayload, bind, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some] at read
  obtain ⟨targets, available, generation, ⟨actual, tag, value⟩, tagged, equalTag, equalCode⟩ := read
  cases equalTag
  cases equalCode
  obtain ⟨code, declared, loaded, valid, split⟩ := taggedCode_source tagged
  exact ⟨targets, code, available, generation, declared, loaded, valid, split⟩

theorem PackedRecord.Memory.readPayloadInScope_typed {record : PackedRecord abi schema}
    {memory : record.Memory} {id code : Nat} {payload : record.PayloadRef}
    (read : memory.readPayloadInScope id payload = some code) :
    ∃ ty selected, schema.typeAt payload.path = some ty ∧
      ty.payloadTypeAt payload.tag = some selected ∧ selected.Represents code := by
  obtain ⟨⟨ty, data⟩, loaded, rfl⟩ := Option.map_eq_some_iff.mp read
  obtain ⟨_, _, _, _, declared, _, valid, split⟩ := readPayloadWithType_source loaded
  obtain ⟨selected, selection, represented⟩ := PackedType.splitTag_typed valid split
  exact ⟨ty, selected, declared, selection, represented⟩

/-- Project a typed subfield after the live capture has authorized the full
tagged leaf read. The selector itself performs no memory access. -/
def PackedRecord.Memory.readPayloadFieldInScope {record : PackedRecord abi schema}
    (memory : record.Memory) (id : Nat) (payload : record.PayloadRef)
    (steps : List PackedType.FieldStep) : Option Nat := do
  let (ty, code) ← memory.readPayloadWithType id payload
  ty.payloadFieldCode payload.tag code steps

theorem PackedRecord.Memory.readPayloadFieldInScope_live {record : PackedRecord abi schema}
    {memory : record.Memory} {id code : Nat} {payload : record.PayloadRef}
    {steps : List PackedType.FieldStep}
    (read : memory.readPayloadFieldInScope id payload steps = some code) :
    payload.generation = memory.generation payload.path ∧
      ∃ scope, memory.scope? id = some scope ∧ scope.path <+: payload.path ∧ scope.mode.Allows .shared := by
  obtain ⟨⟨_, _⟩, loaded, _⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨_, _, available, generation, _, _, _, _⟩ := readPayloadWithType_source loaded
  exact ⟨generation, scopeTargets_sound available⟩

theorem PackedRecord.Memory.readPayloadFieldInScope_typed {record : PackedRecord abi schema}
    {memory : record.Memory} {id code : Nat} {payload : record.PayloadRef}
    {steps : List PackedType.FieldStep}
    (read : memory.readPayloadFieldInScope id payload steps = some code) :
    ∃ ty selected offset field data, schema.typeAt payload.path = some ty ∧
      ty.payloadTypeAt payload.tag = some selected ∧ selected.fieldAt steps = some (offset, field) ∧
      memory.readPayloadInScope id payload = some data ∧ offset + field.width ≤ selected.width ∧
      code = packedCodeSlice data offset field.width ∧ field.Represents code := by
  simp only [readPayloadFieldInScope, PackedType.payloadFieldCode, bind, pure, Option.bind_eq_some_iff,
    Option.some.injEq] at read
  obtain ⟨⟨ty, data⟩, fetched, selected, chosen, ⟨offset, field⟩, located, rfl⟩ := read
  obtain ⟨_, _, _, _, declared, _, wholeValid, split⟩ := readPayloadWithType_source fetched
  obtain ⟨actual, inferred, valid⟩ := PackedType.splitTag_typed wholeValid split
  rw [chosen] at inferred
  cases inferred
  obtain ⟨within, represents⟩ := PackedType.fieldAt_sound located valid
  exact ⟨ty, selected, offset, field, data, declared, chosen, located,
    by simp [readPayloadInScope, fetched], within, rfl, represents⟩

theorem PackedRecord.Memory.readPayloadFieldInScope_on_image {record : PackedRecord abi schema}
    {memory : record.Memory} {id code : Nat} {payload : record.PayloadRef}
    {steps : List PackedType.FieldStep} {image : Image record.layout.size}
    (represented : image.InAllocation record.owner memory.heap)
    (read : memory.readPayloadFieldInScope id payload steps = some code) :
    ∃ ty whole, schema.typeAt payload.path = some ty ∧ record.readImage image payload.path = some whole ∧
      ty.projectTaggedCode payload.tag whole steps = some code := by
  obtain ⟨⟨ty, data⟩, loaded, projected⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨_, whole, _, _, declared, ran, _, split⟩ := readPayloadWithType_source loaded
  exact ⟨ty, whole, declared, PackedRecord.read_on_image represented ran,
    by simpa [PackedType.projectTaggedCode, split, bind] using projected⟩

theorem PackedRecord.Memory.openPayloadInScope_kernel {record : PackedRecord abi schema}
    {memory : record.Memory} {id : Nat} {path : List Nat} {payload : record.PayloadRef}
    (ran : memory.openPayloadInScope id path = some payload) :
    ∃ program, memory.readInScopeProgram id path = some program ∧
      RunsOnStorage memory.heap program memory.heap := by
  obtain ⟨_, accessed, opened⟩ := Option.bind_eq_some_iff.mp ran
  obtain ⟨⟨_, _, _⟩, tagged, _⟩ := Option.bind_eq_some_iff.mp opened
  obtain ⟨_, _, loaded, _, _⟩ := taggedCode_source tagged
  exact ⟨_, by simp [readInScopeProgram, accessed], PackedRecord.read_kernel loaded⟩

private theorem PackedRecord.Memory.readPayloadWithType_kernel {record : PackedRecord abi schema}
    {memory : record.Memory} {id data : Nat} {ty : PackedType} {payload : record.PayloadRef}
    (ran : memory.readPayloadWithType id payload = some (ty, data)) :
    ∃ program, memory.readInScopeProgram id payload.path = some program ∧
      RunsOnStorage memory.heap program memory.heap := by
  obtain ⟨_, _, accessed, _, _, loaded, _, _⟩ := readPayloadWithType_source ran
  exact ⟨_, by simp [readInScopeProgram, accessed], PackedRecord.read_kernel loaded⟩

theorem PackedRecord.Memory.readPayloadInScope_kernel {record : PackedRecord abi schema}
    {memory : record.Memory} {id code : Nat} {payload : record.PayloadRef}
    (ran : memory.readPayloadInScope id payload = some code) :
    ∃ program, memory.readInScopeProgram id payload.path = some program ∧
      RunsOnStorage memory.heap program memory.heap := by
  obtain ⟨⟨_, _⟩, loaded, _⟩ := Option.map_eq_some_iff.mp ran
  exact readPayloadWithType_kernel loaded

theorem PackedRecord.Memory.readPayloadFieldInScope_kernel {record : PackedRecord abi schema}
    {memory : record.Memory} {id code : Nat} {payload : record.PayloadRef}
    {steps : List PackedType.FieldStep}
    (read : memory.readPayloadFieldInScope id payload steps = some code) :
    ∃ program, memory.readInScopeProgram id payload.path = some program ∧
      RunsOnStorage memory.heap program memory.heap := by
  obtain ⟨⟨_, _⟩, loaded, _⟩ := Option.bind_eq_some_iff.mp read
  exact readPayloadWithType_kernel loaded

theorem PackedRecord.Memory.openPayload_coordinates {record : PackedRecord abi schema}
    {memory : record.Memory} {path : List Nat} {targets : List AccessTarget}
    {payload : record.PayloadRef} (opened : memory.openPayload path targets = some payload) :
    payload.path = path ∧ payload.generation = memory.generation path := by
  obtain ⟨⟨ty, tag, data⟩, _, equal⟩ := Option.bind_eq_some_iff.mp opened
  cases equal
  exact ⟨rfl, rfl⟩

theorem PackedRecord.Memory.openPayloadInScope_path {record : PackedRecord abi schema}
    {memory : record.Memory} {scope : Nat} {path : List Nat} {payload : record.PayloadRef}
    (opened : memory.openPayloadInScope scope path = some payload) : payload.path = path := by
  obtain ⟨_, _, captured⟩ := Option.bind_eq_some_iff.mp opened
  exact (openPayload_coordinates captured).1

theorem PackedRecord.Memory.write_invalidates_payload {record : PackedRecord abi schema}
    {memory next : record.Memory} {path : List Nat} {readTargets writeTargets : List AccessTarget}
    {payload : record.PayloadRef} {code : Nat}
    (opened : memory.openPayload path readTargets = some payload)
    (written : memory.write path writeTargets code = some next) :
    ∀ targets, next.readPayload payload targets = none := by
  obtain ⟨samePath, generation⟩ := openPayload_coordinates opened
  obtain ⟨heap, _, equal⟩ := Option.bind_eq_some_iff.mp written
  cases equal
  intro targets
  simp [readPayload, samePath, generation]

private theorem PackedRecord.Memory.writeInScope_invalidates_payloadWithType {record : PackedRecord abi schema}
    {memory next : record.Memory} {path : List Nat} {readScope writeScope : Nat}
    {payload : record.PayloadRef} {code : Nat}
    (opened : memory.openPayloadInScope readScope path = some payload)
    (written : memory.writeInScope writeScope path code = some next) :
    ∀ scope, next.readPayloadWithType scope payload = none := by
  obtain ⟨_, _, captured⟩ := Option.bind_eq_some_iff.mp opened
  obtain ⟨_, _, changed⟩ := Option.bind_eq_some_iff.mp written
  intro scope
  simp [readPayloadWithType, bind, write_invalidates_payload captured changed]

theorem PackedRecord.Memory.writeInScope_invalidates_payload {record : PackedRecord abi schema}
    {memory next : record.Memory} {path : List Nat} {readScope writeScope : Nat}
    {payload : record.PayloadRef} {code : Nat}
    (opened : memory.openPayloadInScope readScope path = some payload)
    (written : memory.writeInScope writeScope path code = some next) :
    ∀ scope, next.readPayloadInScope scope payload = none := by
  intro scope
  simp [readPayloadInScope, writeInScope_invalidates_payloadWithType opened written scope]

theorem PackedRecord.Memory.writeInScope_invalidates_payload_field {record : PackedRecord abi schema}
    {memory next : record.Memory} {path : List Nat} {readScope writeScope : Nat}
    {payload : record.PayloadRef} {code : Nat}
    (opened : memory.openPayloadInScope readScope path = some payload)
    (written : memory.writeInScope writeScope path code = some next) :
    ∀ scope steps, next.readPayloadFieldInScope scope payload steps = none := by
  intro scope steps
  simp [readPayloadFieldInScope, bind, writeInScope_invalidates_payloadWithType opened written scope]

/-- A sibling update retains a live capture and its projected value, even
when the two fields occupy some of the same bytes. -/
theorem PackedRecord.Memory.writeInScope_preserves_other_payload_field {record : PackedRecord abi schema}
    {memory next : record.Memory} {path : List Nat} {readScope writeScope : Nat}
    {payload : record.PayloadRef} {code data : Nat} {steps : List PackedType.FieldStep}
    {before : Image record.layout.size} (represented : before.InAllocation record.owner memory.heap)
    (read : memory.readPayloadFieldInScope readScope payload steps = some data)
    (written : memory.writeInScope writeScope path code = some next) (distinct : path ≠ payload.path) :
    next.readPayloadFieldInScope readScope payload steps = some data := by
  obtain ⟨⟨ty, saved⟩, loaded, projected⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨targets, whole, available, generation, declared, decoded, _, split⟩ := readPayloadWithType_source loaded
  obtain ⟨after, updated, finalImage⟩ := writeInScope_on_image represented written
  have prior : memory.readInScope readScope payload.path = some whole := by simp [readInScope, available, decoded, bind]
  have exactCode := (record.writeImage_frame updated distinct).trans (PackedRecord.read_on_image represented decoded)
  have current := readInScope_transfer (writeInScope_preserves_authority written) prior finalImage exactCode
  obtain ⟨targets, permitted, fetched⟩ := Option.bind_eq_some_iff.mp current
  have tagged := taggedCode_of_read declared fetched split
  have stillLive : payload.generation = next.generation payload.path := by
    rw [writeInScope_generation written, ite_eq_right (Ne.symm distinct), Nat.add_zero]
    exact generation
  have kept : next.readPayloadWithType readScope payload = some (ty, saved) := by
    simp [readPayloadWithType, readPayload, permitted, stillLive, tagged, bind]
  exact Option.bind_eq_some_iff.mpr ⟨_, kept, projected⟩

theorem PackedRecord.Memory.reborrow_suspends {record : PackedRecord abi schema}
    {memory next : record.Memory} {id parent : Nat} {path : List Nat} {mode : AccessMode}
    (borrowed : memory.reborrowScope parent path mode = some (id, next)) :
    next.heap = memory.heap ∧ ∀ other, next.readInScope parent other = none := by
  simp only [reborrowScope, bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
    at borrowed
  obtain ⟨_, _, child, _, _, rfl⟩ := borrowed
  exact ⟨rfl, fun _ => by simp [readInScope, scopeTargets, scope?, activeScope?, bind]⟩

end Aethel.AutomaticLayout
