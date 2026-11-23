import Aethel.IntegerLayout

namespace Aethel.AutomaticLayout

inductive StoragePolicy where
  | addressable
  | mayShareByte
  deriving Repr, DecidableEq

/-- Finite, inline integer records. Fields are keyed by declaration index. -/
inductive Schema where
  | integer (kind : IntegerType)
  | record (fields : List (StoragePolicy × Schema))
  deriving Repr

structure Placement where
  byteOffset : Nat
  bitOffset : Option Nat := none
  deriving Repr, DecidableEq

inductive Layout where
  | integer (kind : IntegerType) (slot : IntegerSlot)
  | record (size alignment : Nat) (fields : List (Placement × Layout))
  deriving Repr

def Layout.size : Layout → Nat
  | .integer _ slot => slot.size
  | .record size _ _ => size

def Layout.alignment : Layout → Nat
  | .integer _ slot => slot.alignment
  | .record _ alignment _ => alignment

def Layout.bits : Layout → Nat
  | .integer kind _ => kind.bits
  | .record .. => 0

abbrev Field := Placement × Layout

def Field.bytes (field : Field) : Nat :=
  if field.1.bitOffset.isSome then 1 else field.2.size

def Field.Valid (total alignment : Nat) (policy : StoragePolicy) (field : Field) : Prop :=
  field.1.byteOffset + field.bytes ≤ total ∧
    match field.1.bitOffset with
    | none =>
      0 < field.2.alignment ∧ field.1.byteOffset % field.2.alignment = 0 ∧
        alignment % field.2.alignment = 0
    | some bit =>
      policy = .mayShareByte ∧ 0 < field.2.bits ∧ field.2.bits < 8 ∧ bit + field.2.bits ≤ 8

instance Field.instDecidableValid (total alignment : Nat) (policy : StoragePolicy) (field : Field) :
    Decidable (field.Valid total alignment policy) := by
  unfold Field.Valid
  split <;> infer_instance

def Field.Separate (a b : Field) : Prop :=
  a.bytes = 0 ∨ b.bytes = 0 ∨
  a.1.byteOffset + a.bytes ≤ b.1.byteOffset ∨ b.1.byteOffset + b.bytes ≤ a.1.byteOffset ∨
  (a.1.byteOffset = b.1.byteOffset ∧
    match a.1.bitOffset, b.1.bitOffset with
    | some x, some y => x + a.2.bits ≤ y ∨ y + b.2.bits ≤ x
    | _, _ => False)

instance Field.instDecidableSeparate (a b : Field) : Decidable (a.Separate b) := by
  unfold Field.Separate
  split <;> infer_instance

/-- A successful plan must match each source field in declaration order.
Spans are disjoint except for disjoint bit ranges explicitly sharing one byte. -/
inductive Conforms (abi : TargetIntegerABI) : Schema → Layout → Prop where
  | integer (valid : (abi.slot kind).Valid kind) :
      Conforms abi (.integer kind) (.integer kind (abi.slot kind))
  | record (aligned : alignment.isPowerOfTwo) (stride : size % alignment = 0)
      (count : fields.length = placed.length) (separate : placed.Pairwise Field.Separate)
      (placements : ∀ pair ∈ fields.zip placed, Field.Valid size alignment pair.1.1 pair.2)
      (children : ∀ pair ∈ fields.zip placed, Conforms abi pair.1.2 pair.2.2) :
      Conforms abi (.record fields) (.record size alignment placed)

def validate (abi : TargetIntegerABI) : Nat → Schema → Layout → Bool
  | 0, _, _ => false
  | _ + 1, .integer kind, .integer actual slot =>
    decide (kind = actual ∧ slot = abi.slot kind ∧ slot.Valid kind)
  | depth + 1, .record fields, .record size alignment placed =>
    decide (alignment.isPowerOfTwo ∧ size % alignment = 0 ∧
      fields.length = placed.length ∧ placed.Pairwise Field.Separate) &&
      (fields.zip placed).all (fun (source, field) =>
        decide (Field.Valid size alignment source.1 field) && validate abi depth source.2 field.2)
  | _ + 1, _, _ => false

theorem validate_sound (abi : TargetIntegerABI) (depth : Nat) (schema : Schema) (layout : Layout)
    (checked : validate abi depth schema layout = true) : Conforms abi schema layout := by
  induction depth generalizing schema layout with
  | zero => simp [validate] at checked
  | succ depth ih =>
    cases schema <;> cases layout <;> simp only [validate, Bool.false_eq_true] at checked
    case integer.integer kind actual slot =>
      obtain ⟨rfl, rfl, valid⟩ := of_decide_eq_true checked
      exact .integer valid
    case record.record fields size alignment placed =>
      obtain ⟨geometry, each⟩ := Bool.and_eq_true_iff.mp checked
      obtain ⟨aligned, stride, count, separate⟩ := of_decide_eq_true geometry
      exact .record aligned stride count separate
        (fun pair member =>
          of_decide_eq_true (Bool.and_eq_true_iff.mp (List.all_eq_true.mp each pair member)).1)
        (fun pair member => ih _ _ (Bool.and_eq_true_iff.mp (List.all_eq_true.mp each pair member)).2)

private abbrev IndexedField := (StoragePolicy × Layout) × Nat

private def canPack (entry : IndexedField) : Bool :=
  entry.1.1 == .mayShareByte && decide (0 < entry.1.2.bits ∧ entry.1.2.bits < 8)

private def placeAddressable (state : Nat × List (Nat × Field))
    (entry : IndexedField) : Nat × List (Nat × Field) :=
  let layout := entry.1.2
  let offset := alignUp state.1 layout.alignment
  (offset + layout.size, (entry.2, ⟨offset, none⟩, layout) :: state.2)

private def allocPackedBit (bitsNeeded idx : Nat) : List Nat → Nat × Nat × List Nat
  | [] => (idx, 0, [bitsNeeded])
  | used :: rest =>
    if used + bitsNeeded ≤ 8 then
      (idx, used, (used + bitsNeeded) :: rest)
    else
      let (resIdx, resBit, nextRest) := allocPackedBit bitsNeeded (idx + 1) rest
      (resIdx, resBit, used :: nextRest)

private def placePacked (base : Nat) (state : List Nat × List (Nat × Field))
    (entry : IndexedField) : List Nat × List (Nat × Field) :=
  let layout := entry.1.2
  let (byteIdx, bitOff, nextBins) := allocPackedBit layout.bits 0 state.1
  (nextBins, (entry.2, ⟨base + byteIdx, some bitOff⟩, layout) :: state.2)

/-- Compare actual aligned sizes, with declaration order winning a tie. -/
def choose (declaration compact : Layout) : Layout :=
  if compact.size < declaration.size then compact else declaration

theorem choose_no_larger (declaration compact : Layout) :
    (choose declaration compact).size ≤ declaration.size := by
  unfold choose
  split <;> omega

private def assemble (indexed : List IndexedField) (entries : List (Nat × Field))
    (size alignment : Nat) : Option Layout := do
  let fields ← indexed.mapM fun entry =>
    (entries.find? fun placed => placed.1 == entry.2).map Prod.snd
  return .record size alignment fields

private def recordCandidate (fields : List (StoragePolicy × Layout)) (compact : Bool) : Option Layout :=
  let indexed := fields.zipIdx
  let alignment := fields.foldl (fun n field => max n field.2.alignment) 1
  let (packed, ordinary) := if compact then indexed.partition canPack else ([], indexed)
  let ordered := if compact then ordinary.mergeSort (fun a b => a.1.2.alignment ≥ b.1.2.alignment)
    else ordinary
  let (base, addressable) := ordered.foldl placeAddressable (0, [])
  let packed := packed.mergeSort (fun a b => a.1.2.bits ≥ b.1.2.bits)
  let (bins, shared) := packed.foldl (placePacked base) ([], [])
  assemble indexed (addressable ++ shared) (alignUp (base + bins.length) alignment) alignment

private def compute (abi : TargetIntegerABI) : Nat → Schema → Option Layout
  | 0, _ => none
  | _ + 1, .integer kind => some (.integer kind (abi.slot kind))
  | depth + 1, .record fields => do
    let children ← fields.mapM fun (policy, child) =>
      (compute abi depth child).map fun layout => (policy, layout)
    let declaration ← recordCandidate children false
    let compact ← recordCandidate children true
    return choose declaration compact

def Schema.depth : Schema → Nat
  | .integer _ => 1
  | .record fields =>
    fields.attach.foldl (fun largest field => max largest (depth field.val.2)) 0 + 1
termination_by schema => sizeOf schema
decreasing_by
  have smaller := List.sizeOf_lt_of_mem field.property
  have childSmaller : sizeOf field.val.2 < sizeOf field.val := by
    cases field.val
    simp
    omega
  simp_wf
  omega

def plan (abi : TargetIntegerABI) (schema : Schema) : Option Layout := do
  let depth := schema.depth
  let layout ← compute abi depth schema
  if validate abi depth schema layout then some layout else none

theorem plan_sound {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : plan abi schema = some layout) : Conforms abi schema layout := by
  simp only [plan, bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq] at planned
  obtain ⟨_, _, verified, rfl⟩ := planned
  exact validate_sound _ _ _ _ verified

/-- Locate a nested field using declaration indices. Byte offsets accumulate
from the outer root. A packed scalar reports its bit offset in that byte. -/
def resolve (layout : Layout) (path : List Nat) : Option Field :=
  match path, layout with
  | [], _ => some (⟨0, none⟩, layout)
  | index :: rest, .record _ _ fields => do
    let (placement, child) ← fields[index]?
    match rest with
    | [] => some (placement, child)
    | _ :: _ => do
      let (inner, leaf) ← resolve child rest
      return (⟨placement.byteOffset + inner.byteOffset, inner.bitOffset⟩, leaf)
  | _ :: _, .integer .. => none

def Schema.resolve (schema : Schema) (path : List Nat) : Option Schema :=
  match path, schema with
  | [], _ => some schema
  | index :: rest, .record fields => fields[index]?.bind fun field => field.2.resolve rest
  | _ :: _, .integer _ => none

theorem Conforms.field {abi : TargetIntegerABI} {fields : List (StoragePolicy × Schema)}
    {size alignment : Nat} {placed : List Field} {index : Nat} {field : Field}
    (record : Conforms abi (.record fields) (.record size alignment placed))
    (found : placed[index]? = some field) :
    ∃ policy child, fields[index]? = some (policy, child) ∧
      Field.Valid size alignment policy field ∧ Conforms abi child field.2 := by
  cases record with
  | record _ _ count _ placements children =>
    obtain ⟨placedIndex, atIndex⟩ := List.getElem?_eq_some_iff.mp found
    have sourceIndex : index < fields.length := count.symm ▸ placedIndex
    have zipIndex : index < (fields.zip placed).length := by
      simp only [List.length_zip, Nat.lt_min]
      exact ⟨sourceIndex, placedIndex⟩
    have member : (fields[index], field) ∈ fields.zip placed :=
      List.mem_of_getElem (h := zipIndex) (by rw [List.getElem_zip, atIndex])
    exact ⟨_, _, List.getElem?_eq_getElem sourceIndex, placements _ member, children _ member⟩

theorem Conforms.alignment_pos {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) : 0 < layout.alignment := by
  have power : layout.alignment.isPowerOfTwo := by
    cases planned with
    | integer slot => exact slot.2.1
    | record aligned _ _ _ _ _ => exact aligned
  obtain ⟨exponent, h⟩ := power
  rw [h]
  exact Nat.two_pow_pos exponent

private theorem Field.Valid.allowPacking {total align : Nat} {policy : StoragePolicy} {field : Field}
    (valid : Field.Valid total align policy field) : Field.Valid total align .mayShareByte field := by
  cases h : field.1.bitOffset <;> simp_all [Field.Valid]

private theorem Field.Valid.rebase {total align : Nat} {outer inner : Field}
    (outside : Field.Valid total align .mayShareByte outer) (addressable : outer.1.bitOffset = none)
    (inside : Field.Valid outer.2.size outer.2.alignment .mayShareByte inner) :
    Field.Valid total align .mayShareByte
      (⟨outer.1.byteOffset + inner.1.byteOffset, inner.1.bitOffset⟩, inner.2) := by
  have bounds := outside.1
  simp only [Field.bytes, addressable, Option.isSome_none, Bool.false_eq_true, ite_false] at bounds
  have aligned := outside.2
  rw [addressable] at aligned
  refine ⟨by change outer.1.byteOffset + inner.1.byteOffset + inner.bytes ≤ total; have := inside.1; omega, ?_⟩
  cases h : inner.1.bitOffset with
  | some bit => simpa only [h] using inside.2
  | none =>
    have proper := inside.2
    rw [h] at proper
    have outerOffset : inner.2.alignment ∣ outer.1.byteOffset :=
      Nat.dvd_trans (Nat.dvd_of_mod_eq_zero proper.2.2) (Nat.dvd_of_mod_eq_zero aligned.2.1)
    have base : inner.2.alignment ∣ align :=
      Nat.dvd_trans (Nat.dvd_of_mod_eq_zero proper.2.2) (Nat.dvd_of_mod_eq_zero aligned.2.2)
    exact ⟨proper.1, Nat.mod_eq_zero_of_dvd (Nat.dvd_add outerOffset
      (Nat.dvd_of_mod_eq_zero proper.2.1)), Nat.mod_eq_zero_of_dvd base⟩

/-- Resolving a nested path preserves the declared type, stays inside the
outer record, and inherits alignment from the root for addressable fields. -/
theorem resolve_sound {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {path : List Nat} {field : Field} (planned : Conforms abi schema layout)
    (found : resolve layout path = some field) :
    ∃ child, schema.resolve path = some child ∧ Conforms abi child field.2 ∧
      Field.Valid layout.size layout.alignment .mayShareByte field := by
  induction path generalizing schema layout field with
  | nil =>
    cases found
    exact ⟨schema, rfl, planned, by simp [Field.bytes], planned.alignment_pos,
      Nat.zero_mod _, Nat.mod_self _⟩
  | cons index rest ih =>
    cases planned with
    | integer valid => simp [resolve] at found
    | record aligned stride count separate placements children =>
      rename_i fields placed
      cases atIndex : placed[index]? with
      | none => simp [resolve, atIndex, bind] at found
      | some outer =>
        obtain ⟨policy, child, source, fieldValid, childValid⟩ :=
          (Conforms.record aligned stride count separate placements children).field atIndex
        cases rest with
        | nil =>
          simp [resolve, atIndex, bind] at found
          exact ⟨child, by simp [Schema.resolve, source], found ▸ childValid,
            found ▸ fieldValid.allowPacking⟩
        | cons next rest =>
          simp only [resolve, atIndex, bind, pure, Option.bind_eq_some_iff, Prod.exists,
            Option.some.injEq] at found
          obtain ⟨location, localLayout, rfl, inner, leaf, resolved, rfl⟩ := found
          obtain ⟨target, targetAt, targetValid, innerValid⟩ := ih childValid resolved
          have addressable : location.bitOffset = none := by
            cases h : location.bitOffset with
            | none => rfl
            | some bit =>
              cases localLayout with
              | integer kind slot => simp [resolve] at resolved
              | record size align fields => simp [Field.Valid, h, Layout.bits] at fieldValid
          exact ⟨target, by simp [Schema.resolve, source, targetAt], targetValid,
            fieldValid.allowPacking.rebase addressable innerValid⟩

/-- Packed scalar accesses use their containing byte. Addressable fields
use the alignment of the resolved logical field. -/
def Field.accessAlignment (field : Field) : Nat :=
  if field.1.bitOffset.isSome then 1 else field.2.alignment

theorem resolved_access {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {path : List Nat} {field : Field} {base addressLimit : Nat}
    (planned : Conforms abi schema layout) (found : resolve layout path = some field)
    (nonempty : 0 < field.bytes) (baseAligned : base % layout.alignment = 0)
    (capacity : base + layout.size ≤ addressLimit) :
    checkAccess layout.size base field.1.byteOffset field.bytes field.accessAlignment addressLimit =
      true := by
  obtain ⟨_, _, _, valid⟩ := resolve_sound planned found
  cases h : field.1.bitOffset with
  | some bit =>
    exact decide_eq_true ⟨nonempty, by simp [Field.accessAlignment, h], valid.1, capacity,
      by simp [Field.accessAlignment, h, Nat.mod_one]⟩
  | none =>
    have aligned := valid.2
    rw [h] at aligned
    have baseMultiple : field.2.alignment ∣ base :=
      Nat.dvd_trans (Nat.dvd_of_mod_eq_zero aligned.2.2) (Nat.dvd_of_mod_eq_zero baseAligned)
    have addressAligned := Nat.mod_eq_zero_of_dvd
      (Nat.dvd_add baseMultiple (Nat.dvd_of_mod_eq_zero aligned.2.1))
    have useAlignment : field.accessAlignment = field.2.alignment := by
      simp [Field.accessAlignment, h]
    rw [useAlignment]
    exact decide_eq_true ⟨nonempty, aligned.1, valid.1, capacity, addressAligned⟩

end Aethel.AutomaticLayout
