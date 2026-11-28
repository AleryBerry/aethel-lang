import Aethel.IntegerLayout

namespace Aethel.AutomaticLayout

inductive StoragePolicy where
  | addressable
  | mayShareByte
  deriving Repr, DecidableEq

/-- Finite inline records. A fixed field stores an encoding of known width,
with its target slot supplied separately. Fields are keyed by declaration index. -/
inductive Schema where
  | integer (kind : IntegerType)
  | fixed (width : Nat) (slot : IntegerSlot)
  | record (fields : List (StoragePolicy × Schema))
  deriving Repr

structure Placement where
  byteOffset : Nat
  bitOffset : Option Nat := none
  deriving Repr, DecidableEq

def Placement.bitStart (placement : Placement) : Nat :=
  placement.byteOffset * 8 + placement.bitOffset.getD 0

/-- A relative placement inherits bit addressing from any packed ancestor. -/
def Placement.rebase (outer inner : Placement) : Placement :=
  match outer.bitOffset with
  | none => ⟨outer.byteOffset + inner.byteOffset, inner.bitOffset⟩
  | some _ =>
    let start := outer.bitStart + inner.bitStart
    ⟨start / 8, some (start % 8)⟩

theorem Placement.bitStart_rebase (outer inner : Placement) :
    (outer.rebase inner).bitStart = outer.bitStart + inner.bitStart := by
  cases loc : outer.bitOffset <;> simp [Placement.rebase, Placement.bitStart, loc] <;> omega

inductive Layout where
  | integer (kind : IntegerType) (slot : IntegerSlot)
  | fixed (width : Nat) (slot : IntegerSlot)
  | record (size alignment : Nat) (fields : List (Placement × Layout))
  deriving Repr

def Layout.size : Layout → Nat
  | .integer _ slot => slot.size
  | .fixed _ slot => slot.size
  | .record size _ _ => size

def Layout.alignment : Layout → Nat
  | .integer _ slot => slot.alignment
  | .fixed _ slot => slot.alignment
  | .record _ alignment _ => alignment

def Layout.embeddable : Layout → Bool
  | .record _ _ fields => fields.all (fun field => field.1.bitOffset.isSome)
  | _ => true

def Layout.bits : Layout → Nat
  | .integer kind _ => kind.bits
  | .fixed width _ => width
  | .record _ _ fields =>
    if fields.all (fun field => field.1.bitOffset.isSome) then
      ((fields.attach.map fun field => field.val.1.bitStart + bits field.val.2).max?).getD 0
    else 0
termination_by layout => sizeOf layout
decreasing_by
  have smaller := List.sizeOf_lt_of_mem field.property
  have childSmaller : sizeOf field.val.2 < sizeOf field.val := by
    cases field.val
    simp
    omega
  simp_wf
  omega

abbrev Field := Placement × Layout

theorem Layout.packedChild {size alignment : Nat} {fields : List Field} {field : Field}
    (packed : (Layout.record size alignment fields).embeddable = true) (member : field ∈ fields) :
    field.1.bitOffset.isSome = true ∧
      field.1.bitStart + field.2.bits ≤ (Layout.record size alignment fields).bits := by
  change fields.all _ = true at packed
  rw [Layout.bits, ite_eq_left packed]
  exact ⟨List.all_eq_true.mp packed field member,
    List.le_max?_getD_of_mem (List.mem_map.mpr ⟨⟨field, member⟩, List.mem_attach _ _, rfl⟩)⟩

def Field.bytes (field : Field) : Nat :=
  if field.1.bitOffset.isSome then
    if field.2.bits = 0 then 0 else (field.1.bitOffset.getD 0 + field.2.bits + 7) / 8
  else field.2.size

/-- Packed scalar accesses use their containing byte. Addressable fields
use the alignment of the resolved logical field. -/
def Field.accessAlignment (field : Field) : Nat :=
  if field.1.bitOffset.isSome then 1 else field.2.alignment

def Field.bitExtent (field : Field) : Nat :=
  if field.1.bitOffset.isSome then field.2.bits else field.2.size * 8

theorem Field.bitExtent_fits (field : Field) (positive : 0 < field.bitExtent) :
    field.1.bitStart + field.bitExtent ≤ (field.1.byteOffset + field.bytes) * 8 := by
  cases atBit : field.1.bitOffset with
  | none => simp [Field.bitExtent, Field.bytes, Placement.bitStart, atBit]; omega
  | some bit =>
    have nonzero : field.2.bits ≠ 0 := by
      simp [Field.bitExtent, atBit] at positive
      omega
    simp [Field.bitExtent, Field.bytes, Placement.bitStart, atBit, nonzero]
    omega

def Field.Valid (total alignment : Nat) (policy : StoragePolicy) (field : Field) : Prop :=
  field.1.byteOffset + field.bytes ≤ total ∧
    match field.1.bitOffset with
    | none =>
      0 < field.2.alignment ∧ field.1.byteOffset % field.2.alignment = 0 ∧
        alignment % field.2.alignment = 0
    | some bit =>
      policy = .mayShareByte ∧ field.2.embeddable = true ∧ bit < 8 ∧
        field.1.bitStart + field.2.bits ≤ total * 8

instance Field.instDecidableValid (total alignment : Nat) (policy : StoragePolicy) (field : Field) :
    Decidable (field.Valid total alignment policy) := by
  unfold Field.Valid
  split <;> infer_instance

theorem Field.Valid.accessAlignment_dvd {total align : Nat} {policy : StoragePolicy} {field : Field}
    (valid : Field.Valid total align policy field) :
    0 < field.accessAlignment ∧ field.1.byteOffset % field.accessAlignment = 0 ∧ align % field.accessAlignment = 0 := by
  cases place : field.1.bitOffset with
  | none =>
    have geometry := valid.2
    rw [place] at geometry
    simpa [Field.accessAlignment, place] using geometry
  | some bit =>
    simp [Field.accessAlignment, place, Nat.mod_one]

theorem Field.Valid.bitExtent_within {total align : Nat} {policy : StoragePolicy} {field : Field}
    (valid : Field.Valid total align policy field) :
    field.1.bitStart + field.bitExtent ≤ total * 8 := by
  cases place : field.1.bitOffset with
  | none =>
    have bounded := valid.1
    simp [Field.bytes, place] at bounded
    simp [Field.bitExtent, Placement.bitStart, place]
    omega
  | some bit =>
    have geometry := valid.2
    rw [place] at geometry
    simpa [Field.bitExtent, place] using geometry.2.2.2

def Field.Separate (a b : Field) : Prop :=
  a.bytes = 0 ∨ b.bytes = 0 ∨
  a.1.byteOffset + a.bytes ≤ b.1.byteOffset ∨ b.1.byteOffset + b.bytes ≤ a.1.byteOffset ∨
  (match a.1.bitOffset, b.1.bitOffset with
    | some _, some _ =>
      a.1.bitStart + a.2.bits ≤ b.1.bitStart ∨ b.1.bitStart + b.2.bits ≤ a.1.bitStart
    | _, _ => False)

instance Field.instDecidableSeparate (a b : Field) : Decidable (a.Separate b) := by
  unfold Field.Separate
  split <;> infer_instance

/-- Absolute bit positions occupied by a field. Empty fields have no positions. -/
def Field.bitPositions (field : Field) : List Nat :=
  (List.range field.bitExtent).map (field.1.bitStart + ·)

theorem Field.mem_bitPositions {field : Field} {position : Nat} :
    position ∈ field.bitPositions ↔
      ∃ offset < field.bitExtent, position = field.1.bitStart + offset := by
  simp [Field.bitPositions, List.mem_range, eq_comm]

theorem Field.bitPositions_nodup (field : Field) : field.bitPositions.Nodup := by
  rw [List.nodup_iff_pairwise_ne, Field.bitPositions, List.pairwise_map]
  exact List.nodup_range.imp (fun different => by omega)

theorem Field.bitExtent_eq_zero_of_bytes_eq_zero {field : Field} (empty : field.bytes = 0) :
    field.bitExtent = 0 := by
  cases place : field.1.bitOffset <;>
    simp [Field.bytes, Field.bitExtent, place] at empty ⊢ <;> omega

theorem Field.Separate.bitPositions_disjoint {a b : Field} (separate : a.Separate b)
    {x y : Nat} (inA : x ∈ a.bitPositions) (inB : y ∈ b.bitPositions) : x ≠ y := by
  obtain ⟨i, withinA, rfl⟩ := a.mem_bitPositions.mp inA
  obtain ⟨j, withinB, rfl⟩ := b.mem_bitPositions.mp inB
  rcases separate with empty | empty | before | after | packed
  · have := a.bitExtent_eq_zero_of_bytes_eq_zero empty
    omega
  · have := b.bitExtent_eq_zero_of_bytes_eq_zero empty
    omega
  · have endA := a.bitExtent_fits (by omega)
    have startB : b.1.byteOffset * 8 ≤ b.1.bitStart := by
      simp [Placement.bitStart]
    have multiplied := Nat.mul_le_mul_right 8 before
    omega
  · have endB := b.bitExtent_fits (by omega)
    have startA : a.1.byteOffset * 8 ≤ a.1.bitStart := by
      simp [Placement.bitStart]
    have multiplied := Nat.mul_le_mul_right 8 after
    omega
  · cases placeA : a.1.bitOffset <;> cases placeB : b.1.bitOffset <;>
      simp [placeA, placeB] at packed
    simp [Field.bitExtent, placeA, placeB] at withinA withinB
    rcases packed with before | after <;> omega

theorem Field.bitPositions_pairwise {fields : List Field} (separate : fields.Pairwise Field.Separate) :
    (fields.flatMap Field.bitPositions).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_flatMap]
  exact ⟨fun field _ => List.nodup_iff_pairwise_ne.mp field.bitPositions_nodup,
    List.Pairwise.imp (R := Field.Separate)
      (fun {a b} (disjoint : a.Separate b) => by
        intro x inA y inB
        exact disjoint.bitPositions_disjoint inA inB) separate⟩

def FixedSlotValid (width : Nat) (slot : IntegerSlot) : Prop :=
  width ≤ slot.size * 8 ∧ slot.alignment.isPowerOfTwo ∧ slot.size % slot.alignment = 0 ∧
    (width = 0 → slot = ⟨0, 1⟩)

instance (width : Nat) (slot : IntegerSlot) : Decidable (FixedSlotValid width slot) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A successful plan must match each source field in declaration order.
Addressable slots have separate byte spans. Packed fields may share bytes
when their logical bit intervals are disjoint. -/
inductive Conforms (abi : TargetIntegerABI) : Schema → Layout → Prop where
  | integer (valid : (abi.slot kind).Valid kind) :
      Conforms abi (.integer kind) (.integer kind (abi.slot kind))
  | fixed (valid : FixedSlotValid width slot) :
      Conforms abi (.fixed width slot) (.fixed width slot)
  | record (aligned : alignment.isPowerOfTwo) (stride : size % alignment = 0)
      (count : fields.length = placed.length) (separate : placed.Pairwise Field.Separate)
      (placements : ∀ pair ∈ fields.zip placed, Field.Valid size alignment pair.1.1 pair.2)
      (children : ∀ pair ∈ fields.zip placed, Conforms abi pair.1.2 pair.2.2) :
      Conforms abi (.record fields) (.record size alignment placed)

/-- Field extents consume distinct positions in the enclosing record. This is
independent of the planner and also bounds layouts supplied by certificates. -/
theorem Conforms.bitVolume_le {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) :
    match layout with
    | .record size _ placed => (placed.map Field.bitExtent).sum ≤ size * 8
    | _ => True := by
  cases planned with
  | integer _ => trivial
  | fixed _ => trivial
  | @record recordSize recordAlignment fields placed aligned stride count separate placements children =>
    have positionsNodup := Field.bitPositions_pairwise separate
    have subset : placed.flatMap Field.bitPositions ⊆ List.range (recordSize * 8) := by
      intro position member
      obtain ⟨field, fieldMember, positionMember⟩ := List.mem_flatMap.mp member
      obtain ⟨index, bounded, located⟩ := List.mem_iff_getElem.mp fieldMember
      have sourceBounded : index < fields.length := by omega
      have zippedBounded : index < (fields.zip placed).length := by
        simpa using Nat.lt_min.mpr ⟨sourceBounded, bounded⟩
      have pairMember : (fields.zip placed)[index] ∈ fields.zip placed :=
        List.getElem_mem zippedBounded
      have valid := placements _ pairMember
      rw [List.getElem_zip, located] at valid
      obtain ⟨offset, within, rfl⟩ := field.mem_bitPositions.mp positionMember
      rw [List.mem_range]
      have fits : field.1.bitStart + field.bitExtent ≤ recordSize * 8 :=
        valid.bitExtent_within
      omega
    have lengthBound := positionsNodup.length_le_of_subset subset
    simpa [Field.bitPositions, List.length_flatMap] using lengthBound

theorem alignUp_le_of_le_of_mod {offset aligned alignment : Nat} (positive : 0 < alignment)
    (within : offset ≤ aligned) (stride : aligned % alignment = 0) :
    alignUp offset alignment ≤ aligned := by
  by_cases equal : offset = aligned
  · subst aligned
    simp [alignUp, padding, stride]
  · have paddingBound := padding_minimal offset (aligned - offset) positive (by
      rw [Nat.add_sub_of_le within]
      exact stride)
    unfold alignUp
    omega

/-- The byte-volume lower bound inherits the record's alignment constraint. -/
theorem Conforms.roundedBitVolume_le {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) :
    match layout with
    | .record size alignment placed =>
      alignUp (((placed.map Field.bitExtent).sum + 7) / 8) alignment ≤ size
    | _ => True := by
  cases planned with
  | integer _ | fixed _ => trivial
  | @record recordSize recordAlignment fields placed aligned stride count separate placements children =>
    have positiveAlignment : 0 < recordAlignment := by
      obtain ⟨power, equality⟩ := aligned
      rw [equality]
      exact Nat.two_pow_pos power
    have volume := Conforms.bitVolume_le (Conforms.record aligned stride count separate placements children)
    change (placed.map Field.bitExtent).sum ≤ recordSize * 8 at volume
    have bytesLe : ((placed.map Field.bitExtent).sum + 7) / 8 ≤ recordSize :=
      (Nat.div_le_iff_le_mul (by decide : 0 < 8)).mpr (by omega)
    exact alignUp_le_of_le_of_mod positiveAlignment bytesLe stride

def validate (abi : TargetIntegerABI) : Nat → Schema → Layout → Bool
  | 0, _, _ => false
  | _ + 1, .integer kind, .integer actual slot =>
    decide (kind = actual ∧ slot = abi.slot kind ∧ slot.Valid kind)
  | _ + 1, .fixed width target, .fixed actual slot =>
    decide (width = actual ∧ slot = target ∧ FixedSlotValid width slot)
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
    case fixed.fixed width target actual slot =>
      obtain ⟨rfl, rfl, valid⟩ := of_decide_eq_true checked
      exact .fixed valid
    case record.record fields size alignment placed =>
      obtain ⟨geometry, each⟩ := Bool.and_eq_true_iff.mp checked
      obtain ⟨aligned, stride, count, separate⟩ := of_decide_eq_true geometry
      exact .record aligned stride count separate
        (fun pair member =>
          of_decide_eq_true (Bool.and_eq_true_iff.mp (List.all_eq_true.mp each pair member)).1)
        (fun pair member => ih _ _ (Bool.and_eq_true_iff.mp (List.all_eq_true.mp each pair member)).2)

private abbrev IndexedField := (StoragePolicy × Layout) × Nat

def Schema.defaultPackable : Schema → Bool
  | .integer kind => kind.bits % 8 != 0
  | .fixed width _ => 0 < width && width % 8 != 0
  | .record _ => false

/-- Default x86-64 L1 data cache capacity (32 KiB) for `@layout(auto)` packing decisions. -/
def l1DataCacheBytes : Nat := 32768

def shouldUnpackHotInL1 (isHot : Bool) (workingSetBytes : Option Nat) : Bool :=
  match workingSetBytes with
  | some ws => isHot && decide (ws ≤ l1DataCacheBytes)
  | none => false

private def placeAddressable (state : Nat × List (Nat × Field))
    (entry : IndexedField) : Nat × List (Nat × Field) :=
  let layout := entry.1.2
  let offset := alignUp state.1 layout.alignment
  (offset + layout.size, (entry.2, ⟨offset, none⟩, layout) :: state.2)

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

private def declarationCandidate (fields : List (StoragePolicy × Layout)) : Option Layout :=
  let indexed := fields.zipIdx
  let alignment := fields.foldl (fun n field => max n field.2.alignment) 1
  let (endByte, addressable) := indexed.foldl placeAddressable (0, [])
  assemble indexed addressable (alignUp endByte alignment) alignment

private def placeBitInterval (state : Nat × List (Nat × Field))
    (entry : IndexedField) : Nat × List (Nat × Field) :=
  let start := state.1
  let layout := entry.1.2
  (start + layout.bits, (entry.2, ⟨start / 8, some (start % 8)⟩, layout) :: state.2)

private def compactCandidate (fields : List (StoragePolicy × Layout × Layout)) : Option Layout := do
  let indexed := (fields.map fun (policy, ordinary, embedded) =>
    if policy == .mayShareByte && embedded.embeddable then (.mayShareByte, embedded)
    else (.addressable, ordinary)).zipIdx
  let (packed, ordinary) := indexed.partition (fun entry => entry.1.1 == .mayShareByte)
  let alignment := ordinary.foldl (fun n entry => max n entry.1.2.alignment) 1
  let ordered := ordinary.mergeSort (fun a b => a.1.2.alignment ≥ b.1.2.alignment)
  let (base, slots) := ordered.foldl placeAddressable (0, [])
  let packed := packed.mergeSort (fun a b => a.1.2.bits ≥ b.1.2.bits)
  let (endBit, intervals) := packed.foldl placeBitInterval (base * 8, [])
  assemble indexed (slots ++ intervals) (alignUp ((endBit + 7) / 8) alignment) alignment

/-- Compute the best standalone layout and the layout available to a packed
parent. A standalone size tie can still save padding when embedded. -/
private def compute (abi : TargetIntegerABI) :
    Nat → List (List Nat) → Schema → Option (Layout × Layout)
  | 0, _, _ => none
  | _ + 1, _, .integer kind =>
    let layout := Layout.integer kind (abi.slot kind)
    some (layout, layout)
  | _ + 1, _, .fixed width slot =>
    let layout := Layout.fixed width slot
    some (layout, layout)
  | depth + 1, flatRecords, .record fields => do
    let flat := flatRecords.contains []
    let children ← fields.zipIdx.mapM fun ((policy, child), index) => do
      let below := flatRecords.filterMap fun
        | head :: rest => if head = index then some rest else none
        | [] => none
      let childLayout ← compute abi depth (if flat then [[]] else below) child
      let childPolicy := if flat || below.contains [] then .addressable else policy
      return (childPolicy, childLayout)
    let standalone := children.map fun (policy, layout, _) => (policy, layout)
    let declaration ← declarationCandidate standalone
    if flat then return (declaration, declaration)
    let compact ← compactCandidate children
    return (choose declaration compact, compact)

def Schema.depth : Schema → Nat
  | .integer _ => 1
  | .fixed .. => 1
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

def Schema.integerOnly : Schema → Bool
  | .integer _ => true
  | .fixed .. => false
  | .record fields => fields.attach.all fun field => integerOnly field.val.2
termination_by schema => sizeOf schema
decreasing_by
  have smaller := List.sizeOf_lt_of_mem field.property
  have childSmaller : sizeOf field.val.2 < sizeOf field.val := by
    cases field.val
    simp
    omega
  simp_wf
  omega

private def checkedPlan (abi : TargetIntegerABI) (schema : Schema)
    (flatRecords : List (List Nat) := []) : Option Layout := do
  let depth := schema.depth
  let (layout, _) ← compute abi depth flatRecords schema
  if validate abi depth schema layout then some layout else none

def plan (abi : TargetIntegerABI) (schema : Schema) : Option Layout :=
  checkedPlan abi schema

private theorem checkedPlan_sound {abi : TargetIntegerABI} {schema : Schema}
    {flatRecords : List (List Nat)} {layout : Layout}
    (planned : checkedPlan abi schema flatRecords = some layout) :
    Conforms abi schema layout := by
  simp only [checkedPlan, bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some,
    Option.some.injEq, Prod.exists] at planned
  obtain ⟨_, _, _, verified, rfl⟩ := planned
  exact validate_sound _ _ _ _ verified

theorem plan_sound {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : plan abi schema = some layout) : Conforms abi schema layout :=
  checkedPlan_sound planned

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
      return (placement.rebase inner, leaf)
  | _ :: _, _ => none

/-- The next field in declaration order starts at the first aligned byte
after its predecessor, and its whole slot contributes to the next offset. -/
inductive DeclarationSlots : Nat → List Field → Nat → Prop where
  | nil : DeclarationSlots cursor [] cursor
  | cons (rest : DeclarationSlots (alignUp cursor child.alignment + child.size) children ending) :
      DeclarationSlots cursor ((⟨alignUp cursor child.alignment, none⟩, child) :: children) ending

inductive Layout.FlatTree : Layout → Prop where
  | integer : FlatTree (.integer kind slot)
  | fixed : FlatTree (.fixed width slot)
  | record {extent align : Nat} (ordered : DeclarationSlots 0 fields ending)
      (alignment : align = fields.foldl (fun a f => max a f.2.alignment) 1)
      (stride : extent = alignUp ending align) (children : ∀ f ∈ fields, FlatTree f.2) :
      FlatTree (.record extent align fields)

def Layout.RespectsFlat (layout : Layout) (paths : List (List Nat)) : Prop :=
  ∀ path ∈ paths, ∃ offset size align fields,
    resolve layout path = some (⟨offset, none⟩, .record size align fields) ∧
    (Layout.record size align fields).FlatTree

private def declarationEnd (cursor : Nat) : List Field → Option Nat
  | [] => some cursor
  | (placement, child) :: children =>
    let start := alignUp cursor child.alignment
    if placement = ⟨start, none⟩ then declarationEnd (start + child.size) children else none

private theorem declarationEnd_sound {cursor ending : Nat} {fields : List Field}
    (found : declarationEnd cursor fields = some ending) : DeclarationSlots cursor fields ending := by
  induction fields generalizing cursor with
  | nil => cases found; exact .nil
  | cons field rest ih =>
    obtain ⟨placement, child⟩ := field
    simp only [declarationEnd, Option.ite_none_right_eq_some] at found
    obtain ⟨rfl, tail⟩ := found
    exact .cons (ih tail)

private def checkFlatTree : Nat → Layout → Bool
  | 0, _ => false
  | depth + 1, .record size align fields =>
    (declarationEnd 0 fields).any (fun ending =>
      align == fields.foldl (fun a f => max a f.2.alignment) 1 && size == alignUp ending align) &&
      fields.all (fun f => checkFlatTree depth f.2)
  | _ + 1, _ => true

private theorem checkFlatTree_sound {depth : Nat} {layout : Layout}
    (checked : checkFlatTree depth layout = true) : layout.FlatTree := by
  induction depth generalizing layout with
  | zero => simp [checkFlatTree] at checked
  | succ _ ih =>
    cases layout with
    | integer _ _ => exact .integer
    | fixed _ _ => exact .fixed
    | record size align fields =>
      simp only [checkFlatTree, Bool.and_eq_true, Option.any_eq_true, beq_iff_eq, List.all_eq_true] at checked
      obtain ⟨⟨_, ordered, alignment, stride⟩, children⟩ := checked
      exact .record (declarationEnd_sound ordered) alignment stride (fun f member => ih (children f member))

private def checkFlatPath (depth : Nat) (layout : Layout) (path : List Nat) : Bool :=
  match resolve layout path with
  | some (place, .record size align fields) =>
    place.bitOffset.isNone && checkFlatTree depth (.record size align fields)
  | _ => false

def planWithFlat (abi : TargetIntegerABI) (schema : Schema) (flatRecords : List (List Nat)) : Option Layout := do
  let layout ← checkedPlan abi schema flatRecords
  if flatRecords.all (checkFlatPath schema.depth layout) then some layout else none

theorem planWithFlat_sound {abi : TargetIntegerABI} {schema : Schema} {flatRecords : List (List Nat)}
    {layout : Layout} (planned : planWithFlat abi schema flatRecords = some layout) :
    Conforms abi schema layout ∧ layout.RespectsFlat flatRecords := by
  simp only [planWithFlat, bind, Option.bind_eq_some_iff, Option.ite_none_right_eq_some] at planned
  obtain ⟨_, checked, flat, equal⟩ := planned
  cases equal
  refine ⟨checkedPlan_sound checked, fun path member => ?_⟩
  have atPath := List.all_eq_true.mp flat path member
  unfold checkFlatPath at atPath
  split at atPath
  next place size align fields found =>
    obtain ⟨unpacked, tree⟩ := Bool.and_eq_true_iff.mp atPath
    cases place with
    | mk offset bitOffset =>
      simp only [Option.isNone_iff_eq_none] at unpacked
      subst bitOffset
      exact ⟨offset, size, align, fields, found, checkFlatTree_sound tree⟩
  next => contradiction

def Schema.resolve (schema : Schema) (path : List Nat) : Option Schema :=
  match path, schema with
  | [], _ => some schema
  | index :: rest, .record fields => fields[index]?.bind fun field => field.2.resolve rest
  | _ :: _, _ => none

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

theorem Conforms.resolvePacked {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {index : Nat} {rest : List Nat} {field : Field} (conforms : Conforms abi schema layout)
    (packed : layout.embeddable = true) (found : resolve layout (index :: rest) = some field) :
    field.1.bitOffset.isSome = true ∧ field.1.bitStart + field.2.bits ≤ layout.bits := by
  induction rest generalizing schema layout index field with
  | nil =>
    cases conforms with
    | integer _ => simp [resolve] at found
    | fixed _ => simp [resolve] at found
    | record aligned stride count separate placements children =>
      rename_i fields placed
      cases atIndex : placed[index]? with
      | none => simp [resolve, atIndex, bind] at found
      | some outer =>
        simp [resolve, atIndex, bind] at found
        subst field
        exact Layout.packedChild packed (List.mem_of_getElem? atIndex)
  | cons next rest ih =>
    cases conforms with
    | integer _ => simp [resolve] at found
    | fixed _ => simp [resolve] at found
    | record aligned stride count separate placements children =>
      rename_i fields placed
      cases atIndex : placed[index]? with
      | none => simp [resolve, atIndex, bind] at found
      | some outer =>
        obtain ⟨policy, child, _, valid, childValid⟩ :=
          (Conforms.record aligned stride count separate placements children).field atIndex
        obtain ⟨outerPacked, outerFits⟩ := Layout.packedChild packed (List.mem_of_getElem? atIndex)
        obtain ⟨location, localLayout⟩ := outer
        cases h : location.bitOffset with
        | none => simp [h] at outerPacked
        | some bit =>
          have embeddable : localLayout.embeddable = true := by
            have packedValid := valid.2
            rw [show (location, localLayout).1.bitOffset = some bit from h] at packedValid
            exact packedValid.2.1
          simp only [resolve, atIndex, bind, pure, Option.bind_eq_some_iff, Prod.exists,
            Option.some.injEq] at found
          obtain ⟨_, _, pairEq, inner, leaf, resolved, rfl⟩ := found
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEq
          obtain ⟨_, fits⟩ := ih childValid embeddable resolved
          refine ⟨by simp [Placement.rebase, h], ?_⟩
          change (location.rebase inner).bitStart + leaf.bits ≤ _
          rw [Placement.bitStart_rebase]
          change location.bitStart + localLayout.bits ≤ _ at outerFits
          change inner.bitStart + leaf.bits ≤ localLayout.bits at fits
          omega

theorem Conforms.alignment_pos {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) : 0 < layout.alignment := by
  have power : layout.alignment.isPowerOfTwo := by
    cases planned with
    | integer slot => exact slot.2.1
    | fixed slot => exact slot.2.1
    | record aligned _ _ _ _ _ => exact aligned
  obtain ⟨exponent, h⟩ := power
  rw [h]
  exact Nat.two_pow_pos exponent

private theorem Field.Valid.allowPacking {total align : Nat} {policy : StoragePolicy} {field : Field}
    (valid : Field.Valid total align policy field) : Field.Valid total align .mayShareByte field := by
  cases h : field.1.bitOffset <;> simp_all [Field.Valid]

private theorem Field.Valid.rebaseAddressable {total align : Nat} {outer inner : Field}
    (outside : Field.Valid total align .mayShareByte outer) (addressable : outer.1.bitOffset = none)
    (inside : Field.Valid outer.2.size outer.2.alignment .mayShareByte inner) :
    Field.Valid total align .mayShareByte
      (outer.1.rebase inner.1, inner.2) := by
  unfold Placement.rebase
  rw [addressable]
  have bounds := outside.1
  simp only [Field.bytes, addressable, Option.isSome_none, Bool.false_eq_true, ite_false] at bounds
  have aligned := outside.2
  rw [addressable] at aligned
  refine ⟨by change outer.1.byteOffset + inner.1.byteOffset + inner.bytes ≤ total; have := inside.1; omega, ?_⟩
  cases h : inner.1.bitOffset with
  | some bit =>
    have packed := inside.2
    rw [h] at packed
    refine ⟨packed.1, packed.2.1, packed.2.2.1, ?_⟩
    have fits := packed.2.2.2
    simp [Placement.bitStart, h] at fits ⊢
    omega
  | none =>
    have proper := inside.2
    rw [h] at proper
    have outerOffset : inner.2.alignment ∣ outer.1.byteOffset :=
      Nat.dvd_trans (Nat.dvd_of_mod_eq_zero proper.2.2) (Nat.dvd_of_mod_eq_zero aligned.2.1)
    have base : inner.2.alignment ∣ align :=
      Nat.dvd_trans (Nat.dvd_of_mod_eq_zero proper.2.2) (Nat.dvd_of_mod_eq_zero aligned.2.2)
    exact ⟨proper.1, Nat.mod_eq_zero_of_dvd (Nat.dvd_add outerOffset
      (Nat.dvd_of_mod_eq_zero proper.2.1)), Nat.mod_eq_zero_of_dvd base⟩

private theorem Field.Valid.rebasePacked {total align bit : Nat} {outer inner : Field}
    (outside : Field.Valid total align .mayShareByte outer) (packed : outer.1.bitOffset = some bit)
    (inside : inner.1.bitStart + inner.2.bits ≤ outer.2.bits)
    (embeddable : inner.2.embeddable = true) :
    Field.Valid total align .mayShareByte (outer.1.rebase inner.1, inner.2) := by
  have valid := outside.2
  rw [packed] at valid
  have bound : (outer.1.rebase inner.1).bitStart + inner.2.bits ≤ total * 8 := by
    rw [Placement.bitStart_rebase]
    have outerFits := valid.2.2.2
    omega
  refine ⟨?_, ?_⟩
  · simp [Placement.rebase, packed, Placement.bitStart] at bound
    simp [Placement.rebase, packed, Field.bytes]
    split <;> omega
  · have bitOffset : (outer.1.rebase inner.1, inner.2).1.bitOffset =
        some ((outer.1.bitStart + inner.1.bitStart) % 8) := by simp [Placement.rebase, packed]
    rw [bitOffset]
    exact ⟨rfl, embeddable, Nat.mod_lt _ (by decide), bound⟩

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
    | fixed valid => simp [resolve] at found
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
          refine ⟨target, by simp [Schema.resolve, source, targetAt], targetValid, ?_⟩
          cases h : location.bitOffset with
          | none => exact fieldValid.allowPacking.rebaseAddressable h innerValid
          | some bit =>
            have outerEmbeddable : localLayout.embeddable = true := by
              have valid := fieldValid.2
              rw [show (location, localLayout).1.bitOffset = some bit from h] at valid
              exact valid.2.1
            obtain ⟨packed, fits⟩ := childValid.resolvePacked outerEmbeddable resolved
            have innerEmbeddable : leaf.embeddable = true := by
              cases atBit : inner.bitOffset with
              | none => simp [atBit] at packed
              | some _ =>
                have valid := innerValid.2
                rw [show (inner, leaf).1.bitOffset = _ from atBit] at valid
                exact valid.2.1
            exact fieldValid.allowPacking.rebasePacked h fits innerEmbeddable

theorem resolve_complete {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {path : List Nat} {child : Schema} (planned : Conforms abi schema layout)
    (declared : schema.resolve path = some child) :
    ∃ field, resolve layout path = some field ∧ Conforms abi child field.2 := by
  induction path generalizing schema layout child with
  | nil =>
    cases declared
    exact ⟨(⟨0, none⟩, layout), rfl, planned⟩
  | cons index rest ih =>
    cases planned with
    | integer _ => simp [Schema.resolve] at declared
    | fixed _ => simp [Schema.resolve] at declared
    | record aligned stride count separate placements children =>
      rename_i fields placed
      cases source : fields[index]? with
      | none => simp [Schema.resolve, source] at declared
      | some entry =>
        have within := (List.getElem?_eq_some_iff.mp source).1
        have present : index < placed.length := count ▸ within
        have found := List.getElem?_eq_getElem (l := placed) present
        obtain ⟨policy, ty, agrees, _, conforms⟩ :=
          (Conforms.record aligned stride count separate placements children).field found
        rw [source] at agrees
        have same : entry.2 = ty := congrArg Prod.snd (Option.some.inj agrees)
        have nested : ty.resolve rest = some child := by
          simpa [Schema.resolve, source, same] using declared
        cases rest with
        | nil =>
          cases nested
          exact ⟨placed[index], by simp [resolve, found, bind], conforms⟩
        | cons next rest =>
          obtain ⟨inner, located, valid⟩ := ih conforms nested
          exact ⟨(placed[index].1.rebase inner.1, inner.2), by simp [resolve, found, located, bind, pure], valid⟩

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
