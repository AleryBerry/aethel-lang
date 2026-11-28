import Aethel.PackedMachine

namespace Aethel.AutomaticLayout

open Core Structured

/-- An array allocation uses a whole byte stride per element. The limit is
the largest permitted one-past-end pointer, and is excluded from byte addresses. -/
structure PackedArrayRegion (layout : Layout) where
  base : Nat
  count : Nat
  limit : Nat

def PackedArrayRegion.Valid (region : PackedArrayRegion layout) : Prop :=
  0 < layout.alignment ∧ layout.size % layout.alignment = 0 ∧
    region.base % layout.alignment = 0 ∧
    region.base + region.count * layout.size ≤ region.limit

instance (region : PackedArrayRegion layout) : Decidable region.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def PackedArrayRegion.rowBase (region : PackedArrayRegion layout) (index : Nat) : Nat :=
  region.base + index * layout.size

theorem Conforms.stride_aligned {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) :
    layout.size % layout.alignment = 0 := by
  cases planned with
  | integer slot => exact slot.2.2
  | fixed slot => exact slot.2.2.1
  | record _ stride _ _ _ _ => exact stride

theorem PackedArrayRegion.valid_of_layout {abi : TargetIntegerABI} {schema : Schema}
    {layout : Layout} (region : PackedArrayRegion layout) (planned : Conforms abi schema layout)
    (aligned : region.base % layout.alignment = 0)
    (fits : region.base + region.count * layout.size ≤ region.limit) :
    region.Valid :=
  ⟨planned.alignment_pos, planned.stride_aligned, aligned, fits⟩

theorem PackedArrayRegion.rowBase_aligned {region : PackedArrayRegion layout} (valid : region.Valid)
    (index : Nat) : region.rowBase index % layout.alignment = 0 := by
  have localStride := valid.2.1
  have base := valid.2.2.1
  unfold rowBase
  rw [Nat.add_mod, Nat.mul_mod, localStride, base]
  simp

theorem PackedArrayRegion.row_end_le {region : PackedArrayRegion layout} {left right : Nat}
    (ordered : left < right) : region.rowBase left + layout.size ≤ region.rowBase right := by
  have orderedStride := Nat.mul_le_mul_right layout.size (Nat.succ_le_of_lt ordered)
  rw [Nat.succ_mul] at orderedStride
  unfold rowBase
  omega

theorem PackedArrayRegion.row_end_within {region : PackedArrayRegion layout} {index : Nat}
    (valid : region.Valid) (inBounds : index < region.count) :
    region.rowBase index + layout.size ≤ region.limit :=
  Nat.le_trans (region.row_end_le inBounds) valid.2.2.2

/-- Resolve a proved row-relative field to checked target addresses. A
zero-width field still requires a live row and yields an empty address list. -/
def PackedArrayRegion.addresses (region : PackedArrayRegion layout) (index : Nat)
    (field : PackedValueField layout.size width) : Option (List Nat) :=
  if region.Valid ∧ index < region.count then
    some (field.byteOffsets.map fun byte => region.rowBase index + byte)
  else none

theorem PackedArrayRegion.addresses_correct (region : PackedArrayRegion layout) (index : Nat)
    (field : PackedValueField layout.size width) (addresses : List Nat) :
    region.addresses index field = some addresses ↔ region.Valid ∧ index < region.count ∧
      addresses = field.byteOffsets.map (fun byte => region.rowBase index + byte) := by
  simp only [PackedArrayRegion.addresses, Option.ite_none_right_eq_some, Option.some.injEq]
  exact ⟨fun ⟨⟨valid, bound⟩, placed⟩ => ⟨valid, bound, placed.symm⟩,
    fun ⟨valid, bound, placed⟩ => ⟨⟨valid, bound⟩, placed.symm⟩⟩

theorem PackedArrayRegion.addresses_within {region : PackedArrayRegion layout} {index : Nat}
    {field : PackedValueField layout.size width} {addresses : List Nat}
    (resolved : region.addresses index field = some addresses) {address : Nat}
    (member : address ∈ addresses) :
    region.rowBase index ≤ address ∧ address < region.rowBase index + layout.size ∧
      address < region.limit := by
  obtain ⟨valid, inBounds, rfl⟩ := (region.addresses_correct index field addresses).mp resolved
  obtain ⟨byte, touched, rfl⟩ := List.mem_map.mp member
  have fits := field.byteOffset_inBounds touched
  have endWithin := region.row_end_within valid inBounds
  omega

theorem PackedArrayRegion.rows_disjoint {region : PackedArrayRegion layout} {left right : Nat}
    {a : PackedValueField layout.size w} {b : PackedValueField layout.size v}
    {xs ys : List Nat} (first : region.addresses left a = some xs)
    (second : region.addresses right b = some ys) (distinct : left ≠ right) :
    ∀ address ∈ xs, address ∉ ys := by
  intro address aMember bMember
  have withinA := region.addresses_within first aMember
  have withinB := region.addresses_within second bMember
  rcases Nat.lt_or_gt_of_ne distinct with before | after
  · exact (Nat.not_lt_of_ge (Nat.le_trans (region.row_end_le before) withinB.1)) withinA.2.1
  · exact (Nat.not_lt_of_ge (Nat.le_trans (region.row_end_le after) withinA.1)) withinB.2.1

theorem PackedArrayRegion.resolved_access {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (region : PackedArrayRegion layout) (valid : region.Valid)
    (planned : Conforms abi schema layout) {index : Nat} (inBounds : index < region.count)
    {path : List Nat} {field : Field} (found : resolve layout path = some field)
    (nonempty : 0 < field.bytes) :
    checkAccess layout.size (region.rowBase index) field.1.byteOffset field.bytes
      field.accessAlignment region.limit = true :=
  AutomaticLayout.resolved_access planned found nonempty
    (region.rowBase_aligned valid index) (region.row_end_within valid inBounds)

private theorem rowOffset_fits {stride count : Nat} (row : Fin count) (byte : Fin stride) :
    row.val * stride + byte.val < count * stride := by
  have bound := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt row.isLt)
  rw [Nat.succ_mul] at bound
  omega

def PackedArrayRegion.readRow (region : PackedArrayRegion layout)
    (image : Image (region.count * layout.size)) (row : Fin region.count) : Image layout.size :=
  fun byte => image ⟨row.val * layout.size + byte.val, rowOffset_fits row byte⟩

def PackedArrayRegion.encodeRows (region : PackedArrayRegion layout)
    (rows : Fin region.count → Image layout.size) : Image (region.count * layout.size) :=
  fun byte =>
    if nonempty : 0 < layout.size then
      rows ⟨byte.val / layout.size, (Nat.div_lt_iff_lt_mul nonempty).mpr byte.isLt⟩
        ⟨byte.val % layout.size, Nat.mod_lt _ nonempty⟩
    else
      have empty : layout.size = 0 := Nat.eq_zero_of_not_pos nonempty
      (Nat.not_lt_zero byte.val (by simpa [empty] using byte.isLt)).elim

theorem PackedArrayRegion.readRow_encodeRows (region : PackedArrayRegion layout)
    (rows : Fin region.count → Image layout.size) (row : Fin region.count) :
    region.readRow (region.encodeRows rows) row = rows row := by
  funext byte
  have positive : 0 < layout.size := Nat.zero_lt_of_lt byte.isLt
  unfold readRow encodeRows
  rw [dite_eq_left positive]
  congr 1
  · apply Fin.ext
    change (row.val * layout.size + byte.val) / layout.size = row.val
    rw [Nat.mul_comm row.val, Nat.mul_add_div positive, Nat.div_eq_of_lt byte.isLt, Nat.add_zero]
  · apply Fin.ext
    change (row.val * layout.size + byte.val) % layout.size = byte.val
    rw [Nat.mul_comm row.val, Nat.mul_add_mod, Nat.mod_eq_of_lt byte.isLt]

def PackedArrayRegion.writeRow (region : PackedArrayRegion layout)
    (image : Image (region.count * layout.size)) (row : Fin region.count) (data : Image layout.size) :
    Image (region.count * layout.size) :=
  fun byte =>
    let start := row.val * layout.size
    if inside : start ≤ byte.val ∧ byte.val < start + layout.size then
      data ⟨byte.val - start, by omega⟩
    else image byte

theorem PackedArrayRegion.readRow_writeRow (region : PackedArrayRegion layout)
    (image : Image (region.count * layout.size)) (row : Fin region.count) (data : Image layout.size) :
    region.readRow (region.writeRow image row data) row = data := by
  funext byte
  unfold readRow writeRow
  have inside : row.val * layout.size ≤ row.val * layout.size + byte.val ∧
      row.val * layout.size + byte.val < row.val * layout.size + layout.size := by
    have bound := byte.isLt
    omega
  rw [dite_eq_left inside]
  congr 1
  exact Fin.ext (by simp)

theorem PackedArrayRegion.writeRow_preserves_other (region : PackedArrayRegion layout)
    (image : Image (region.count * layout.size)) (row other : Fin region.count)
    (data : Image layout.size) (distinct : row ≠ other) :
    region.readRow (region.writeRow image row data) other = region.readRow image other := by
  funext byte
  have bounds := byte.isLt
  have separate := fun {i j : Nat} (ordered : i < j) => region.row_end_le ordered
  have different : row.val ≠ other.val := fun equal => distinct (Fin.ext equal)
  have notInside : ¬ (row.val * layout.size ≤ other.val * layout.size + byte.val ∧
      other.val * layout.size + byte.val < row.val * layout.size + layout.size) := by
    rcases Nat.lt_or_gt_of_ne different with before | after
    · have bound := separate before
      unfold rowBase at bound
      omega
    · have bound := separate after
      unfold rowBase at bound
      omega
  unfold readRow writeRow
  rw [dite_eq_right notInside]

def PackedArrayRegion.readValue (region : PackedArrayRegion layout)
    (image : Image (region.count * layout.size)) (row : Fin region.count)
    (field : PackedValueField layout.size width) (codec : PackedCodec α width) : Option α :=
  field.load codec (region.readRow image row)

def PackedArrayRegion.writeValue (region : PackedArrayRegion layout)
    (image : Image (region.count * layout.size)) (row : Fin region.count)
    (field : PackedValueField layout.size width) (codec : PackedCodec α width) (value : α) :
    Image (region.count * layout.size) :=
  region.writeRow image row (field.store codec (region.readRow image row) value)

theorem PackedArrayRegion.readValue_writeValue (region : PackedArrayRegion layout)
    (image : Image (region.count * layout.size)) (row : Fin region.count)
    (field : PackedValueField layout.size width) (codec : PackedCodec α width) (value : α) :
    region.readValue (region.writeValue image row field codec value) row field codec = some value := by
  simp [readValue, writeValue, readRow_writeRow, PackedValueField.load_store]

theorem PackedArrayRegion.writeValue_preserves_other (region : PackedArrayRegion layout)
    (image : Image (region.count * layout.size)) (row other : Fin region.count)
    (field : PackedValueField layout.size width) (codec : PackedCodec α width) (value : α)
    (observed : PackedValueField layout.size v) (reader : PackedCodec β v) (distinct : row ≠ other) :
    region.readValue (region.writeValue image row field codec value) other observed reader =
      region.readValue image other observed reader := by
  simp [readValue, writeValue, writeRow_preserves_other, distinct]

def PackedArrayRegion.fieldAtRow (region : PackedArrayRegion layout) (row : Fin region.count)
    (field : PackedValueField layout.size width) : PackedValueField (region.count * layout.size) width :=
  ⟨row.val * layout.size * 8 + field.start, by
    have fits := field.fits
    have bound := Nat.mul_le_mul_right layout.size (Nat.succ_le_of_lt row.isLt)
    rw [Nat.succ_mul] at bound
    omega⟩

theorem PackedArrayRegion.fieldAtRow_offsets (region : PackedArrayRegion layout)
    (row : Fin region.count) (field : PackedValueField layout.size width) :
    (region.fieldAtRow row field).byteOffsets =
      field.byteOffsets.map (fun byte => row.val * layout.size + byte) := by
  let start := row.val * layout.size
  change bitIntervalBytes (start * 8 + field.start) width = (bitIntervalBytes field.start width).map (start + ·)
  have modEq : (start * 8 + field.start) % 8 = field.start % 8 := by omega
  have divEq : (start * 8 + field.start) / 8 = start + field.start / 8 := by omega
  by_cases empty : width = 0
  · simp [bitIntervalBytes, empty]
  · simp [bitIntervalBytes, empty, modEq, divEq, List.map_map, Function.comp_def, Nat.add_assoc]

private theorem bit_at_byte (image : Image size) (address : Fin size) (bit : Nat) (within : bit < 8) :
    image.bit (address.val * 8 + bit) = (image address).getLsbD bit := by
  have divEq : (address.val * 8 + bit) / 8 = address.val := by omega
  have modEq : (address.val * 8 + bit) % 8 = bit := by omega
  simp [Image.bit, divEq, modEq, address.isLt]

theorem PackedArrayRegion.fieldAtRow_load (region : PackedArrayRegion layout)
    (image : Image (region.count * layout.size)) (row : Fin region.count)
    (field : PackedValueField layout.size width) (codec : PackedCodec α width) :
    (region.fieldAtRow row field).load codec image = region.readValue image row field codec := by
  unfold readValue PackedValueField.load
  rw [Image.readBytes_refines, Image.readBytes_refines]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro bit declared
  rw [Image.readBits_getLsbD _ _ _ declared, Image.readBits_getLsbD _ _ _ declared]
  let start := row.val * layout.size
  have inside : (field.start + bit) / 8 < layout.size := by have := field.fits; omega
  have divEq : ((region.fieldAtRow row field).start + bit) / 8 = start + (field.start + bit) / 8 := by
    change (start * 8 + field.start + bit) / 8 = _
    omega
  have modEq : ((region.fieldAtRow row field).start + bit) % 8 = (field.start + bit) % 8 := by
    change (start * 8 + field.start + bit) % 8 = _
    omega
  have rowEnd : start + layout.size ≤ region.count * layout.size := by
    have h := Nat.mul_le_mul_right layout.size (Nat.succ_le_of_lt row.isLt)
    simpa only [start, Nat.succ_mul] using h
  have absolute : start + (field.start + bit) / 8 < region.count * layout.size := by omega
  simp only [Image.bit, divEq, modEq, dite_eq_left inside, dite_eq_left absolute, readRow]
  rfl

theorem PackedArrayRegion.fieldAtRow_store (region : PackedArrayRegion layout)
    (image : Image (region.count * layout.size)) (row : Fin region.count)
    (field : PackedValueField layout.size width) (codec : PackedCodec α width) (value : α) :
    (region.fieldAtRow row field).store codec image value = region.writeValue image row field codec value := by
  unfold writeValue PackedValueField.store
  rw [Image.writeBytes_refines, Image.writeBytes_refines]
  funext address
  apply BitVec.eq_of_getLsbD_eq
  intro bit small
  rw [← bit_at_byte _ address bit small, Image.bit_write _ _ _ _ (by have := address.isLt; omega)]
  unfold writeRow
  let start := row.val * layout.size
  change (if start * 8 + field.start ≤ address.val * 8 + bit ∧
      address.val * 8 + bit < start * 8 + field.start + width then
      (codec.encode value).getLsbD (address.val * 8 + bit - (start * 8 + field.start))
    else image.bit (address.val * 8 + bit)) = _
  by_cases inside : start ≤ address.val ∧ address.val < start + layout.size
  · rw [dite_eq_left inside]
    let relative : Fin layout.size := ⟨address.val - start, by omega⟩
    change _ = ((region.readRow image row).writeBits field.start (codec.encode value) relative).getLsbD bit
    rw [← bit_at_byte _ relative bit small, Image.bit_write _ _ _ _ (by have := relative.isLt; omega)]
    have decompose : address.val = start + relative.val := by dsimp [relative]; omega
    have sameRange : (start * 8 + field.start ≤ address.val * 8 + bit ∧
        address.val * 8 + bit < start * 8 + field.start + width) ↔
        (field.start ≤ relative.val * 8 + bit ∧ relative.val * 8 + bit < field.start + width) := by omega
    simp only [sameRange]
    split
    · congr 1
      omega
    · rw [bit_at_byte image address bit small, bit_at_byte (region.readRow image row) relative bit small]
      unfold readRow
      have bound : row.val * layout.size + relative.val < region.count * layout.size := decompose ▸ address.isLt
      have eq : (⟨row.val * layout.size + relative.val, bound⟩ : Fin (region.count * layout.size)) = address :=
        Fin.ext decompose.symm
      rw [eq]
  · rw [dite_eq_right inside]
    have untouched : ¬ (start * 8 + field.start ≤ address.val * 8 + bit ∧
        address.val * 8 + bit < start * 8 + field.start + width) := by
      have := field.fits
      omega
    rw [ite_eq_right untouched, bit_at_byte image address bit small]

theorem PackedArrayRegion.fieldAtRow_addresses (region : PackedArrayRegion layout) (valid : region.Valid)
    (row : Fin region.count) (field : PackedValueField layout.size width) :
    region.addresses row.val field = some ((region.fieldAtRow row field).byteOffsets.map (region.base + ·)) := by
  apply (region.addresses_correct row.val field _).mpr
  exact ⟨valid, row.isLt, by simp [region.fieldAtRow_offsets, List.map_map, Function.comp_def, rowBase, Nat.add_assoc]⟩

def PackedArrayRegion.allocateRows (region : PackedArrayRegion layout) (state : State) (owner : OwnerId)
    (rows : Fin region.count → Image layout.size) : Option State :=
  if region.Valid then execute state (.alloc owner (region.encodeRows rows).toBytes) else none

theorem PackedArrayRegion.allocateRows_sound {region : PackedArrayRegion layout}
    {state next : State} {owner : OwnerId} {rows : Fin region.count → Image layout.size}
    (ran : region.allocateRows state owner rows = some next) :
    region.Valid ∧ Step state (.alloc owner (region.encodeRows rows).toBytes) next ∧
      (region.encodeRows rows).InAllocation owner next := by
  obtain ⟨valid, allocated⟩ := Option.ite_none_right_eq_some.mp ran
  have step := execute_sound allocated
  exact ⟨valid, step, Image.inAllocation_of_alloc step⟩

def PackedArrayRegion.readMachine (region : PackedArrayRegion layout) (codec : PackedCodec α width)
    (state : State) (owner : OwnerId) (index : Nat) (field : PackedValueField layout.size width)
    (targets : List AccessTarget) : Option α :=
  if checked : region.Valid ∧ index < region.count then
    (region.fieldAtRow ⟨index, checked.2⟩ field).readMachine codec state owner targets
  else none

theorem PackedArrayRegion.readMachine_sound {region : PackedArrayRegion layout}
    {codec : PackedCodec α width} {state : State} {owner : OwnerId} {index : Nat}
    {field : PackedValueField layout.size width} {targets : List AccessTarget}
    {image : Image (region.count * layout.size)} {value : α}
    (represented : image.InAllocation owner state)
    (ran : region.readMachine codec state owner index field targets = some value) :
    ∃ row : Fin region.count, row.val = index ∧ region.Valid ∧
      AccessAllowed state owner .shared (region.fieldAtRow row field).byteOffsets targets ∧
      region.readValue image row field codec = some value ∧
      RunsOnStorage state (targets.map AccessTarget.readInstruction) state := by
  unfold readMachine at ran
  split at ran
  next checked =>
    let row : Fin region.count := ⟨index, checked.2⟩
    have loaded := (region.fieldAtRow row field).readMachine_on_image codec represented ran
    rw [region.fieldAtRow_load] at loaded
    exact ⟨row, rfl, checked.1, (region.fieldAtRow row field).readMachine_authorized codec ran,
      loaded, (region.fieldAtRow row field).readMachine_on_storage codec ran⟩
  next => cases ran

def PackedArrayRegion.writeMachine (region : PackedArrayRegion layout) (codec : PackedCodec α width)
    (state : State) (owner : OwnerId) (index : Nat) (field : PackedValueField layout.size width)
    (targets : List AccessTarget) (value : α) : Option State :=
  if checked : region.Valid ∧ index < region.count then
    (region.fieldAtRow ⟨index, checked.2⟩ field).writeMachine codec state owner targets value
  else none

theorem PackedArrayRegion.writeMachine_sound {region : PackedArrayRegion layout}
    {codec : PackedCodec α width} {state next : State} {owner : OwnerId} {index : Nat}
    {field : PackedValueField layout.size width} {targets : List AccessTarget}
    {image : Image (region.count * layout.size)} {value : α}
    (represented : image.InAllocation owner state)
    (ran : region.writeMachine codec state owner index field targets value = some next) :
    ∃ row : Fin region.count, row.val = index ∧ region.Valid ∧
      AccessAllowed state owner .exclusive (region.fieldAtRow row field).byteOffsets targets ∧
      (region.writeValue image row field codec value).InAllocation owner next ∧ next.resources = state.resources ∧
      (∀ other : Fin region.count, other ≠ row →
        region.readRow (region.writeValue image row field codec value) other = region.readRow image other) ∧
      ∃ program, (region.fieldAtRow row field).writeProgram codec state owner targets value = some program ∧
        Runs state program next := by
  unfold writeMachine at ran
  split at ran
  next checked =>
    let row : Fin region.count := ⟨index, checked.2⟩
    let translated := region.fieldAtRow row field
    have stored := translated.writeMachine_on_image codec represented ran
    change ((region.fieldAtRow row field).store codec image value).InAllocation owner next at stored
    rw [region.fieldAtRow_store] at stored
    obtain ⟨allowed, _⟩ := translated.writeMachine_refines codec ran
    refine ⟨row, rfl, checked.1, allowed, stored, translated.writeMachine_preserves_resources codec ran,
      fun other distinct => ?_, translated.writeProgram_correct codec ran⟩
    exact region.writeRow_preserves_other image row other _ (Ne.symm distinct)
  next => cases ran

/-- Fixed-word calculation of the target address of a byte within a row. -/
def PackedArrayRegion.wordAddress (region : PackedArrayRegion layout) (wordBits index byte : Nat) :
    BitVec wordBits :=
  (BitVec.ofNat wordBits region.base + BitVec.ofNat wordBits index * BitVec.ofNat wordBits layout.size) +
    BitVec.ofNat wordBits byte

theorem PackedArrayRegion.wordAddress_exact {region : PackedArrayRegion layout}
    {index byte wordBits : Nat} (valid : region.Valid) (row : index < region.count)
    (inRow : byte < layout.size) (limitFits : region.limit < 2 ^ wordBits) :
    region.base < 2 ^ wordBits ∧ index < 2 ^ wordBits ∧ layout.size < 2 ^ wordBits ∧
    index * layout.size < 2 ^ wordBits ∧ region.rowBase index < 2 ^ wordBits ∧
    (region.wordAddress wordBits index byte).toNat = region.rowBase index + byte := by
  have within := region.row_end_within valid row
  have stridePositive : 0 < layout.size := Nat.zero_lt_of_lt inRow
  have indexFits := Nat.le_mul_of_pos_right index stridePositive
  have byteFits : region.rowBase index + byte < 2 ^ wordBits := by omega
  have addressEq : (region.wordAddress wordBits index byte).toNat = region.rowBase index + byte := by
    rw [wordAddress, BitVec.ofNat_mul_ofNat, BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
    change (region.rowBase index + byte) % (2 ^ wordBits) = region.rowBase index + byte
    exact Nat.mod_eq_of_lt byteFits
  unfold rowBase at within
  exact ⟨by omega, by omega, by omega, by omega, by omega, addressEq⟩

theorem PackedArrayRegion.wordAddresses_exact {region : PackedArrayRegion layout}
    {index width wordBits : Nat} {field : PackedValueField layout.size width} {addresses : List Nat}
    (resolved : region.addresses index field = some addresses) (limitFits : region.limit < 2 ^ wordBits) :
    (field.byteOffsets.map fun byte => (region.wordAddress wordBits index byte).toNat) = addresses := by
  obtain ⟨valid, row, rfl⟩ := (region.addresses_correct index field addresses).mp resolved
  apply List.map_congr_left
  intro byte member
  exact (region.wordAddress_exact valid row (field.byteOffset_inBounds member) limitFits).2.2.2.2.2

end Aethel.AutomaticLayout
