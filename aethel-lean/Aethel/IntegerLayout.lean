import Aethel.IntegerTypes
import Aethel.LayoutAlgebra

namespace Aethel

/-- Byte-addressable size and alignment supplied by the selected target ABI. -/
structure IntegerSlot where
  size : Nat
  alignment : Nat
  deriving Repr, DecidableEq

structure TargetIntegerABI where
  slot : IntegerType → IntegerSlot

def IntegerType.payloadBytes (ty : IntegerType) : Nat :=
  (ty.bits + 7) / 8

def naturalAlignment (payloadBytes : Nat) : Nat :=
  if payloadBytes ≤ 1 then 1
  else if payloadBytes ≤ 2 then 2
  else if payloadBytes ≤ 4 then 4
  else if payloadBytes ≤ 8 then 8
  else 16

theorem naturalAlignment_isPowerOfTwo (b : Nat) : (naturalAlignment b).isPowerOfTwo := by
  unfold naturalAlignment
  split
  · exact ⟨0, rfl⟩
  · split
    · exact ⟨1, rfl⟩
    · split
      · exact ⟨2, rfl⟩
      · split
        · exact ⟨3, rfl⟩
        · exact ⟨4, rfl⟩

private theorem naturalAlignment_pos (b : Nat) : 0 < naturalAlignment b := by
  unfold naturalAlignment
  split
  · decide
  · split
    · decide
    · split
      · decide
      · split <;> decide

/-- Conventional ABI policy for arbitrary bit-width scalars: byte payload
rounded up to power-of-two alignment capped at 16 bytes. A backend supplies
and validates the actual target ABI. -/
def TargetIntegerABI.natural : TargetIntegerABI :=
  ⟨fun ty =>
    let align := naturalAlignment ty.payloadBytes
    ⟨alignUp ty.payloadBytes align, align⟩⟩

def IntegerSlot.Valid (slot : IntegerSlot) (ty : IntegerType) : Prop :=
  ty.payloadBytes ≤ slot.size ∧ slot.alignment.isPowerOfTwo ∧ slot.size % slot.alignment = 0

instance IntegerSlot.instDecidableValid (slot : IntegerSlot) (ty : IntegerType) : Decidable (slot.Valid ty) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem IntegerType.payloadBytes_pos (ty : IntegerType) : 0 < ty.payloadBytes := by
  have hPos := ty.bits_pos
  unfold IntegerType.payloadBytes
  omega

theorem TargetIntegerABI.natural_valid (ty : IntegerType) : (natural.slot ty).Valid ty := by
  refine ⟨?_, naturalAlignment_isPowerOfTwo _, ?_⟩
  · change ty.payloadBytes ≤ alignUp ty.payloadBytes (naturalAlignment ty.payloadBytes)
    exact Nat.le_add_right _ _
  · exact alignUp_aligned ty.payloadBytes (naturalAlignment_pos _)

/-- An addressable integer occupies a whole slot. The slot size, including
any padding required by the target, also serves as the array stride. -/
def TargetIntegerABI.place (abi : TargetIntegerABI) (ty : IntegerType)
    (cursor : Nat) : Option FieldPlacement :=
  let slot := abi.slot ty
  if slot.Valid ty then
    some ⟨alignUp cursor slot.alignment, slot.size, slot.alignment⟩
  else none

theorem TargetIntegerABI.place_sound {abi : TargetIntegerABI} {ty : IntegerType}
    {cursor : Nat} {field : FieldPlacement} (placed : abi.place ty cursor = some field) :
    (abi.slot ty).Valid ty ∧ cursor ≤ field.offset ∧ ty.payloadBytes ≤ field.size ∧
      field.Valid (field.offset + field.size) := by
  dsimp only [place] at placed
  split at placed
  next valid =>
    cases placed
    have aligned : 0 < (abi.slot ty).alignment := by
      obtain ⟨power, h⟩ := valid.2.1
      rw [h]
      exact Nat.two_pow_pos power
    exact ⟨valid, Nat.le_add_right _ _, valid.1,
      Nat.lt_of_lt_of_le ty.payloadBytes_pos valid.1, aligned, alignUp_aligned cursor aligned,
      Nat.le_refl _⟩
  next => cases placed

theorem TargetIntegerABI.placed_access {abi : TargetIntegerABI} {ty : IntegerType}
    {cursor capacity base addressLimit : Nat} {field : FieldPlacement}
    (placed : abi.place ty cursor = some field)
    (baseAligned : base % field.alignment = 0)
    (fits : field.offset + field.size ≤ capacity)
    (addressSpace : base + capacity ≤ addressLimit) :
    checkAccess capacity base field.offset field.size field.alignment addressLimit = true := by
  obtain ⟨_, _, _, positive, alignment, offsetAligned, _⟩ := place_sound placed
  exact decide_eq_true ⟨positive, alignment, fits, addressSpace,
    by rw [Nat.add_mod, baseAligned, offsetAligned]; simp⟩

/-- Sub-byte fields can share a storage byte when the surrounding borrow and
layout policy permits it. Packed offsets count bits within that byte. -/
def IntegerType.checkPackedByte (ty : IntegerType) (offset : Nat) : Bool :=
  decide (ty.bits < 8 ∧ offset + ty.bits ≤ 8)

theorem IntegerType.checkPackedByte_correct (ty : IntegerType) (offset : Nat) :
    ty.checkPackedByte offset = true ↔ ty.bits < 8 ∧ offset + ty.bits ≤ 8 := by
  simp [checkPackedByte]

end Aethel
