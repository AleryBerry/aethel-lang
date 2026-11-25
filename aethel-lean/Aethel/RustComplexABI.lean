import Aethel.LayoutAlgebra
import Aethel.CacheLayout
import Aethel.RustFFI

namespace Aethel.RustComplexABI

open Aethel Aethel.Core Aethel.CacheLayout Aethel.RustFFI

/-!
## Complex Rust ABI Bridge: Flat C-ABI Structs, Split SoA Queries & 64B AoSoA Tiles

Establishes representation soundness for feeding Aethel's L1-optimized structures
zero-copy into Rust libraries:
1. `planFlatStruct` proves deterministic declaration-order field placement matches
   Rust `#[repr(C)]` layout (`FieldsShape::Arbitrary` + array stride).
2. `soa_query_slices_pairwise_compatible` and `soa_query_preserves_unqueried_columns`
   prove Bevy-style split SoA ECS queries (`entities ~>.{pos, vel}`) produce
   pairwise compatible `&mut [T]` / `&[T]` Rust slices while leaving untouched sibling
   columns (`health`) preserved byte-for-byte.
3. `aosoa_tile_rust_offset_eq` and `aosoa_tile_64B_aligned` prove physical
   64-byte-aligned AoSoA tile arrays match `CacheLayout.aosoaSlot` exactly so
   Rust SIMD kernels operate zero-copy on Aethel tile buffers.
-/

/-! ### Part A: Deterministic Flat C-ABI Struct Layout (`#[repr(C)]`) -/

structure FlatFieldSpec where
  size : Nat
  alignment : Nat
  sizePos : 0 < size
  alignPos : 0 < alignment
  alignPow2 : alignment.isPowerOfTwo
  strideAligned : size % alignment = 0
  deriving Repr

private def placeFlatFields (curOffset : Nat) : List FlatFieldSpec → List FieldPlacement × Nat
  | [] => ([], curOffset)
  | f :: rest =>
    let off := alignUp curOffset f.alignment
    let nextOff := off + f.size
    let (placedRest, finalEnd) := placeFlatFields nextOff rest
    (⟨off, f.size, f.alignment⟩ :: placedRest, finalEnd)

def maxFieldAlign : List FlatFieldSpec → Nat
  | [] => 1
  | f :: rest => max f.alignment (maxFieldAlign rest)

def planFlatStruct (fields : List FlatFieldSpec) : RecordLayout :=
  let (placed, rawEnd) := placeFlatFields 0 fields
  let structAlign := maxFieldAlign fields
  let totalSize := alignUp rawEnd structAlign
  { size := totalSize, alignment := structAlign, fields := placed }

private theorem placeFlatFields_mono (curOffset : Nat) (fields : List FlatFieldSpec) :
    curOffset ≤ (placeFlatFields curOffset fields).2 := by
  induction fields generalizing curOffset with
  | nil => exact Nat.le_refl _
  | cons f rest ih =>
    dsimp [placeFlatFields]
    have hAlign := ih (alignUp curOffset f.alignment + f.size)
    have hPad : curOffset ≤ alignUp curOffset f.alignment := by
      dsimp [alignUp]; omega
    omega

private theorem placeFlatFields_fields_valid (curOffset : Nat) (fields : List FlatFieldSpec)
    {p : FieldPlacement} (hp : p ∈ (placeFlatFields curOffset fields).1) :
    0 < p.size ∧ 0 < p.alignment ∧ p.offset % p.alignment = 0 ∧
    curOffset ≤ p.offset ∧ p.offset + p.size ≤ (placeFlatFields curOffset fields).2 := by
  induction fields generalizing curOffset with
  | nil => cases hp
  | cons f rest ih =>
    dsimp [placeFlatFields] at hp ⊢
    rcases List.mem_cons.mp hp with rfl | hpRest
    · refine ⟨f.sizePos, f.alignPos, alignUp_aligned curOffset f.alignPos, ?_, ?_⟩
      · dsimp [alignUp]; omega
      · exact placeFlatFields_mono (alignUp curOffset f.alignment + f.size) rest
    · obtain ⟨hs, ha, hmod, hlo, hhi⟩ := ih (alignUp curOffset f.alignment + f.size) hpRest
      have hPad : curOffset ≤ alignUp curOffset f.alignment := by dsimp [alignUp]; omega
      exact ⟨hs, ha, hmod, by omega, hhi⟩

private theorem placeFlatFields_pairwise_separate (curOffset : Nat) (fields : List FlatFieldSpec) :
    (placeFlatFields curOffset fields).1.Pairwise FieldPlacement.Separate := by
  induction fields generalizing curOffset with
  | nil => exact List.Pairwise.nil
  | cons f rest ih =>
    dsimp [placeFlatFields]
    apply List.Pairwise.cons _ (ih _)
    intro q hq
    obtain ⟨_, _, _, hqLo, _⟩ := placeFlatFields_fields_valid (alignUp curOffset f.alignment + f.size) rest hq
    exact Or.inl hqLo

private theorem maxFieldAlign_pos (fields : List FlatFieldSpec) : 0 < maxFieldAlign fields := by
  induction fields with
  | nil => decide
  | cons f rest ih =>
    dsimp [maxFieldAlign]
    have hf := f.alignPos
    omega

private theorem pow2_max_dvd_both {a b : Nat} (ha : a.isPowerOfTwo) (hb : b.isPowerOfTwo) :
    max a b % a = 0 ∧ max a b % b = 0 := by
  obtain ⟨ka, rfl⟩ := ha
  obtain ⟨kb, rfl⟩ := hb
  by_cases hle : ka ≤ kb
  · have hPow : 2 ^ ka ≤ 2 ^ kb := Nat.pow_le_pow_right (by decide) hle
    have hMax : max (2 ^ ka) (2 ^ kb) = 2 ^ kb := Nat.max_eq_right hPow
    rw [hMax]
    refine ⟨?_, Nat.mod_self _⟩
    have hSplit : 2 ^ kb = 2 ^ ka * 2 ^ (kb - ka) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hle]
    rw [hSplit, Nat.mul_comm, Nat.mul_mod_left]
  · have hgt : kb ≤ ka := by omega
    have hPow : 2 ^ kb ≤ 2 ^ ka := Nat.pow_le_pow_right (by decide) hgt
    have hMax : max (2 ^ ka) (2 ^ kb) = 2 ^ ka := Nat.max_eq_left hPow
    rw [hMax]
    refine ⟨Nat.mod_self _, ?_⟩
    have hSplit : 2 ^ ka = 2 ^ kb * 2 ^ (ka - kb) := by
      rw [← Nat.pow_add, Nat.add_sub_of_le hgt]
    rw [hSplit, Nat.mul_comm, Nat.mul_mod_left]

private theorem maxFieldAlign_pow2 (fields : List FlatFieldSpec) :
    (maxFieldAlign fields).isPowerOfTwo := by
  induction fields with
  | nil => exact ⟨0, rfl⟩
  | cons f rest ih =>
    dsimp [maxFieldAlign]
    obtain ⟨kf, hkf⟩ := f.alignPow2
    obtain ⟨kr, hkr⟩ := ih
    rw [hkf, hkr]
    by_cases hle : kf ≤ kr
    · rw [Nat.max_eq_right (Nat.pow_le_pow_right (by decide) hle)]
      exact ⟨kr, rfl⟩
    · rw [Nat.max_eq_left (Nat.pow_le_pow_right (by decide) (by omega))]
      exact ⟨kf, rfl⟩

private theorem maxFieldAlign_dvd_placed (curOffset : Nat) (fields : List FlatFieldSpec)
    {p : FieldPlacement} (hp : p ∈ (placeFlatFields curOffset fields).1) :
    maxFieldAlign fields % p.alignment = 0 := by
  induction fields generalizing curOffset with
  | nil => cases hp
  | cons f rest ih =>
    dsimp [placeFlatFields, maxFieldAlign] at hp ⊢
    rcases List.mem_cons.mp hp with rfl | hpRest
    · exact (pow2_max_dvd_both f.alignPow2 (maxFieldAlign_pow2 rest)).1
    · have hRestDvd : maxFieldAlign rest % p.alignment = 0 := ih _ hpRest
      have hMaxDvd := (pow2_max_dvd_both f.alignPow2 (maxFieldAlign_pow2 rest)).2
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hRestDvd) (Nat.dvd_of_mod_eq_zero hMaxDvd))

theorem planFlatStruct_valid (fields : List FlatFieldSpec) :
    (planFlatStruct fields).Valid := by
  dsimp [planFlatStruct, RecordLayout.Valid]
  refine ⟨maxFieldAlign_pos fields, alignUp_aligned _ (maxFieldAlign_pos fields), ?_, ?_⟩
  · intro p hp
    obtain ⟨hs, ha, hmod, _, hhi⟩ := placeFlatFields_fields_valid 0 fields hp
    have hEndLe : (placeFlatFields 0 fields).2 ≤ alignUp (placeFlatFields 0 fields).2 (maxFieldAlign fields) := by
      dsimp [alignUp]; omega
    exact ⟨⟨hs, ha, hmod, Nat.le_trans hhi hEndLe⟩, maxFieldAlign_dvd_placed 0 fields hp⟩
  · exact placeFlatFields_pairwise_separate 0 fields

theorem flatStruct_slice_valid (s : Core.State) (owner : OwnerId)
    (fields : List FlatFieldSpec) (len : Nat)
    (hIsz : len * (planFlatStruct fields).size ≤ isizeMax64)
    (hNonEmpty : len = 0 ∨ ∃ alloc, s.allocation owner = some alloc ∧
      0 + len * (planFlatStruct fields).size ≤ alloc.bytes.length ∧
      ∀ loc ∈ (RustSliceSpec.mk owner 0 len (planFlatStruct fields).size (planFlatStruct fields).alignment .exclusive false).locations,
        s.Available loc .exclusive none) :
    RustSliceValid s
      ⟨owner, 0, len, (planFlatStruct fields).size, (planFlatStruct fields).alignment, .exclusive, false⟩ := by
  have hLayValid := planFlatStruct_valid fields
  have hPow : (planFlatStruct fields).alignment.isPowerOfTwo = (true = true) := by
    simpa [planFlatStruct] using maxFieldAlign_pow2 fields
  exact ⟨rfl, hLayValid.1, hPow, Nat.zero_mod _, hLayValid.2.1, hIsz, hNonEmpty⟩

/-! ### Part B: Bevy-Style Split-Column SoA Query Bridge -/

structure SoAQueryField where
  fieldIdx : Nat
  mode : AccessMode
  deriving Repr, DecidableEq

def soaColumnSliceSpec (owner : OwnerId) (length elemBytes : Nat) (qf : SoAQueryField) :
    RustSliceSpec :=
  ⟨owner, qf.fieldIdx * (length * elemBytes), length, elemBytes, 1, qf.mode, false⟩

/-- A Bevy-style SoA query specification is valid iff any two queried fields with
distinct indices are compatible or equal-field readers are both shared. -/
def checkSoAQueryFields (fields : List SoAQueryField) : Bool :=
  fields.Pairwise fun a b =>
    decide (a.fieldIdx ≠ b.fieldIdx ∨ (a.mode = .shared ∧ b.mode = .shared))

def SoAQueryValid (fields : List SoAQueryField) : Prop :=
  fields.Pairwise fun a b => a.fieldIdx ≠ b.fieldIdx ∨ (a.mode = .shared ∧ b.mode = .shared)

theorem checkSoAQueryFields_correct (fields : List SoAQueryField) :
    checkSoAQueryFields fields = true ↔ SoAQueryValid fields := by
  dsimp [checkSoAQueryFields, SoAQueryValid]
  induction fields with
  | nil => simp
  | cons a rest _ =>
    simp [List.pairwise_cons]

theorem soa_column_slices_compatible {owner : OwnerId} {length elemBytes : Nat}
    {q1 q2 : SoAQueryField}
    (hCompat : q1.fieldIdx ≠ q2.fieldIdx ∨ (q1.mode = .shared ∧ q2.mode = .shared)) :
    RustSlicesCompatible
      (soaColumnSliceSpec owner length elemBytes q1)
      (soaColumnSliceSpec owner length elemBytes q2) := by
  rcases hCompat with hNe | ⟨hM1, hM2⟩
  · intro loc ha hb
    simp only [soaColumnSliceSpec, RustSliceSpec.locations, RustSliceSpec.byteLen,
      List.mem_map, List.mem_range] at ha hb
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨j, hj, hEq⟩ := hb
    have hOff : q2.fieldIdx * (length * elemBytes) + j = q1.fieldIdx * (length * elemBytes) + i :=
      congrArg ByteLocation.offset hEq
    rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
    · have hMul := Nat.mul_le_mul_right (length * elemBytes) (Nat.succ_le_of_lt hLt)
      simp only [Nat.succ_mul] at hMul
      omega
    · have hMul := Nat.mul_le_mul_right (length * elemBytes) (Nat.succ_le_of_lt hGt)
      simp only [Nat.succ_mul] at hMul
      omega
  · intro loc _ _
    simp [soaColumnSliceSpec, hM1, hM2, AccessMode.Compatible]

theorem soa_query_preserves_unqueried_columns {s : Core.State} {owner : OwnerId}
    {length fieldCount fWrite fRead : Nat} {table : Nat → Nat → UInt8}
    {i : Nat} (hi : i < length) (hfW : fWrite < fieldCount) (hfR : fRead < fieldCount)
    (hNe : fWrite ≠ fRead) (newVal : UInt8)
    (hRep : ByteCollectionRep s owner .soa length fieldCount table) :
    (s.store ⟨owner, collectionSlot .soa length fieldCount i fWrite⟩ newVal).byte
      ⟨owner, collectionSlot .soa length fieldCount i fRead⟩ = some (table i fRead) := by
  have hWriteRep := byteCollection_write_simulation (layout := .soa) trivial newVal hi hfW hRep
  have hAt := hWriteRep i hi fRead hfR
  simpa [writeByteTable, hNe.symm] using hAt

/-- Dynamic `__AethelDynSoA_<Rec>` column slice specification: each column lives in an
independently allocated, `elemAlign`-aligned heap buffer owned by `colOwner qf.fieldIdx`. -/
def dynSoAColumnSliceSpec (colOwner : Nat → OwnerId) (length elemBytes elemAlign : Nat)
    (qf : SoAQueryField) : RustSliceSpec :=
  ⟨colOwner qf.fieldIdx, 0, length, elemBytes, elemAlign, qf.mode, false⟩

theorem dynSoA_column_slices_compatible {colOwner : Nat → OwnerId}
    (hInj : ∀ a b, colOwner a = colOwner b → a = b)
    {length elemBytes elemAlign : Nat} {q1 q2 : SoAQueryField}
    (hCompat : q1.fieldIdx ≠ q2.fieldIdx ∨ (q1.mode = .shared ∧ q2.mode = .shared)) :
    RustSlicesCompatible
      (dynSoAColumnSliceSpec colOwner length elemBytes elemAlign q1)
      (dynSoAColumnSliceSpec colOwner length elemBytes elemAlign q2) := by
  rcases hCompat with hNe | ⟨hM1, hM2⟩
  · intro loc ha hb
    simp only [dynSoAColumnSliceSpec, RustSliceSpec.locations, RustSliceSpec.byteLen,
      List.mem_map, List.mem_range] at ha hb
    obtain ⟨i, _, rfl⟩ := ha
    obtain ⟨j, _, hEq⟩ := hb
    have hOwner : colOwner q2.fieldIdx = colOwner q1.fieldIdx := congrArg ByteLocation.allocation hEq
    exact absurd (hInj _ _ hOwner).symm hNe
  · intro loc _ _
    simp [dynSoAColumnSliceSpec, hM1, hM2, AccessMode.Compatible]

/-- When a dynamic SoA query checks `SoAQueryValid [q1, q2]` and `colOwner` assigns distinct
column allocations, distinct columns occupy completely disjoint byte locations, justifying
direct Rust `&mut [T]` / `&[T]` `noalias` parameter passing without runtime overlap checks. -/
theorem dynSoA_mut_noalias_disjoint {colOwner : Nat → OwnerId}
    (hInj : ∀ a b, colOwner a = colOwner b → a = b)
    {length elemBytes elemAlign : Nat} {q1 q2 : SoAQueryField}
    (hValid : SoAQueryValid [q1, q2]) (hMut : q1.mode = .exclusive) :
    ∀ loc, loc ∈ (dynSoAColumnSliceSpec colOwner length elemBytes elemAlign q1).locations →
      loc ∉ (dynSoAColumnSliceSpec colOwner length elemBytes elemAlign q2).locations := by
  have hPair : q1.fieldIdx ≠ q2.fieldIdx ∨ (q1.mode = .shared ∧ q2.mode = .shared) :=
    (List.pairwise_cons.mp hValid).1 q2 (by simp)
  have hNe : q1.fieldIdx ≠ q2.fieldIdx := by
    rcases hPair with h | ⟨hM1, _⟩
    · exact h
    · rw [hMut] at hM1; cases hM1
  intro loc ha hb
  simp only [dynSoAColumnSliceSpec, RustSliceSpec.locations, RustSliceSpec.byteLen,
    List.mem_map, List.mem_range] at ha hb
  obtain ⟨i, _, rfl⟩ := ha
  obtain ⟨j, _, hEq⟩ := hb
  have hOwner : colOwner q2.fieldIdx = colOwner q1.fieldIdx := congrArg ByteLocation.allocation hEq
  exact hNe (hInj _ _ hOwner).symm

/-! ### Part C: Zero-Copy 64-Byte AoSoA SIMD Tile Bridge -/

structure AoSoATileBridgeSpec where
  tileWidth : Nat
  fieldCount : Nat
  slotBytes : Nat
  hw : 0 < tileWidth
  hf : 0 < fieldCount
  hs : 0 < slotBytes
  hLine : tileWidth * slotBytes = 64

def aosoaTileByteOffset (spec : AoSoATileBridgeSpec) (tile field lane : Nat) : Nat :=
  (tile * (spec.fieldCount * spec.tileWidth) + field * spec.tileWidth + lane) * spec.slotBytes

theorem aosoa_tile_rust_offset_eq (spec : AoSoATileBridgeSpec)
    (tile field lane : Nat) (hLane : lane < spec.tileWidth) :
    aosoaTileByteOffset spec tile field lane =
      aosoaSlot spec.tileWidth spec.fieldCount (tile * spec.tileWidth + lane) field * spec.slotBytes := by
  have hDiv : (tile * spec.tileWidth + lane) / spec.tileWidth = tile := by
    rw [Nat.mul_comm tile spec.tileWidth, Nat.mul_add_div spec.hw,
      Nat.div_eq_of_lt hLane, Nat.add_zero]
  have hMod : (tile * spec.tileWidth + lane) % spec.tileWidth = lane := by
    rw [Nat.mul_comm tile spec.tileWidth, Nat.mul_add_mod, Nat.mod_eq_of_lt hLane]
  simp only [aosoaTileByteOffset, aosoaSlot, hDiv, hMod]

theorem aosoa_tile_64B_aligned (spec : AoSoATileBridgeSpec) (tile field : Nat) :
    aosoaTileByteOffset spec tile field 0 % 64 = 0 := by
  have hEq := aosoa_tile_rust_offset_eq spec tile field 0 spec.hw
  rw [hEq, Nat.add_zero]
  exact aosoa_tile_cache_aligned spec.tileWidth spec.fieldCount tile field spec.slotBytes spec.hLine

end Aethel.RustComplexABI
