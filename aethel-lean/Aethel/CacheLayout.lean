import Aethel.ScalarLayout
import Aethel.LayoutAlgebra
import Aethel.Representation
import Aethel.AutomaticLayout

namespace Aethel.CacheLayout

open Aethel

/-- Hardware cache-line and SIMD lane descriptor. Default matches x86-64 L1 (64 bytes). -/
structure CacheSpec where
  lineSize : Nat := 64
  simdLaneCount : Nat := 8
  linePos : 0 < lineSize := by decide
  linePow2 : lineSize.isPowerOfTwo := by decide

def withinCacheLine (lineSize offset width : Nat) : Prop :=
  0 < width → offset / lineSize = (offset + width - 1) / lineSize

private theorem mod_add_width_lt_line {lineSize offset width : Nat}
    (hW : 0 < width) (hL : 0 < lineSize) (_hLe : width ≤ lineSize)
    (hDvd : width ∣ lineSize) (hAlign : offset % width = 0) :
    offset % lineSize + width ≤ lineSize := by
  obtain ⟨k, hk⟩ := hDvd
  have hkPos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hkPos
    · simp at hk; omega
    · exact hkPos
  have hModZero : (offset % lineSize) % width = 0 := by
    rw [Nat.mod_mod_of_dvd offset ⟨k, hk⟩]
    exact hAlign
  obtain ⟨m, hm⟩ := Nat.dvd_of_mod_eq_zero hModZero
  have hmLt : m < k := by
    have hRemLt := Nat.mod_lt offset hL
    rw [hm, hk] at hRemLt
    exact (Nat.mul_lt_mul_left hW).mp hRemLt
  have hSucc : m + 1 ≤ k := hmLt
  calc
    offset % lineSize + width = width * m + width := by rw [hm]
    _ = width * (m + 1) := by rw [Nat.mul_succ]
    _ ≤ width * k := Nat.mul_le_mul_left width hSucc
    _ = lineSize := hk.symm

theorem aligned_within_cacheLine {lineSize offset width : Nat}
    (hW : 0 < width) (hL : 0 < lineSize) (hLe : width ≤ lineSize)
    (hDvd : width ∣ lineSize) (hAlign : offset % width = 0) :
    withinCacheLine lineSize offset width := by
  intro _
  have hFits : offset % lineSize + (width - 1) < lineSize := by
    have hBound := mod_add_width_lt_line hW hL hLe hDvd hAlign
    omega
  have hDecomp : offset + width - 1 = (offset / lineSize) * lineSize + (offset % lineSize + (width - 1)) := by
    have hDivMod := Nat.div_add_mod offset lineSize
    rw [Nat.mul_comm lineSize (offset / lineSize)] at hDivMod
    omega
  rw [hDecomp, Nat.mul_comm (offset / lineSize) lineSize, Nat.mul_add_div hL,
    Nat.div_eq_of_lt hFits, Nat.add_zero]

/-- Tiled Array-of-Structures-of-Arrays (AoSoA) slot addressing: groups
`tileWidth` elements per field contiguously before advancing to the next field,
aligning SIMD vector loads cleanly to L1 cache lines. -/
def aosoaSlot (tileWidth fieldCount element field : Nat) : Nat :=
  (element / tileWidth) * (fieldCount * tileWidth) + field * tileWidth + (element % tileWidth)

def encodeAoSoA (table : ScalarTable) (tileWidth fieldCount : Nat) : SlotStore :=
  fun address =>
    let tileSize := fieldCount * tileWidth
    let tile := address / tileSize
    let rem := address % tileSize
    let field := rem / tileWidth
    let lane := rem % tileWidth
    table (tile * tileWidth + lane) field

private theorem inner_offset_lt {tileWidth fieldCount field lane : Nat}
    (hf : field < fieldCount) (hl : lane < tileWidth) :
    field * tileWidth + lane < fieldCount * tileWidth := by
  have hSucc : field + 1 ≤ fieldCount := hf
  calc
    field * tileWidth + lane < field * tileWidth + tileWidth := by omega
    _ = (field + 1) * tileWidth := by rw [Nat.succ_mul]
    _ ≤ fieldCount * tileWidth := Nat.mul_le_mul_right tileWidth hSucc

theorem aosoa_read (table : ScalarTable) (tileWidth fieldCount element field : Nat)
    (hw : 0 < tileWidth) (hf : field < fieldCount) :
    encodeAoSoA table tileWidth fieldCount (aosoaSlot tileWidth fieldCount element field) =
      table element field := by
  have hTilePos : 0 < fieldCount * tileWidth := Nat.mul_pos (Nat.zero_lt_of_lt hf) hw
  have hLaneLt : element % tileWidth < tileWidth := Nat.mod_lt element hw
  have hRemLt : field * tileWidth + element % tileWidth < fieldCount * tileWidth :=
    inner_offset_lt hf hLaneLt
  have hAssoc : aosoaSlot tileWidth fieldCount element field =
      (fieldCount * tileWidth) * (element / tileWidth) + (field * tileWidth + element % tileWidth) := by
    simp only [aosoaSlot, Nat.mul_comm (element / tileWidth), Nat.add_assoc]
  have hDiv : aosoaSlot tileWidth fieldCount element field / (fieldCount * tileWidth) =
      element / tileWidth := by
    rw [hAssoc, Nat.mul_add_div hTilePos, Nat.div_eq_of_lt hRemLt, Nat.add_zero]
  have hMod : aosoaSlot tileWidth fieldCount element field % (fieldCount * tileWidth) =
      field * tileWidth + element % tileWidth := by
    rw [hAssoc, Nat.mul_add_mod, Nat.mod_eq_of_lt hRemLt]
  have hField : (field * tileWidth + element % tileWidth) / tileWidth = field := by
    rw [Nat.mul_comm field tileWidth, Nat.mul_add_div hw, Nat.div_eq_of_lt hLaneLt, Nat.add_zero]
  have hLane : (field * tileWidth + element % tileWidth) % tileWidth = element % tileWidth := by
    rw [Nat.mul_comm field tileWidth, Nat.mul_add_mod, Nat.mod_eq_of_lt hLaneLt]
  have hElem : (element / tileWidth) * tileWidth + element % tileWidth = element := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod element tileWidth
  simp only [encodeAoSoA, hDiv, hMod, hField, hLane, hElem]

theorem three_way_read_agreement (table : ScalarTable)
    (length tileWidth fieldCount element field : Nat)
    (hi : element < length) (hw : 0 < tileWidth) (hf : field < fieldCount) :
    encodeAoS table fieldCount (aosSlot fieldCount element field) = table element field ∧
    encodeSoA table length (soaSlot length element field) = table element field ∧
    encodeAoSoA table tileWidth fieldCount (aosoaSlot tileWidth fieldCount element field) =
      table element field :=
  ⟨aos_read table fieldCount element field hf,
   soa_read table length element field hi,
   aosoa_read table tileWidth fieldCount element field hw hf⟩

theorem aosoaSlot_eq_iff (tileWidth fieldCount i j f g : Nat)
    (hw : 0 < tileWidth) (hf : f < fieldCount) (hg : g < fieldCount) :
    aosoaSlot tileWidth fieldCount i f = aosoaSlot tileWidth fieldCount j g ↔ i = j ∧ f = g := by
  constructor
  · intro h
    have hRow := congrArg (encodeAoSoA (fun row _ => row) tileWidth fieldCount) h
    have hCol := congrArg (encodeAoSoA (fun _ col => col) tileWidth fieldCount) h
    simp only [aosoa_read _ _ _ _ _ hw hf, aosoa_read _ _ _ _ _ hw hg] at hRow hCol
    exact ⟨hRow, hCol⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem aosoa_write_observation (table : ScalarTable) (tileWidth fieldCount i j f g value : Nat)
    (hw : 0 < tileWidth) (hf : f < fieldCount) (hg : g < fieldCount) :
    writeSlot (encodeAoSoA table tileWidth fieldCount) (aosoaSlot tileWidth fieldCount i f) value
      (aosoaSlot tileWidth fieldCount j g) = writeTable table i f value j g := by
  simp [writeSlot, writeTable, aosoaSlot_eq_iff _ _ _ _ _ _ hw hg hf, aosoa_read _ _ _ _ _ hw hg]

def ScalarRepAoSoA (table : ScalarTable) (store : SlotStore)
    (length tileWidth fieldCount : Nat) : Prop :=
  ∀ i, i < length → ∀ f, f < fieldCount →
    store (aosoaSlot tileWidth fieldCount i f) = table i f

theorem scalarRepAoSoA_init (table : ScalarTable) (length tileWidth fieldCount : Nat)
    (hw : 0 < tileWidth) :
    ScalarRepAoSoA table (encodeAoSoA table tileWidth fieldCount) length tileWidth fieldCount :=
  fun _ _ _ hf => aosoa_read table tileWidth fieldCount _ _ hw hf

theorem scalarRepAoSoA_write {table : ScalarTable} {store : SlotStore}
    {length tileWidth fieldCount : Nat}
    (hrep : ScalarRepAoSoA table store length tileWidth fieldCount)
    (i f value : Nat) (_hi : i < length) (hw : 0 < tileWidth) (hf : f < fieldCount) :
    ScalarRepAoSoA (writeTable table i f value)
      (writeSlot store (aosoaSlot tileWidth fieldCount i f) value) length tileWidth fieldCount := by
  intro j hj g hg
  simp [writeSlot, writeTable, aosoaSlot_eq_iff _ _ _ _ _ _ hw hg hf, hrep j hj g hg]

theorem three_way_write_refinement {table : ScalarTable} {aos soa aosoa : SlotStore}
    {length tileWidth fieldCount : Nat}
    (ha : ScalarRepAoS table aos length fieldCount)
    (hs : ScalarRepSoA table soa length fieldCount)
    (ht : ScalarRepAoSoA table aosoa length tileWidth fieldCount)
    (i f value : Nat) (hi : i < length) (hw : 0 < tileWidth) (hf : f < fieldCount) :
    ScalarRepAoS (writeTable table i f value)
      (writeSlot aos (aosSlot fieldCount i f) value) length fieldCount ∧
    ScalarRepSoA (writeTable table i f value)
      (writeSlot soa (soaSlot length i f) value) length fieldCount ∧
    ScalarRepAoSoA (writeTable table i f value)
      (writeSlot aosoa (aosoaSlot tileWidth fieldCount i f) value) length tileWidth fieldCount :=
  ⟨scalarRepAoS_write ha i f value hi hf,
   scalarRepSoA_write hs i f value hi hf,
   scalarRepAoSoA_write ht i f value hi hw hf⟩

theorem aosoa_tile_contiguous (tileWidth fieldCount element field : Nat)
    (hw : 0 < tileWidth) (hSameTile : element % tileWidth + 1 < tileWidth) :
    aosoaSlot tileWidth fieldCount (element + 1) field =
      aosoaSlot tileWidth fieldCount element field + 1 := by
  have hDecomp : element + 1 = tileWidth * (element / tileWidth) + (element % tileWidth + 1) := by
    have := Nat.div_add_mod element tileWidth
    omega
  have hDiv : (element + 1) / tileWidth = element / tileWidth := by
    rw [hDecomp, Nat.mul_add_div hw, Nat.div_eq_of_lt hSameTile, Nat.add_zero]
  have hMod : (element + 1) % tileWidth = element % tileWidth + 1 := by
    rw [hDecomp, Nat.mul_add_mod, Nat.mod_eq_of_lt hSameTile]
  simp only [aosoaSlot, hDiv, hMod]
  omega

theorem aosoa_tile_cache_aligned (tileWidth fieldCount tile field slotBytes : Nat)
    (hLine : tileWidth * slotBytes = 64) :
    (aosoaSlot tileWidth fieldCount (tile * tileWidth) field * slotBytes) % 64 = 0 := by
  have hw : 0 < tileWidth := by
    rcases Nat.eq_zero_or_pos tileWidth with rfl | hPos
    · simp at hLine
    · exact hPos
  have hDiv : (tile * tileWidth) / tileWidth = tile := Nat.mul_div_cancel tile hw
  have hMod : (tile * tileWidth) % tileWidth = 0 := Nat.mul_mod_left tile tileWidth
  simp only [aosoaSlot, hDiv, hMod, Nat.add_zero]
  have hFactor : (tile * (fieldCount * tileWidth) + field * tileWidth) * slotBytes =
      (tile * fieldCount + field) * (tileWidth * slotBytes) := by
    simp only [Nat.add_mul, Nat.mul_assoc]
  rw [hFactor, hLine]
  exact Nat.mul_mod_left _ 64

/-- Collection representation variants including Tiled AoSoA. -/
inductive CollectionLayout where
  | aos
  | soa
  | aosoa (tileWidth : Nat)
  deriving Repr, DecidableEq

def CollectionLayout.Valid : CollectionLayout → Prop
  | .aos => True
  | .soa => True
  | .aosoa w => 0 < w

def collectionSlot (layout : CollectionLayout) (length fieldCount element field : Nat) : Nat :=
  match layout with
  | .aos => aosSlot fieldCount element field
  | .soa => soaSlot length element field
  | .aosoa w => aosoaSlot w fieldCount element field

theorem collectionSlot_eq_iff {layout : CollectionLayout} (hValid : layout.Valid)
    {length fieldCount i j f g : Nat}
    (hi : i < length) (hj : j < length) (hf : f < fieldCount) (hg : g < fieldCount) :
    collectionSlot layout length fieldCount i f =
      collectionSlot layout length fieldCount j g ↔ i = j ∧ f = g := by
  cases layout with
  | aos => exact aosSlot_eq_iff fieldCount i j f g hf hg
  | soa => exact soaSlot_eq_iff length i j f g hi hj
  | aosoa w => exact aosoaSlot_eq_iff w fieldCount i j f g hValid hf hg

/-- Byte-level physical collection representation in `Core.State` unified across
AoS, SoA, and Tiled AoSoA layouts. -/
def ByteCollectionRep (s : Core.State) (owner : Core.OwnerId) (layout : CollectionLayout)
    (length fieldCount : Nat) (table : Nat → Nat → UInt8) : Prop :=
  ∀ i, i < length → ∀ f, f < fieldCount →
    s.byte ⟨owner, collectionSlot layout length fieldCount i f⟩ = some (table i f)

def writeByteTable (table : Nat → Nat → UInt8) (element field : Nat) (val : UInt8) :
    Nat → Nat → UInt8 :=
  fun i f => if i = element ∧ f = field then val else table i f

theorem byteCollection_write_simulation {s : Core.State} {owner : Core.OwnerId}
    {layout : CollectionLayout} (hValid : layout.Valid)
    {length fieldCount i f : Nat} {table : Nat → Nat → UInt8} (newVal : UInt8)
    (hi : i < length) (hf : f < fieldCount)
    (hRep : ByteCollectionRep s owner layout length fieldCount table) :
    ByteCollectionRep
      (s.store ⟨owner, collectionSlot layout length fieldCount i f⟩ newVal)
      owner layout length fieldCount (writeByteTable table i f newVal) := by
  intro j hj g hg
  by_cases hEq : j = i ∧ g = f
  · obtain ⟨rfl, rfl⟩ := hEq
    simp only [writeByteTable, and_self, ite_true]
    exact Core.State.store_byte_written s ⟨owner, collectionSlot layout length fieldCount j g⟩
      (table j g) newVal (hRep j hj g hg)
  · have hNot : ¬ (j = i ∧ g = f) := hEq
    simp only [writeByteTable, ite_eq_right hNot]
    have hSlotNe : collectionSlot layout length fieldCount i f ≠
        collectionSlot layout length fieldCount j g := by
      intro hSlotEq
      have hSame := (collectionSlot_eq_iff hValid hi hj hf hg).mp hSlotEq
      exact hNot ⟨hSame.1.symm, hSame.2.symm⟩
    have hLocNe : (⟨owner, collectionSlot layout length fieldCount i f⟩ : ByteLocation) ≠
        ⟨owner, collectionSlot layout length fieldCount j g⟩ := by
      intro hLocEq
      exact hSlotNe (congrArg ByteLocation.offset hLocEq)
    rw [Core.State.store_byte_other s _ _ newVal hLocNe]
    exact hRep j hj g hg

theorem byteCollection_write_preserves_other_owner {s : Core.State}
    {written : ByteLocation} {newVal : UInt8}
    {other : Core.OwnerId} {layout : CollectionLayout} {length fieldCount : Nat}
    {table : Nat → Nat → UInt8}
    (hNe : other ≠ written.allocation)
    (hRep : ByteCollectionRep s other layout length fieldCount table) :
    ByteCollectionRep (s.store written newVal) other layout length fieldCount table := by
  intro j hj g hg
  have hLocNe : written ≠ ⟨other, collectionSlot layout length fieldCount j g⟩ := by
    intro hEq
    exact hNe (congrArg ByteLocation.allocation hEq).symm
  rw [Core.State.store_byte_other s written _ newVal hLocNe]
  exact hRep j hj g hg

/-- Profitability profile used to pick AoS, SoA, or Tiled AoSoA for an allocation site. -/
structure LoopAccessProfile where
  totalFields : Nat
  hotFieldCount : Nat
  elementCount : Nat
  simdPreferred : Bool
  elemFieldBytes : Nat
  deriving Repr, DecidableEq

def selectCollectionLayout (p : LoopAccessProfile) : CollectionLayout :=
  if p.elementCount ≤ 8 ∨ p.hotFieldCount == p.totalFields && !p.simdPreferred then
    .aos
  else if p.simdPreferred && 0 < p.elemFieldBytes && p.elemFieldBytes ≤ 64 then
    let lanes := max 1 (64 / p.elemFieldBytes)
    .aosoa lanes
  else
    .soa

theorem selectCollectionLayout_valid (p : LoopAccessProfile) :
    (selectCollectionLayout p).Valid := by
  unfold selectCollectionLayout
  split
  · exact trivial
  · split
    · dsimp [CollectionLayout.Valid]
      omega
    · exact trivial

/-- Hot/cold field clustering: places frequently co-accessed fields first so
hot fields stay packed inside the leading 64-byte L1 cache line. -/
def reorderHotFirst (isHot : α → Bool) (fields : List α) : List α :=
  fields.filter isHot ++ fields.filter (fun x => !isHot x)

theorem reorderHotFirst_length (isHot : α → Bool) (fields : List α) :
    (reorderHotFirst isHot fields).length = fields.length := by
  induction fields with
  | nil => rfl
  | cons x xs ih =>
    cases hx : isHot x <;> simp [reorderHotFirst, hx] at ih ⊢ <;> omega

theorem reorderHotFirst_mem_iff (isHot : α → Bool) (fields : List α) (x : α) :
    x ∈ reorderHotFirst isHot fields ↔ x ∈ fields := by
  simp only [reorderHotFirst, List.mem_append, List.mem_filter]
  constructor
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · intro hx
    cases hHot : isHot x
    · right; exact ⟨hx, by simp⟩
    · left; exact ⟨hx, rfl⟩

/-! ## Tiled SIMD + Scalar Tail Equivalence (`@layout(aosoa(W))` Lowering Refinement) -/

def applyElemField (owner : Core.OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) (f : UInt8 → UInt8)
    (s : Core.State) (i : Nat) : Core.State :=
  let loc : ByteLocation := ⟨owner, collectionSlot layout length fieldCount i field⟩
  match s.byte loc with
  | some b => s.store loc (f b)
  | none => s

def applyRange (owner : Core.OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) (f : UInt8 → UInt8)
    (start : Nat) : Nat → Core.State → Core.State
  | 0, s => s
  | count + 1, s =>
    let mid := applyElemField owner layout length fieldCount field f s start
    applyRange owner layout length fieldCount field f (start + 1) count mid

def applyFullTiles (owner : Core.OwnerId) (layout : CollectionLayout)
    (length fieldCount tileWidth field : Nat) (f : UInt8 → UInt8) :
    Nat → Core.State → Core.State
  | 0, s => s
  | tiles + 1, s =>
    let mid := applyFullTiles owner layout length fieldCount tileWidth field f tiles s
    applyRange owner layout length fieldCount field f (tiles * tileWidth) tileWidth mid

/-- Two-phase lowering used by `@layout(aosoa(W))`: executes `length / tileWidth`
vectorized `tileWidth`-lane tiles followed by the `length % tileWidth` scalar tail. -/
def applyTiledSimdPass (owner : Core.OwnerId) (layout : CollectionLayout)
    (length fieldCount tileWidth field : Nat) (f : UInt8 → UInt8)
    (s : Core.State) : Core.State :=
  let tiles := length / tileWidth
  let tailStart := tiles * tileWidth
  let mid := applyFullTiles owner layout length fieldCount tileWidth field f tiles s
  applyRange owner layout length fieldCount field f tailStart (length % tileWidth) mid

theorem applyRange_append (owner : Core.OwnerId) (layout : CollectionLayout)
    (length fieldCount field : Nat) (f : UInt8 → UInt8)
    (start n m : Nat) (s : Core.State) :
    applyRange owner layout length fieldCount field f (start + n) m
      (applyRange owner layout length fieldCount field f start n s) =
    applyRange owner layout length fieldCount field f start (n + m) s := by
  induction n generalizing start s with
  | zero =>
    simp [applyRange]
  | succ n ih =>
    have hEq : start + (n + 1) = (start + 1) + n := by omega
    have hSum : n + 1 + m = (n + m) + 1 := by omega
    rw [hEq, hSum]
    dsimp [applyRange]
    exact ih (start + 1) (applyElemField owner layout length fieldCount field f s start)

theorem applyFullTiles_eq_applyRange (owner : Core.OwnerId) (layout : CollectionLayout)
    (length fieldCount tileWidth field : Nat) (f : UInt8 → UInt8)
    (tiles : Nat) (s : Core.State) :
    applyFullTiles owner layout length fieldCount tileWidth field f tiles s =
    applyRange owner layout length fieldCount field f 0 (tiles * tileWidth) s := by
  induction tiles with
  | zero =>
    simp [applyFullTiles, applyRange]
  | succ tiles ih =>
    dsimp [applyFullTiles]
    rw [ih]
    have hZero : 0 + tiles * tileWidth = tiles * tileWidth := Nat.zero_add _
    have hMul : (tiles + 1) * tileWidth = tiles * tileWidth + tileWidth := Nat.succ_mul _ _
    rw [hMul]
    simpa [hZero] using
      applyRange_append owner layout length fieldCount field f 0 (tiles * tileWidth) tileWidth s

theorem applyTiledSimdPass_eq_applyRange (owner : Core.OwnerId) (layout : CollectionLayout)
    (length fieldCount tileWidth field : Nat) (f : UInt8 → UInt8) (s : Core.State) :
    applyTiledSimdPass owner layout length fieldCount tileWidth field f s =
    applyRange owner layout length fieldCount field f 0 length s := by
  dsimp [applyTiledSimdPass]
  rw [applyFullTiles_eq_applyRange]
  have hZero : 0 + (length / tileWidth) * tileWidth = (length / tileWidth) * tileWidth := Nat.zero_add _
  have hDivMod : (length / tileWidth) * tileWidth + length % tileWidth = length := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod length tileWidth
  have hApp := applyRange_append owner layout length fieldCount field f
    0 ((length / tileWidth) * tileWidth) (length % tileWidth) s
  rw [hZero] at hApp
  rw [hApp, hDivMod]

theorem applyElemField_rep {owner : Core.OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount field : Nat}
    (hField : field < fieldCount) (f : UInt8 → UInt8)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner layout length fieldCount table)
    {k : Nat} (hk : k < length) :
    ByteCollectionRep (applyElemField owner layout length fieldCount field f s k)
      owner layout length fieldCount
      (fun i g => if i = k ∧ g = field then f (table i g) else table i g) := by
  dsimp [applyElemField]
  rw [hRep k hk field hField]
  intro j hj g hg
  by_cases hEq : j = k ∧ g = field
  · obtain ⟨rfl, rfl⟩ := hEq
    simp only [and_self, ↓reduceIte]
    exact Core.State.store_byte_written s ⟨owner, collectionSlot layout length fieldCount j g⟩
      (table j g) (f (table j g)) (hRep j hj g hg)
  · have hNot : ¬ (j = k ∧ g = field) := hEq
    simp only [ite_eq_right hNot]
    have hSlotNe : collectionSlot layout length fieldCount k field ≠
        collectionSlot layout length fieldCount j g := by
      intro hSlotEq
      have hSame := (collectionSlot_eq_iff hValid hk hj hField hg).mp hSlotEq
      exact hNot ⟨hSame.1.symm, hSame.2.symm⟩
    have hLocNe : (⟨owner, collectionSlot layout length fieldCount k field⟩ : ByteLocation) ≠
        ⟨owner, collectionSlot layout length fieldCount j g⟩ := by
      intro hLocEq
      exact hSlotNe (congrArg ByteLocation.offset hLocEq)
    rw [Core.State.store_byte_other s _ _ (f (table k field)) hLocNe]
    exact hRep j hj g hg

theorem applyRange_rep {owner : Core.OwnerId} {layout : CollectionLayout}
    (hValid : layout.Valid) {length fieldCount field : Nat}
    (hField : field < fieldCount) (f : UInt8 → UInt8)
    (start count : Nat) (hBound : start + count ≤ length)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner layout length fieldCount table) :
    ByteCollectionRep (applyRange owner layout length fieldCount field f start count s)
      owner layout length fieldCount
      (fun i g => if start ≤ i ∧ i < start + count ∧ g = field then f (table i g) else table i g) := by
  induction count generalizing start s table with
  | zero =>
    intro i hi g hg
    have hFalse : ¬ (start ≤ i ∧ i < start + 0 ∧ g = field) := by omega
    simp only [hFalse, ↓reduceIte]
    exact hRep i hi g hg
  | succ count ih =>
    have hStartLt : start < length := by omega
    have hStepRep := applyElemField_rep hValid hField f hRep hStartLt
    have hRestRep := ih (start + 1) (by omega) hStepRep
    intro i hi g hg
    have hAt := hRestRep i hi g hg
    dsimp [applyRange]
    rw [hAt]
    congr 1
    dsimp only
    by_cases hIsStart : i = start ∧ g = field
    · have hNotTail : ¬ (start + 1 ≤ i ∧ i < start + 1 + count ∧ g = field) := by omega
      have hInFull : start ≤ i ∧ i < start + (count + 1) ∧ g = field := by omega
      rw [ite_eq_right hNotTail, ite_eq_left hIsStart, ite_eq_left hInFull]
    · by_cases hInTail : start + 1 ≤ i ∧ i < start + 1 + count ∧ g = field
      · have hInFull : start ≤ i ∧ i < start + (count + 1) ∧ g = field := by omega
        rw [ite_eq_left hInTail, ite_eq_right hIsStart, ite_eq_left hInFull]
      · have hNotFull : ¬ (start ≤ i ∧ i < start + (count + 1) ∧ g = field) := by omega
        rw [ite_eq_right hInTail, ite_eq_right hIsStart, ite_eq_right hNotFull]

/-- Tiled AoSoA SIMD execution + scalar tail refines exact element-wise
physical collection representation identically across every element and field. -/
theorem aosoa_simd_tile_step_refines {owner : Core.OwnerId} {w length fieldCount field : Nat}
    (hw : 0 < w) (hField : field < fieldCount) (f : UInt8 → UInt8)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner (.aosoa w) length fieldCount table) :
    ByteCollectionRep
      (applyTiledSimdPass owner (.aosoa w) length fieldCount w field f s)
      owner (.aosoa w) length fieldCount
      (fun i g => if g = field then f (table i g) else table i g) := by
  rw [applyTiledSimdPass_eq_applyRange]
  have hRng := applyRange_rep (layout := .aosoa w) hw hField f 0 length (by omega) hRep
  intro i hi g hg
  have hCell := hRng i hi g hg
  rw [hCell]
  congr 1
  dsimp only
  have hBound : 0 ≤ i ∧ i < 0 + length := ⟨Nat.zero_le _, by omega⟩
  by_cases hgEq : g = field
  · have hAll : 0 ≤ i ∧ i < 0 + length ∧ g = field := ⟨hBound.1, hBound.2, hgEq⟩
    rw [ite_eq_left hAll, ite_eq_left hgEq]
  · have hNot : ¬ (0 ≤ i ∧ i < 0 + length ∧ g = field) := fun h => hgEq h.2.2
    rw [ite_eq_right hNot, ite_eq_right hgEq]

/-- Native `.soa` `@Vector(w, T)` SIMD + scalar tail execution refines exact element-wise
physical column representation identically across every element and preserves unqueried columns. -/
theorem soa_simd_tile_step_refines {owner : Core.OwnerId} {w length fieldCount field : Nat}
    (_hw : 0 < w) (hField : field < fieldCount) (f : UInt8 → UInt8)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner .soa length fieldCount table) :
    ByteCollectionRep
      (applyTiledSimdPass owner .soa length fieldCount w field f s)
      owner .soa length fieldCount
      (fun i g => if g = field then f (table i g) else table i g) := by
  rw [applyTiledSimdPass_eq_applyRange]
  have hRng := applyRange_rep (layout := .soa) trivial hField f 0 length (by omega) hRep
  intro i hi g hg
  have hCell := hRng i hi g hg
  rw [hCell]
  congr 1
  dsimp only
  have hBound : 0 ≤ i ∧ i < 0 + length := ⟨Nat.zero_le _, by omega⟩
  by_cases hgEq : g = field
  · have hAll : 0 ≤ i ∧ i < 0 + length ∧ g = field := ⟨hBound.1, hBound.2, hgEq⟩
    rw [ite_eq_left hAll, ite_eq_left hgEq]
  · have hNot : ¬ (0 ≤ i ∧ i < 0 + length ∧ g = field) := fun h => hgEq h.2.2
    rw [ite_eq_right hNot, ite_eq_right hgEq]

/-- Writing back a full row snapshot `writeAllColumnsUpTo` after an interleaved write to column `1`
clobbers column `1` back to `snap 1` instead of preserving `newCold` (demonstrating why selective
column writes are required to uphold `CategoricalFusion` and `ScopedForkJoin` frame guarantees). -/
def writeAllColumnsUpTo (owner : Core.OwnerId) (layout : CollectionLayout)
    (length fieldCount idx : Nat) (row : Nat → UInt8) (s : Core.State) : Nat → Core.State
  | 0 => s
  | g + 1 =>
    (writeAllColumnsUpTo owner layout length fieldCount idx row s g).store
      ⟨owner, collectionSlot layout length fieldCount idx g⟩ (row g)

theorem whole_record_set_clobbers_sibling_counterexample {owner : Core.OwnerId}
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner .soa 1 2 table)
    (newHot newCold : UInt8) :
    let loc1 : ByteLocation := ⟨owner, collectionSlot .soa 1 2 0 1⟩
    let s1 := s.store loc1 newCold
    let snap := fun g => if g = 0 then newHot else table 0 g
    (writeAllColumnsUpTo owner .soa 1 2 0 snap s1 2).byte loc1 = some (table 0 1) := by
  intro loc1 s1 snap
  let loc0 : ByteLocation := ⟨owner, collectionSlot .soa 1 2 0 0⟩
  have hAt1 : s.byte loc1 = some (table 0 1) := hRep 0 (by decide) 1 (by decide)
  have hNeLoc : loc0 ≠ loc1 := by
    intro hEq
    have hSlot := congrArg ByteLocation.offset hEq
    have hSame := (collectionSlot_eq_iff (layout := .soa) (length := 1) (fieldCount := 2)
      trivial (by decide) (by decide) (by decide) (by decide)).mp hSlot
    exact absurd hSame.2 (by decide)
  have hS1Has1 : s1.byte loc1 = some newCold :=
    Core.State.store_byte_written s loc1 (table 0 1) newCold hAt1
  have hStep0 : (s1.store loc0 (snap 0)).byte loc1 = some newCold := by
    rw [Core.State.store_byte_other s1 loc0 loc1 (snap 0) hNeLoc]
    exact hS1Has1
  dsimp [writeAllColumnsUpTo]
  simpa [snap, loc1] using
    Core.State.store_byte_written (s1.store loc0 (snap 0)) loc1 newCold (table 0 1) hStep0

/-- Branchless `@select` SIMD predication (`if pred v then fThen v else fElse v`) refines exact
element-wise conditional field updates over `.soa` while preserving all unqueried columns. -/
theorem soa_simd_select_step_refines {owner : Core.OwnerId} {w length fieldCount field : Nat}
    (hw : 0 < w) (hField : field < fieldCount)
    (pred : UInt8 → Bool) (fThen fElse : UInt8 → UInt8)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner .soa length fieldCount table) :
    ByteCollectionRep
      (applyTiledSimdPass owner .soa length fieldCount w field
        (fun v => if pred v then fThen v else fElse v) s)
      owner .soa length fieldCount
      (fun i g =>
        if g = field then (if pred (table i g) then fThen (table i g) else fElse (table i g))
        else table i g) :=
  soa_simd_tile_step_refines hw hField (fun v => if pred v then fThen v else fElse v) hRep

/-- Branchless `@select` SIMD predication over 64B-aligned `.aosoa w` tiles refines exact
element-wise conditional field updates while preserving all unqueried columns. -/
theorem aosoa_simd_select_step_refines {owner : Core.OwnerId} {w length fieldCount field : Nat}
    (hw : 0 < w) (hField : field < fieldCount)
    (pred : UInt8 → Bool) (fThen fElse : UInt8 → UInt8)
    {s : Core.State} {table : Nat → Nat → UInt8}
    (hRep : ByteCollectionRep s owner (.aosoa w) length fieldCount table) :
    ByteCollectionRep
      (applyTiledSimdPass owner (.aosoa w) length fieldCount w field
        (fun v => if pred v then fThen v else fElse v) s)
      owner (.aosoa w) length fieldCount
      (fun i g =>
        if g = field then (if pred (table i g) then fThen (table i g) else fElse (table i g))
        else table i g) :=
  aosoa_simd_tile_step_refines hw hField (fun v => if pred v then fThen v else fElse v) hRep

/-- Associative wrapping/natural addition fold over a contiguous index range `[start, start+count)`. -/
def sumRange (vals : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange vals start n + vals (start + n)

def sumTiles (vals : Nat → Nat) (w : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => sumTiles vals w t + sumRange vals (t * w) w

theorem sumRange_append (vals : Nat → Nat) (start n m : Nat) :
    sumRange vals start (n + m) = sumRange vals start n + sumRange vals (start + n) m := by
  induction m with
  | zero => simp [sumRange]
  | succ m ih =>
    have hAssoc : start + (n + m) = (start + n) + m := by omega
    dsimp [sumRange]
    rw [ih, hAssoc, Nat.add_assoc]

theorem sumTiles_eq_sumRange (vals : Nat → Nat) (w tiles : Nat) :
    sumTiles vals w tiles = sumRange vals 0 (tiles * w) := by
  induction tiles with
  | zero => simp [sumTiles, sumRange]
  | succ t ih =>
    dsimp [sumTiles]
    rw [ih]
    have hMul : (t + 1) * w = t * w + w := Nat.succ_mul _ _
    have hZ : 0 + t * w = t * w := Nat.zero_add _
    rw [hMul, sumRange_append, hZ]

/-- Accumulating `w`-wide SIMD lane sums (`sumTiles`) plus scalar tail equals the sequential `fold`. -/
theorem simd_tiled_sum_eq_sequential_fold (vals : Nat → Nat) (w length : Nat) :
    sumTiles vals w (length / w) + sumRange vals ((length / w) * w) (length % w) =
      sumRange vals 0 length := by
  rw [sumTiles_eq_sumRange]
  have hZ : 0 + (length / w) * w = (length / w) * w := Nat.zero_add _
  have hApp := sumRange_append vals 0 ((length / w) * w) (length % w)
  rw [hZ] at hApp
  rw [← hApp]
  have hDivMod : (length / w) * w + length % w = length := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod length w
  rw [hDivMod]

/-- Default x86-64 L1 data cache capacity (32 KiB) for `@layout(auto)` sub-byte packing decisions. -/
def l1DataCacheBytes : Nat := 32768

def selectSubBytePolicy (hasConflict isHot : Bool) (workingSetBytes : Nat) :
    AutomaticLayout.StoragePolicy :=
  if hasConflict || (isHot && decide (workingSetBytes ≤ l1DataCacheBytes)) then .addressable
  else .mayShareByte

theorem selectSubBytePolicy_conflict_addressable (isHot : Bool) (workingSetBytes : Nat) :
    selectSubBytePolicy true isHot workingSetBytes = .addressable := by
  simp [selectSubBytePolicy]

theorem selectSubBytePolicy_hot_l1_addressable (hasConflict : Bool) {workingSetBytes : Nat}
    (hL1 : workingSetBytes ≤ l1DataCacheBytes) :
    selectSubBytePolicy hasConflict true workingSetBytes = .addressable := by
  simp [selectSubBytePolicy, decide_eq_true hL1]

theorem selectSubBytePolicy_cold_or_streaming_packs
    (hNoConflict : hasConflict = false)
    (hNotHotInL1 : isHot = false ∨ l1DataCacheBytes < workingSetBytes) :
    selectSubBytePolicy hasConflict isHot workingSetBytes = .mayShareByte := by
  rcases hNotHotInL1 with rfl | hGt
  · simp [selectSubBytePolicy, hNoConflict]
  · simp [selectSubBytePolicy, hNoConflict, Nat.not_le_of_gt hGt]

end Aethel.CacheLayout
