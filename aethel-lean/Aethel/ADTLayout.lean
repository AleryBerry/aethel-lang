import Aethel.StatusCodec
import Aethel.FunctionSummaries
import Aethel.IntegerTypes
import Aethel.LayoutAccess

namespace Aethel.ADTLayout

open Aethel AutomaticLayout

/-- Descriptor for one variant of a bit-compact algebraic data type. -/
structure VariantSpec where
  tag : Nat
  payloadBits : Nat
  deriving Repr, DecidableEq

/-- Generalized bit-packed tagged sum descriptor generalizing `StatusCodec` to
arbitrary finite non-recursive ADTs with minimal discriminant tags. -/
structure CompactADT where
  tagBits : Nat
  maxPayloadBits : Nat
  variants : List VariantSpec
  deriving Repr, DecidableEq

/-- Minimum number of binary positions needed for the given number of codes. -/
def minTagBits (count : Nat) : Nat :=
  if count ≤ 1 then 0 else (count - 1).log2 + 1

theorem minTagBits_le_iff {count bits : Nat} : minTagBits count ≤ bits ↔ count ≤ 2 ^ bits := by
  unfold minTagBits
  split
  · rename_i small
    have one := Nat.two_pow_pos bits
    omega
  · rename_i multiple
    have positive : count - 1 ≠ 0 := by omega
    rw [← Nat.lt_iff_add_one_le, Nat.log2_lt positive]
    omega

/-- A finite sum can use consecutive codes when each payload has a dense
index. The second variant starts after all possible first-variant values. -/
def denseIndex {left right : Nat} : Sum (Fin left) (Fin right) → Fin (left + right)
  | .inl value => value.castAdd right
  | .inr value => value.natAdd left

def denseVariant {left right : Nat} (code : Fin (left + right)) : Sum (Fin left) (Fin right) :=
  Fin.addCases (motive := fun _ => Sum (Fin left) (Fin right)) Sum.inl Sum.inr code

@[simp] theorem denseVariant_index {left right : Nat} (value : Sum (Fin left) (Fin right)) :
    denseVariant (denseIndex value) = value := by
  cases value <;> simp [denseIndex, denseVariant]

@[simp] theorem denseIndex_variant {left right : Nat} (code : Fin (left + right)) :
    denseIndex (denseVariant code) = code := by
  induction code using Fin.addCases with
  | left value => simp [denseIndex, denseVariant]
  | right value => simp [denseIndex, denseVariant]

def packDenseIndex (index : Fin count) : BitVec (minTagBits count) :=
  BitVec.ofNatLT index.val (Nat.lt_of_lt_of_le index.isLt (minTagBits_le_iff.mp (Nat.le_refl _)))

def unpackDenseIndex (count : Nat) (bits : BitVec (minTagBits count)) : Option (Fin count) :=
  if within : bits.toNat < count then some ⟨bits.toNat, within⟩ else none

theorem unpackDenseIndex_correct {count : Nat} {bits : BitVec (minTagBits count)} {index : Fin count} :
    unpackDenseIndex count bits = some index ↔ bits = packDenseIndex index := by
  constructor
  · intro decoded
    unfold unpackDenseIndex at decoded
    split at decoded
    · exact BitVec.eq_of_toNat_eq (congrArg (Fin.val : Fin count → Nat) (Option.some.inj decoded))
    · contradiction
  · rintro rfl
    have within : (packDenseIndex index).toNat < count := index.isLt
    rw [unpackDenseIndex, dite_eq_left within]
    rfl

def packDenseSum {left right : Nat} (value : Sum (Fin left) (Fin right)) :
    BitVec (minTagBits (left + right)) :=
  packDenseIndex (denseIndex value)

def unpackDenseSum (left right : Nat) (bits : BitVec (minTagBits (left + right))) :
    Option (Sum (Fin left) (Fin right)) :=
  (unpackDenseIndex (left + right) bits).map denseVariant

theorem unpackDenseSum_correct {left right : Nat} {bits : BitVec (minTagBits (left + right))}
    {value : Sum (Fin left) (Fin right)} :
    unpackDenseSum left right bits = some value ↔ bits = packDenseSum value := by
  rw [unpackDenseSum, Option.map_eq_some_iff]
  constructor
  · rintro ⟨index, valid, rfl⟩
    simpa only [packDenseSum, denseIndex_variant] using unpackDenseIndex_correct.mp valid
  · intro packed
    exact ⟨denseIndex value, unpackDenseIndex_correct.mpr packed, denseVariant_index value⟩

/-- Any injective fixed-width representation needs at least the width of
the consecutive encoding. -/
theorem packDenseIndex_minimum {count width : Nat}
    (encode : Fin count → BitVec width) (distinct : Function.Injective encode) :
    minTagBits count ≤ width := by
  let code (index : Fin count) := (encode index).toFin
  have codeDistinct : Function.Injective code := by
    intro a b same
    exact distinct (BitVec.eq_of_toNat_eq (congrArg Fin.val same))
  have unique : ((List.finRange count).map code).Nodup :=
    List.Pairwise.map code (fun _ _ different same => different (codeDistinct same))
    (List.nodup_finRange count)
  have capacity := unique.length_le_of_subset (l₂ := List.finRange (2 ^ width))
    (fun {_} _ => List.mem_finRange _)
  exact minTagBits_le_iff.mpr (by simpa using capacity)

theorem packDenseSum_minimum {left right width : Nat}
    (encode : Sum (Fin left) (Fin right) → BitVec width) (distinct : Function.Injective encode) :
    minTagBits (left + right) ≤ width := by
  apply packDenseIndex_minimum (encode ∘ denseVariant)
  intro a b same
  simpa using congrArg denseIndex (distinct same)

theorem denseSum_no_wider_than_tagged (left right : Nat) :
    minTagBits (left + right) ≤ (max (minTagBits left) (minTagBits right)) + 1 := by
  rw [minTagBits_le_iff, Nat.pow_succ, Nat.mul_two]
  exact Nat.add_le_add (minTagBits_le_iff.mp (Nat.le_max_left ..))
    (minTagBits_le_iff.mp (Nat.le_max_right ..))

/-- A finite field's complete code fits in the underlying byte image. -/
structure DenseIndexField (size count : Nat) where
  offset : Nat
  fits : offset + minTagBits count ≤ size * 8

def DenseIndexField.load (field : DenseIndexField size count) (image : Image size) : Option (Fin count) :=
  unpackDenseIndex count (image.readBits field.offset (minTagBits count))

def DenseIndexField.store (field : DenseIndexField size count) (image : Image size) (code : Fin count) :
    Image size :=
  image.writeBits field.offset (packDenseIndex code)

theorem DenseIndexField.load_correct (field : DenseIndexField size count) (image : Image size) (code : Fin count) :
    field.load image = some code ↔ image.readBits field.offset (minTagBits count) = packDenseIndex code :=
  unpackDenseIndex_correct

theorem DenseIndexField.load_store (field : DenseIndexField size count) (image : Image size) (code : Fin count) :
    field.load (field.store image code) = some code :=
  (field.load_correct ..).mpr (Image.read_write image field.offset (packDenseIndex code) field.fits)

theorem DenseIndexField.store_frames_bits (field : DenseIndexField size count) (image : Image size)
    (code : Fin count) (offset width : Nat) (fits : offset + width ≤ size * 8)
    (separate : field.offset + minTagBits count ≤ offset ∨ offset + width ≤ field.offset) :
    (field.store image code).readBits offset width = image.readBits offset width :=
  Image.read_write_separate image field.offset offset width (packDenseIndex code) fits separate

abbrev DenseSumField (size left right : Nat) := DenseIndexField size (left + right)

def DenseSumField.load (field : DenseSumField size left right) (image : Image size) :
    Option (Sum (Fin left) (Fin right)) :=
  (DenseIndexField.load field image).map denseVariant

def DenseSumField.store (field : DenseSumField size left right) (image : Image size)
    (value : Sum (Fin left) (Fin right)) : Image size :=
  DenseIndexField.store field image (denseIndex value)

theorem DenseSumField.load_correct (field : DenseSumField size left right) (image : Image size)
    (value : Sum (Fin left) (Fin right)) :
    DenseSumField.load field image = some value ↔
      image.readBits field.offset (minTagBits (left + right)) = packDenseSum value :=
  unpackDenseSum_correct

theorem DenseSumField.load_store (field : DenseSumField size left right) (image : Image size)
    (value : Sum (Fin left) (Fin right)) :
    DenseSumField.load field (DenseSumField.store field image value) = some value := by
  simp [load, store, DenseIndexField.load_store]

theorem DenseSumField.store_frames_bits (field : DenseSumField size left right) (image : Image size)
    (value : Sum (Fin left) (Fin right)) (offset width : Nat) (fits : offset + width ≤ size * 8)
    (separate : field.offset + minTagBits (left + right) ≤ offset ∨ offset + width ≤ field.offset) :
    (DenseSumField.store field image value).readBits offset width = image.readBits offset width :=
  DenseIndexField.store_frames_bits field image (denseIndex value) offset width fits separate

def CompactADT.Valid (spec : CompactADT) : Prop :=
  spec.variants.length ≤ 2 ^ spec.tagBits ∧
  (∀ v ∈ spec.variants, v.tag < 2 ^ spec.tagBits ∧ v.payloadBits ≤ spec.maxPayloadBits) ∧
  (spec.variants.map VariantSpec.tag).Nodup

def CompactADT.totalBits (spec : CompactADT) : Nat :=
  spec.tagBits + spec.maxPayloadBits

def CompactADT.totalBytes (spec : CompactADT) : Nat :=
  (spec.totalBits + 7) / 8

def CompactADT.canShareByte (spec : CompactADT) : Bool :=
  decide (spec.totalBits < 8)

structure CompactValue (spec : CompactADT) where
  tag : Nat
  payload : Nat
  valid : ∃ v ∈ spec.variants, v.tag = tag ∧ payload < 2 ^ v.payloadBits

def CompactADT.encode (spec : CompactADT) (val : CompactValue spec) : Nat :=
  val.tag + (2 ^ spec.tagBits) * val.payload

def CompactADT.decode (spec : CompactADT) (bits : Nat) : Option (Nat × Nat) :=
  let tag := bits % (2 ^ spec.tagBits)
  let payload := bits / (2 ^ spec.tagBits)
  match spec.variants.find? fun v => v.tag == tag with
  | some v => if payload < 2 ^ v.payloadBits then some (tag, payload) else none
  | none => none

private theorem find?_unique_variant {variants : List VariantSpec}
    (hNodup : (variants.map VariantSpec.tag).Nodup)
    {v w : VariantSpec} (hv : v ∈ variants) (hw : w ∈ variants) (hTag : w.tag = v.tag) :
    w = v := by
  obtain ⟨i, hi, atV⟩ := List.mem_iff_getElem.mp hv
  obtain ⟨j, hj, atW⟩ := List.mem_iff_getElem.mp hw
  have hPair : variants.Pairwise fun a b => a.tag ≠ b.tag := List.pairwise_map.mp hNodup
  have hGet := List.pairwise_iff_getElem.mp hPair
  rcases Nat.lt_trichotomy i j with hLt | rfl | hGt
  · have hNe := hGet i j hi hj hLt
    rw [atV, atW] at hNe
    exact False.elim (hNe hTag.symm)
  · exact atW.symm.trans atV
  · have hNe := hGet j i hj hi hGt
    rw [atV, atW] at hNe
    exact False.elim (hNe hTag)

theorem CompactADT.encode_fits {spec : CompactADT} (hSpec : spec.Valid)
    (val : CompactValue spec) :
    spec.encode val < 2 ^ spec.totalBits := by
  obtain ⟨v, hvMem, hTagEq, hPayLt⟩ := val.valid
  obtain ⟨hTagBound, hPayBound⟩ := hSpec.2.1 v hvMem
  have hTagLt : val.tag < 2 ^ spec.tagBits := hTagEq ▸ hTagBound
  have hPayLe : 2 ^ v.payloadBits ≤ 2 ^ spec.maxPayloadBits :=
    Nat.pow_le_pow_right (by decide) hPayBound
  have hPayMax : val.payload < 2 ^ spec.maxPayloadBits := Nat.lt_of_lt_of_le hPayLt hPayLe
  simpa only [CompactADT.encode, CompactADT.totalBits, Nat.mul_comm (2 ^ spec.tagBits)] using
    concatCode_fits hTagLt hPayMax

theorem CompactADT.encode_parts {spec : CompactADT} (hSpec : spec.Valid) (val : CompactValue spec) :
    spec.encode val % 2 ^ spec.tagBits = val.tag ∧
      spec.encode val / 2 ^ spec.tagBits = val.payload := by
  obtain ⟨variant, member, tag, _⟩ := val.valid
  have tagFits : val.tag < 2 ^ spec.tagBits := tag ▸ (hSpec.2.1 variant member).1
  simpa only [CompactADT.encode, Nat.mul_comm (2 ^ spec.tagBits)] using
    concatCode_split (high := val.payload) tagFits

theorem CompactADT.decode_encode {spec : CompactADT} (hSpec : spec.Valid)
    (val : CompactValue spec) :
    spec.decode (spec.encode val) = some (val.tag, val.payload) := by
  obtain ⟨v, hvMem, hTagEq, hPayLt⟩ := val.valid
  obtain ⟨hMod, hDiv⟩ := spec.encode_parts hSpec val
  dsimp [CompactADT.decode]
  rw [hMod, hDiv]
  cases hFind : spec.variants.find? (fun w => w.tag == val.tag) with
  | none =>
    have hNone := List.find?_eq_none.mp hFind v hvMem
    simp [hTagEq] at hNone
  | some w =>
    have hwMem := List.mem_of_find?_eq_some hFind
    have hwTag : w.tag = val.tag := by
      simpa using List.find?_some hFind
    have hwEq : w = v := find?_unique_variant hSpec.2.2 hvMem hwMem (hwTag.trans hTagEq.symm)
    subst hwEq
    simp [hPayLt]

theorem CompactADT.encode_injective {spec : CompactADT} (hSpec : spec.Valid)
    {a b : CompactValue spec} (hEq : spec.encode a = spec.encode b) :
    a.tag = b.tag ∧ a.payload = b.payload := by
  have hDec := congrArg spec.decode hEq
  rw [spec.decode_encode hSpec a, spec.decode_encode hSpec b] at hDec
  have hPair := Option.some.inj hDec
  exact ⟨congrArg Prod.fst hPair, congrArg Prod.snd hPair⟩

/-- Canonical `CompactADT` descriptor for `Aethel.Status` (`idle`, `moving`,
`poisoned`, `dead`): 2 tag bits + 4 payload bits = 6 bits total. -/
def statusCompactADT : CompactADT :=
  ⟨2, 4, [⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 4⟩, ⟨3, 0⟩]⟩

theorem statusCompactADT_valid : statusCompactADT.Valid := by
  refine ⟨by decide, ?_, by decide⟩
  intro v hv
  simp only [statusCompactADT, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> decide

theorem statusCompactADT_fits_byte :
    statusCompactADT.totalBits = 6 ∧ statusCompactADT.canShareByte = true := by
  decide

end Aethel.ADTLayout
