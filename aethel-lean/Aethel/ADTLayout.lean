import Aethel.StatusCodec
import Aethel.FunctionSummaries
import Aethel.IntegerTypes
import Aethel.AutomaticLayout

namespace Aethel.ADTLayout

open Aethel

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

def minTagBits : Nat → Nat
  | 0 | 1 => 0
  | 2 => 1
  | n => if n ≤ 4 then 2 else if n ≤ 8 then 3 else if n ≤ 16 then 4 else 8

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
  have hPaySucc : val.payload + 1 ≤ 2 ^ spec.maxPayloadBits := hPayMax
  have hMulLe : 2 ^ spec.tagBits * (val.payload + 1) ≤ 2 ^ spec.tagBits * 2 ^ spec.maxPayloadBits :=
    Nat.mul_le_mul_left (2 ^ spec.tagBits) hPaySucc
  have hPowAdd : 2 ^ spec.tagBits * 2 ^ spec.maxPayloadBits = 2 ^ spec.totalBits := by
    simp [CompactADT.totalBits, Nat.pow_add]
  dsimp [CompactADT.encode]
  calc
    val.tag + 2 ^ spec.tagBits * val.payload
      < 2 ^ spec.tagBits + 2 ^ spec.tagBits * val.payload := by omega
    _ = 2 ^ spec.tagBits * (val.payload + 1) := by rw [Nat.mul_succ, Nat.add_comm]
    _ ≤ 2 ^ spec.totalBits := hPowAdd ▸ hMulLe

theorem CompactADT.decode_encode {spec : CompactADT} (hSpec : spec.Valid)
    (val : CompactValue spec) :
    spec.decode (spec.encode val) = some (val.tag, val.payload) := by
  obtain ⟨v, hvMem, hTagEq, hPayLt⟩ := val.valid
  obtain ⟨hTagBound, _⟩ := hSpec.2.1 v hvMem
  have hPowPos : 0 < 2 ^ spec.tagBits := Nat.two_pow_pos spec.tagBits
  have hTagLt : val.tag < 2 ^ spec.tagBits := hTagEq ▸ hTagBound
  have hMod : (spec.encode val) % (2 ^ spec.tagBits) = val.tag := by
    dsimp [CompactADT.encode]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hTagLt]
  have hDiv : (spec.encode val) / (2 ^ spec.tagBits) = val.payload := by
    dsimp [CompactADT.encode]
    rw [Nat.add_mul_div_left _ _ hPowPos, Nat.div_eq_of_lt hTagLt, Nat.zero_add]
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
