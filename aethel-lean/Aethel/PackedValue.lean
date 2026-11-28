import Aethel.ADTLayout

namespace Aethel.AutomaticLayout

open ADTLayout

/-- A fixed-width representation with an independent canonical encoding.
A decoder accepts exactly the images of logical values. -/
structure PackedCodec (α : Type) (width : Nat) where
  encode : α → BitVec width
  decode : BitVec width → Option α
  decode_encode : ∀ value, decode (encode value) = some value
  encode_decode : ∀ {bits value}, decode bits = some value → encode value = bits

def PackedCodec.raw (width : Nat) : PackedCodec (BitVec width) width :=
  ⟨id, some, fun _ => rfl, fun h => (Option.some.inj h).symm⟩

/-- Validate logical refinements such as an integer range or a variant's
recursively encoded payload. Successful decoding retains the evidence. -/
def PackedCodec.refine (codec : PackedCodec α width) (valid : α → Prop) [DecidablePred valid] :
    PackedCodec { value // valid value } width where
  encode value := codec.encode value.val
  decode bits := do
    let value ← codec.decode bits
    if checked : valid value then some ⟨value, checked⟩ else none
  decode_encode := by
    intro value
    simp [bind, codec.decode_encode, value.property]
  encode_decode := by
    intro bits value decoded
    obtain ⟨raw, found, refined⟩ := Option.bind_eq_some_iff.mp decoded
    split at refined
    · cases refined
      exact codec.encode_decode found
    · contradiction

/-- The first member occupies the low bits of the product. -/
def PackedCodec.product (left : PackedCodec α a) (right : PackedCodec β b) :
    PackedCodec (α × β) (b + a) where
  encode value := right.encode value.2 ++ left.encode value.1
  decode bits := do
    let first ← left.decode (bits.extractLsb' 0 a)
    let second ← right.decode (bits.extractLsb' a b)
    return (first, second)
  decode_encode := by
    intro value
    simp [BitVec.extractLsb'_append_eq_left, BitVec.extractLsb'_append_eq_right,
      left.decode_encode, right.decode_encode, bind]
  encode_decode := by
    intro bits value decoded
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at decoded
    obtain ⟨first, firstDecoded, second, secondDecoded, rfl⟩ := decoded
    rw [left.encode_decode firstDecoded, right.encode_decode secondDecoded]
    exact BitVec.extractLsb'_append_extractLsb'

def PackedCodec.tagged (spec : CompactADT) (valid : spec.Valid) :
    PackedCodec (CompactValue spec) spec.totalBits where
  encode value := BitVec.ofNatLT (spec.encode value) (spec.encode_fits valid value)
  decode bits :=
    let tag := bits.toNat % 2 ^ spec.tagBits
    let payload := bits.toNat / 2 ^ spec.tagBits
    if found : ∃ v ∈ spec.variants, v.tag = tag ∧ payload < 2 ^ v.payloadBits then
      some ⟨tag, payload, found⟩
    else none
  decode_encode := by
    intro value
    simp only [BitVec.toNat_ofNatLT]
    obtain ⟨tagEq, payloadEq⟩ := spec.encode_parts valid value
    simp [tagEq, payloadEq, dite_eq_left value.valid]
  encode_decode := by
    intro bits value decoded
    dsimp only at decoded
    split at decoded
    · cases decoded
      apply BitVec.eq_of_toNat_eq
      simp [CompactADT.encode, Nat.mod_add_div]
    · contradiction

structure PackedValueField (size width : Nat) where
  start : Nat
  fits : start + width ≤ size * 8

theorem resolved_fixed_fits {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {path : List Nat} {placement : Placement} {width : Nat} {slot : IntegerSlot}
    (planned : Conforms abi schema layout)
    (found : AutomaticLayout.resolve layout path = some (placement, .fixed width slot)) :
    placement.bitStart + width ≤ layout.size * 8 := by
  obtain ⟨child, _, conforms, located⟩ := resolve_sound planned found
  cases conforms with
  | fixed slotValid =>
    have within := located.1
    cases h : placement.bitOffset with
    | none =>
      have payload := slotValid.1
      simp only [Field.bytes, h, Option.isSome_none, Bool.false_eq_true, ite_false,
        Layout.size] at within
      change placement.byteOffset + slot.size ≤ layout.size at within
      simp [Placement.bitStart, h]
      omega
    | some bit =>
      have approved := located.2
      rw [show (placement, Layout.fixed width slot).1.bitOffset = some bit from h] at approved
      simpa only [Layout.bits] using approved.2.2.2

/-- Resolve the location of a fixed codec by declaration index. The expected
width is checked against the validated representation. -/
def PackedValueField.resolve {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) (path : List Nat) (width : Nat) :
    Option (PackedValueField layout.size width) :=
  match found : AutomaticLayout.resolve layout path with
  | some (placement, .fixed actual _) =>
    if same : actual = width then
      some ⟨placement.bitStart, same ▸ resolved_fixed_fits planned found⟩
    else none
  | _ => none

theorem PackedValueField.resolve_coordinates {abi : TargetIntegerABI} {schema : Schema}
    {layout : Layout} (planned : Conforms abi schema layout) {path : List Nat}
    {width : Nat} {field : PackedValueField layout.size width}
    (found : PackedValueField.resolve planned path width = some field) :
    ∃ place slot, AutomaticLayout.resolve layout path = some (place, .fixed width slot) ∧
      field.start = place.bitStart ∧ width ≤ Field.bitExtent (place, .fixed width slot) := by
  unfold PackedValueField.resolve at found
  split at found
  · rename_i place actual slot projected
    split at found
    · rename_i same
      subst actual
      cases found
      refine ⟨place, slot, projected, rfl, ?_⟩
      obtain ⟨_, _, conforms, _⟩ := resolve_sound planned projected
      cases conforms with
      | fixed valid =>
        cases atBit : place.bitOffset with
        | none => simpa [Field.bitExtent, Layout.size, atBit] using valid.1
        | some bit => simp [Field.bitExtent, Layout.bits, atBit]
    · contradiction
  · contradiction

def PackedValueField.load (field : PackedValueField size width) (codec : PackedCodec α width)
    (image : Image size) : Option α :=
  codec.decode (image.readBytes field.start width)

def PackedValueField.store (field : PackedValueField size width) (codec : PackedCodec α width)
    (image : Image size) (value : α) : Image size :=
  image.writeBytes field.start (codec.encode value)

theorem PackedValueField.load_store (field : PackedValueField size width)
    (codec : PackedCodec α width) (image : Image size) (value : α) :
    field.load codec (field.store codec image value) = some value := by
  simp [load, store, Image.readBytes_refines, Image.writeBytes_refines,
    Image.read_write _ _ _ field.fits, codec.decode_encode]

theorem PackedValueField.load_store_other (written : PackedValueField size w)
    (observed : PackedValueField size v) (writer : PackedCodec α w) (reader : PackedCodec β v)
    (image : Image size) (value : α)
    (separate : written.start + w ≤ observed.start ∨ observed.start + v ≤ written.start) :
    observed.load reader (written.store writer image value) = observed.load reader image := by
  simp only [load, store, Image.readBytes_refines, Image.writeBytes_refines,
    Image.read_write_separate _ _ _ _ _ observed.fits separate]

end Aethel.AutomaticLayout
