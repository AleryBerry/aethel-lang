import Aethel.AutomaticLayout

namespace Aethel.AutomaticLayout

/-- A finite byte image. Byte addresses are bounded by the allocation size. -/
abbrev Image (size : Nat) := Fin size → BitVec 8

private def bitsOfFn (f : Fin width → Bool) : BitVec width :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

private theorem bitsOfFn_get (f : Fin width → Bool) {i : Nat} (hi : i < width) :
    (bitsOfFn f).getLsbD i = f ⟨i, hi⟩ := by
  simp only [bitsOfFn, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]

def Image.bit (image : Image size) (index : Nat) : Bool :=
  if within : index / 8 < size then
    (image ⟨index / 8, within⟩).getLsbD (index % 8)
  else false

def Image.readBits (image : Image size) (offset width : Nat) : BitVec width :=
  bitsOfFn fun i => image.bit (offset + i.val)

def Image.writeBits (image : Image size) (offset : Nat) (bits : BitVec width) : Image size :=
  fun byte => bitsOfFn fun bit =>
    let index := byte.val * 8 + bit.val
    if offset ≤ index ∧ index < offset + width then bits.getLsbD (index - offset)
    else (image byte).getLsbD bit.val

theorem Image.bit_write (image : Image size) (offset : Nat) (bits : BitVec width)
    (index : Nat) (within : index < size * 8) :
    (image.writeBits offset bits).bit index =
      if offset ≤ index ∧ index < offset + width then bits.getLsbD (index - offset)
      else image.bit index := by
  have address : index / 8 < size := (Nat.div_lt_iff_lt_mul (by decide)).mpr within
  have bit : index % 8 < 8 := Nat.mod_lt _ (by decide)
  have decompose : index / 8 * 8 + index % 8 = index := by
    simpa [Nat.add_comm, Nat.mul_comm] using Nat.mod_add_div index 8
  simp only [Image.bit, dite_eq_left address, Image.writeBits, bitsOfFn_get _ bit, decompose]

theorem Image.readBits_getLsbD (image : Image size) (offset width : Nat) {i : Nat}
    (hi : i < width) :
    (image.readBits offset width).getLsbD i = image.bit (offset + i) := by
  simp only [Image.readBits, bitsOfFn_get _ hi]

def bitIntervalBytes (offset width : Nat) : List Nat :=
  if width = 0 then []
  else (List.range ((offset % 8 + width + 7) / 8)).map (fun i => offset / 8 + i)

def Image.bytesAt (image : Image size) (offsets : List Nat) : List (BitVec 8) :=
  offsets.map fun byte => if within : byte < size then image ⟨byte, within⟩ else 0

/-- Assemble increasing memory addresses as a little-endian integer, then
select the payload interval. The payload need not fit a machine word. -/
def decodeLittleEndianBytes (bytes : List (BitVec 8)) (skip width : Nat) : BitVec width :=
  BitVec.extractLsb' skip width (BitVec.flattenList bytes.reverse)

def Image.readBytes (image : Image size) (offset width : Nat) : BitVec width :=
  decodeLittleEndianBytes (image.bytesAt (bitIntervalBytes offset width)) (offset % 8) width

theorem Image.readBytes_refines (image : Image size) (offset width : Nat) :
    image.readBytes offset width = image.readBits offset width := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit within
  rw [Image.readBits_getLsbD _ _ _ within]
  let count := (offset % 8 + width + 7) / 8
  let index := (offset % 8 + bit) / 8
  have listBound : index < count := by dsimp [index, count]; omega
  have bitBound : offset % 8 + bit < 8 * ((offset % 8 + width + 7) / 8) := by
    dsimp [index, count] at listBound
    omega
  have address : offset / 8 + index = (offset + bit) / 8 := by dsimp [index]; omega
  have bitIndex : (offset % 8 + bit) % 8 = (offset + bit) % 8 := by omega
  have nonempty : width ≠ 0 := by omega
  simp only [Image.readBytes, decodeLittleEndianBytes, Image.bytesAt, bitIntervalBytes,
    ite_eq_right nonempty, BitVec.getLsbD_extractLsb', BitVec.getLsbD_flattenList, List.length_reverse,
    List.length_map, List.length_range, within, bitBound, decide_true, Bool.true_and]
  change (((((List.range count).map (fun i => offset / 8 + i)).map
    (fun byte => if h : byte < size then image ⟨byte, h⟩ else 0)).reverse[count - 1 - index]?).getD 0).getLsbD
    ((offset % 8 + bit) % 8) = _
  rw [List.getElem?_reverse (by simp only [List.length_map, List.length_range]; omega)]
  simp only [List.length_map, List.length_range, show count - 1 - (count - 1 - index) = index by omega,
    List.getElem?_map, List.getElem?_range listBound, Option.map_some, Option.getD_some, address, bitIndex]
  by_cases inBounds : (offset + bit) / 8 < size <;> simp [Image.bit, inBounds]

theorem Image.read_write (image : Image size) (offset : Nat) (bits : BitVec width)
    (fits : offset + width ≤ size * 8) :
    (image.writeBits offset bits).readBits offset width = bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Image.readBits, bitsOfFn_get _ hi]
  rw [Image.bit_write _ _ _ _ (by omega)]
  simp [hi]

theorem Image.read_write_separate (image : Image size) (offset other count : Nat)
    (bits : BitVec width) (fits : other + count ≤ size * 8)
    (separate : offset + width ≤ other ∨ other + count ≤ offset) :
    (image.writeBits offset bits).readBits other count = image.readBits other count := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Image.readBits, bitsOfFn_get _ hi]
  rw [Image.bit_write _ _ _ _ (by omega)]
  exact ite_eq_right (by omega)

theorem Image.write_preserves_byte (image : Image size) (offset : Nat) (bits : BitVec width)
    (byte : Fin size) (outside : byte.val * 8 + 8 ≤ offset ∨ offset + width ≤ byte.val * 8) :
    image.writeBits offset bits byte = image byte := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Image.writeBits, bitsOfFn_get _ hi]
  exact ite_eq_right (by omega)

private def payloadByte (bits : BitVec width) (offset start : Nat) : BitVec 8 :=
  if offset ≤ start then BitVec.extractLsb' (start - offset) 8 bits
  else BitVec.extractLsb' 0 8 bits <<< (offset - start)

private theorem payloadByte_bit (bits : BitVec width) (offset start : Nat) {i : Nat}
    (hi : i < 8) (lower : offset ≤ start + i) :
    (payloadByte bits offset start).getLsbD i = bits.getLsbD (start + i - offset) := by
  unfold payloadByte
  split
  · rename_i aligned
    simp only [BitVec.getLsbD_extractLsb', hi, decide_true, Bool.true_and]
    congr 1
    omega
  · have enough : ¬ i < offset - start := by omega
    have within : start + i - offset < 8 := by omega
    have same : i - (offset - start) = start + i - offset := by omega
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_extractLsb', hi, enough, within,
      decide_true, decide_false, Bool.not_false, Bool.true_and, Nat.zero_add, same]

private def intervalMask (offset ending start : Nat) : BitVec 8 :=
  (BitVec.allOnes 8 <<< (offset - start)) &&& (BitVec.allOnes 8 >>> (8 - (ending - start)))

private theorem intervalMask_bit (offset ending start : Nat) {i : Nat} (hi : i < 8) :
    (intervalMask offset ending start).getLsbD i = decide (offset ≤ start + i ∧ start + i < ending) := by
  apply Bool.eq_iff_iff.mpr
  simp only [intervalMask, BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not]
  omega

/-- Compute one byte of a store. Interior bytes need only the incoming value.
Boundary bytes use read-modify-write to preserve bits outside the payload. -/
def Image.writeBytes (image : Image size) (offset : Nat) (bits : BitVec width) : Image size :=
  fun byte =>
    let start := byte.val * 8
    let ending := offset + width
    if width = 0 ∨ start + 8 ≤ offset ∨ ending ≤ start then image byte
    else
      let payload := payloadByte bits offset start
      if offset ≤ start ∧ start + 8 ≤ ending then payload
      else
        let mask := intervalMask offset ending start
        (image byte &&& ~~~mask) ||| (payload &&& mask)

theorem Image.writeBytes_refines (image : Image size) (offset : Nat) (bits : BitVec width) :
    image.writeBytes offset bits = image.writeBits offset bits := by
  funext byte
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Image.writeBytes, Image.writeBits, bitsOfFn_get _ hi]
  split
  · exact (ite_eq_right (by omega)).symm
  · split
    · rw [payloadByte_bit _ _ _ hi (by omega), ite_eq_left (by omega)]
    · simp only [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not, intervalMask_bit _ _ _ hi,
        hi, decide_true, Bool.true_and]
      split
      · rename_i inside
        rw [decide_eq_true inside, payloadByte_bit _ _ _ hi inside.1]
        simp
      · rename_i outside
        rw [decide_eq_false outside]
        simp

/-- A resolved integer field with a proof that its payload fits the byte image.
For addressable slots this excludes padding from the value. -/
structure IntegerField (size : Nat) where
  kind : IntegerType
  offset : Nat
  fits : offset + kind.bits ≤ size * 8

def IntegerField.get (field : IntegerField size) (image : Image size) : BitVec field.kind.bits :=
  image.readBits field.offset field.kind.bits

def IntegerField.set (field : IntegerField size) (image : Image size)
    (value : BitVec field.kind.bits) : Image size :=
  image.writeBytes field.offset value

theorem IntegerField.get_set (field : IntegerField size) (image : Image size)
    (value : BitVec field.kind.bits) : field.get (field.set image value) = value := by
  simpa [IntegerField.get, IntegerField.set, Image.writeBytes_refines] using
    Image.read_write image field.offset value field.fits

theorem IntegerField.get_set_other (written observed : IntegerField size) (image : Image size)
    (value : BitVec written.kind.bits)
    (separate : written.offset + written.kind.bits ≤ observed.offset ∨
      observed.offset + observed.kind.bits ≤ written.offset) :
    observed.get (written.set image value) = observed.get image := by
  simpa [IntegerField.get, IntegerField.set, Image.writeBytes_refines] using
    Image.read_write_separate image written.offset observed.offset observed.kind.bits value
      observed.fits separate

theorem integer_span {abi : TargetIntegerABI} {kind : IntegerType} {slot : IntegerSlot}
    {placement : Placement} {total align : Nat} {policy : StoragePolicy}
    (representation : Conforms abi (.integer kind) (.integer kind slot))
    (valid : Field.Valid total align policy (placement, .integer kind slot)) :
    placement.bitStart + kind.bits ≤
      (placement.byteOffset + Field.bytes (placement, .integer kind slot)) * 8 := by
  cases representation with
  | integer slotValid =>
    cases bit : placement.bitOffset with
    | none =>
      have payload := slotValid.1
      simp [IntegerType.payloadBytes] at payload
      simp [Placement.bitStart, Field.bytes, bit, Layout.size]
      omega
    | some offset =>
      simp [Placement.bitStart, Field.bytes, bit, Layout.bits, Nat.ne_of_gt kind.bits_pos]
      omega

theorem resolved_integer_fits {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    {path : List Nat} {placement : Placement} {kind : IntegerType} {slot : IntegerSlot}
    (planned : Conforms abi schema layout)
    (found : resolve layout path = some (placement, .integer kind slot)) :
    placement.bitStart + kind.bits ≤ layout.size * 8 := by
  obtain ⟨child, _, valid, located⟩ := resolve_sound planned found
  cases valid with
  | integer slotValid =>
    have within := integer_span (.integer slotValid) located
    have extent := located.1
    change placement.byteOffset + Field.bytes (placement, .integer kind (abi.slot kind)) ≤ layout.size at extent
    omega

/-- Resolve an integer leaf from a certified layout. The proof records the
bounds of the actual logical payload, including packed fields. -/
def resolveInteger {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) (path : List Nat) : Option (IntegerField layout.size) :=
  match found : resolve layout path with
  | some (placement, .integer kind _slot) =>
    some ⟨kind, placement.bitStart, resolved_integer_fits planned found⟩
  | _ => none

/-- Obtain a usable layout and its independent conformance certificate. -/
def planVerified (abi : TargetIntegerABI) (schema : Schema) :
    Option {layout : Layout // Conforms abi schema layout} :=
  match planned : plan abi schema with
  | some layout => some ⟨layout, plan_sound planned⟩
  | none => none

def Image.ofBytes (bytes : List UInt8) : Image bytes.length :=
  fun index => bytes[index.val].toBitVec

def Image.toBytes (image : Image size) : List UInt8 :=
  List.ofFn fun index => UInt8.ofBitVec (image index)

theorem Image.toBytes_ofBytes (bytes : List UInt8) : (Image.ofBytes bytes).toBytes = bytes := by
  apply List.ext_getElem
  · simp [Image.toBytes]
  · intro i actual expected
    simp only [Image.toBytes, List.getElem_ofFn, Image.ofBytes, UInt8.ofBitVec_toBitVec]

abbrev IntegerBits := (kind : IntegerType) × BitVec kind.bits

def readInteger {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) (path : List Nat) (image : Image layout.size) :
    Option IntegerBits :=
  (resolveInteger planned path).map fun field => ⟨field.kind, field.get image⟩

def writeInteger {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) (path : List Nat) (image : Image layout.size)
    (value : IntegerBits) : Option (Image layout.size) := do
  let field ← resolveInteger planned path
  if matchesKind : value.1 = field.kind then
    some (field.set image (matchesKind ▸ value.2))
  else none

theorem readInteger_after_write {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) (path : List Nat) (image next : Image layout.size)
    (value : IntegerBits) (written : writeInteger planned path image value = some next) :
    readInteger planned path next = some value := by
  cases h : resolveInteger planned path with
  | none => simp [writeInteger, h, bind] at written
  | some field =>
    simp only [writeInteger, h, bind, Option.bind_some] at written
    split at written
    next same =>
      obtain ⟨kind, bits⟩ := value
      change kind = field.kind at same
      subst kind
      cases written
      simp [readInteger, h, IntegerField.get_set]
    next => cases written

theorem readInteger_preserved_by_disjoint_write
    {abi : TargetIntegerABI} {schema : Schema} {layout : Layout}
    (planned : Conforms abi schema layout) {writePath readPath : List Nat}
    {image next : Image layout.size} {value : IntegerBits}
    {written observed : IntegerField layout.size}
    (writeField : resolveInteger planned writePath = some written)
    (readField : resolveInteger planned readPath = some observed)
    (separate : written.offset + written.kind.bits ≤ observed.offset ∨
      observed.offset + observed.kind.bits ≤ written.offset)
    (updated : writeInteger planned writePath image value = some next) :
    readInteger planned readPath next = readInteger planned readPath image := by
  simp only [writeInteger, writeField, bind, Option.bind_some] at updated
  split at updated
  next same =>
    cases updated
    simp only [readInteger, readField, Option.map_some,
      IntegerField.get_set_other _ _ _ _ separate]
  next => cases updated

/-- A record certificate separates the value bits of different integer
siblings, even when their physical byte accesses overlap. -/
theorem integer_sibling_bits_separate {abi : TargetIntegerABI}
    {fields : List (StoragePolicy × Schema)} {size alignment : Nat} {placed : List Field}
    {i j : Nat} {left right : Placement} {lk rk : IntegerType} {ls rs : IntegerSlot}
    (planned : Conforms abi (.record fields) (.record size alignment placed))
    (first : placed[i]? = some (left, .integer lk ls))
    (second : placed[j]? = some (right, .integer rk rs))
    (ordered : i < j) :
    left.bitStart + lk.bits ≤ right.bitStart ∨ right.bitStart + rk.bits ≤ left.bitStart := by
  obtain ⟨_, _, _, leftValid, leftRepr⟩ := planned.field first
  obtain ⟨_, _, _, rightValid, rightRepr⟩ := planned.field second
  cases leftRepr
  cases rightRepr
  have leftSpan := integer_span (.integer (by assumption)) leftValid
  have rightSpan := integer_span (.integer (by assumption)) rightValid
  obtain ⟨hi, atLeft⟩ := List.getElem?_eq_some_iff.mp first
  obtain ⟨hj, atRight⟩ := List.getElem?_eq_some_iff.mp second
  have geometry := by
    cases planned with
    | record _ _ _ apart _ _ => exact apart
  have separated := List.pairwise_iff_getElem.mp geometry i j hi hj ordered
  rw [atLeft, atRight] at separated
  have lpositive : 0 < lk.bits := lk.bits_pos
  have rpositive : 0 < rk.bits := rk.bits_pos
  simp only [Field.Separate] at separated
  rcases separated with zero | zero | before | after | same
  · simp [Placement.bitStart, zero] at leftSpan
    omega
  · simp [Placement.bitStart, zero] at rightSpan
    omega
  · left
    simp only [Placement.bitStart] at leftSpan ⊢
    omega
  · right
    simp only [Placement.bitStart] at rightSpan ⊢
    omega
  · cases l : left.bitOffset <;> cases r : right.bitOffset <;>
      simp [l, r, Layout.bits] at same
    exact same

end Aethel.AutomaticLayout
