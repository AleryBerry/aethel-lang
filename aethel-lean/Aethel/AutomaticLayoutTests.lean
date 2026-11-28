import Aethel.PackedRecord

namespace Aethel.AutomaticLayout.Tests

private def integer (width : IntegerWidth) (policy : StoragePolicy := .addressable) :
    StoragePolicy × Schema := (policy, .integer (.unsigned width))

private def require (name : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError name)

private def expectPlan (schema : Schema) (bytes alignment : Nat) : IO Layout := do
  let some layout := plan .natural schema
    | throw (IO.userError "planner rejected a supported record")
  require s!"expected {bytes} bytes with alignment {alignment}, got {repr layout}"
    (layout.size == bytes && layout.alignment == alignment)
  return layout

private def expectField (layout : Layout) (path : List Nat) (offset : Nat) (bit : Option Nat)
    (width : Nat) : IO Unit :=
  require s!"unexpected location for {path} in {repr layout}"
    ((resolve layout path).any fun (placement, fieldType) =>
      placement.byteOffset == offset && placement.bitOffset == bit && fieldType.bits == width)

def run : IO Unit := do
  let single ← expectPlan (.record [integer .w8, integer .w32, integer .w1, integer .w8]) 8 4
  expectField single [0] 4 none 8
  expectField single [1] 0 none 32
  expectField single [2] 5 none 1
  expectField single [3] 6 none 8
  let flags := List.replicate 5 (integer .w1 .mayShareByte)
  let mixed ← expectPlan (.record (flags ++ [integer .w32])) 8 4
  expectField mixed [0] 4 (some 0) 1
  expectField mixed [4] 4 (some 4) 1
  expectField mixed [5] 0 none 32
  let separate ← expectPlan (.record (List.replicate 5 (integer .w1) ++ [integer .w32])) 12 4
  expectField separate [4] 4 none 1
  let spill ← expectPlan (.record [integer .w4 .mayShareByte, integer .w4 .mayShareByte,
    integer .w2 .mayShareByte, integer .w1 .mayShareByte]) 2 1
  expectField spill [0] 0 (some 0) 4
  expectField spill [1] 0 (some 4) 4
  expectField spill [2] 1 (some 0) 2
  expectField spill [3] 1 (some 2) 1
  let nested ← expectPlan (.record [integer .w8, integer .w64,
    (.addressable, .record (flags ++ [integer .w32])), integer .w8]) 24 8
  expectField nested [2, 0] 12 (some 0) 1
  expectField nested [2, 5] 8 none 32
  expectField nested [1] 0 none 64
  require "out-of-range nested path" (resolve nested [2, 6]).isNone
  require "cannot descend through a scalar" (resolve nested [2, 5, 0]).isNone
  let empty ← expectPlan (.record [(.addressable, .record []), integer .w8]) 1 1
  let _ ← expectPlan (.record []) 0 1
  expectField empty [0] 0 none 0
  let malformed := .record [integer .w32]
  require "undersized target slot is rejected"
    (plan ⟨fun _ => ⟨1, 1⟩⟩ malformed).isNone
  let word := Layout.integer (.unsigned .w8) ⟨1, 1⟩
  require "forged overlapping addressable fields are rejected"
    (!(validate .natural 2 (.record [integer .w8, integer .w8])
      (.record 1 1 [(⟨0, none⟩, word), (⟨0, none⟩, word)])))
  let flag := Layout.integer (.unsigned .w1) ⟨1, 1⟩
  require "forged overlapping packed fields are rejected"
    (!(validate .natural 2 (.record (List.replicate 2 (integer .w1 .mayShareByte)))
      (.record 1 1 [(⟨0, some 0⟩, flag), (⟨0, some 0⟩, flag)])))
  require "packing cannot bypass addressable storage policy"
    (!(validate .natural 2 (.record [integer .w1])
      (.record 1 1 [(⟨0, some 0⟩, flag)])))
  require "validator rejects a different scalar kind at the same offset"
    (!(validate .natural 2 (.record [integer .w1])
      (.record 1 1 [(⟨0, none⟩, word)])))
  let source := Schema.record [(.addressable, .record [integer .w8])]
  let invalidChild := Layout.record 0 1 [(⟨0, none⟩, word)]
  require "validator rejects a field outside its nested record"
    (!(validate .natural 3 source (.record 0 1 [(⟨0, none⟩, invalidChild)])))
  let deep := (List.range 12).foldl (fun child _ => Schema.record [(.addressable, child)])
    (.integer (.unsigned .w64))
  let deepLayout ← expectPlan deep 8 8
  expectField deepLayout (List.replicate 12 0) 0 none 64
  IO.println "Automatic layout regressions passed"

def runCrossBoundary : IO Unit := do
  let tail : IntegerType := .unsigned ⟨14, by decide, by decide⟩
  let middle : IntegerType := .signed ⟨31, by decide, by decide⟩
  let head : IntegerType := .unsigned ⟨35, by decide, by decide⟩
  let maximum : IntegerType := .unsigned ⟨65535, by decide, by decide⟩
  let crossing : IntegerType := .unsigned ⟨33, by decide, by decide⟩
  let short : IntegerType := .unsigned .w2
  let schema := Schema.record ([tail, middle, head].map fun kind => (.mayShareByte, .integer kind))
  let some planned := planVerified .natural schema
    | throw (IO.userError "cross-boundary record planning failed")
  require "reordered wide fields occupy ten bytes" (planned.val.size == 10 && planned.val.alignment == 1)
  expectField planned.val [2] 0 (some 0) 35
  expectField planned.val [1] 4 (some 3) 31
  expectField planned.val [0] 8 (some 2) 14
  let image : Image planned.val.size := fun _ => 255
  let some changed := writeInteger planned.property [1] image ⟨middle, BitVec.ofNat 31 (2^30)⟩
    | throw (IO.userError "cross-boundary signed minimum write failed")
  require "signed minimum round-trips and preserves both neighbors"
    ((readInteger planned.property [1] changed).any (fun v => v.2.toInt == -(2^30)) &&
      (readInteger planned.property [0] changed).any (fun v => v.2.toNat == 2^14 - 1) &&
      (readInteger planned.property [2] changed).any (fun v => v.2.toNat == 2^35 - 1))
  let .record _ _ [tailSlot, midSlot, headSlot] := planned.val
    | throw (IO.userError "cross-boundary fixture lost fields")
  require "forged overlapping bit interval is rejected"
    (!validate .natural 2 schema (.record 10 1 [(⟨8, some 1⟩, tailSlot.2), midSlot, headSlot]))
  require "truncated wide record is rejected"
    (!validate .natural 2 schema (.record 9 1 [tailSlot, midSlot, headSlot]))
  let large := Schema.record ([maximum, crossing, short].map fun kind => (.mayShareByte, .integer kind))
  let some packed := planVerified .natural large
    | throw (IO.userError "maximum-width record planning failed")
  require "maximum-width packed record has 8197 bytes" (packed.val.size == 8197)
  expectField packed.val [1] 8191 (some 7) 33
  let image : Image packed.val.size := fun _ => 255
  let some changed := writeInteger packed.property [1] image ⟨crossing, 0⟩
    | throw (IO.userError "write across the maximum-width field boundary failed")
  require "maximum-width payload and the following field survive a shared-byte write"
    ((readInteger packed.property [0] changed).any (fun v => v.2.toNat == 2^65535 - 1) &&
      (readInteger packed.property [1] changed).any (fun v => v.2.toNat == 0) &&
      (readInteger packed.property [2] changed).any (fun v => v.2.toNat == 3))
  require "byte-window decoding spans maximum and unaligned widths"
    ((changed.readBytes 0 65535).toNat == 2^65535 - 1 &&
      (changed.readBytes 65535 33).toNat == 0 &&
      (changed.readBytes (65535 + 33) 2).toNat == 3)
  let some cleared := writeInteger packed.property [0] image ⟨maximum, 0⟩
    | throw (IO.userError "maximum-width store failed")
  require "maximum-width store round-trips and preserves the shared high bit"
    ((readInteger packed.property [0] cleared).any (fun v => v.2.toNat == 0) &&
      (readInteger packed.property [1] cleared).any (fun v => v.2.toNat == 2^33 - 1))
  IO.println "Cross-boundary integer layout regressions passed"

def runPackedNested : IO Unit := do
  let byte := integer .w8 .mayShareByte
  let wide : IntegerType := .unsigned ⟨17, by decide, by decide⟩
  let nested := Schema.record [byte, byte]
  let schema := Schema.record [integer .w1 .mayShareByte,
    (.mayShareByte, nested), (.mayShareByte, .integer wide)]
  let some planned := planVerified .natural schema
    | throw (IO.userError "could not plan nested packed layout")
  require "nested product occupies 16 consecutive bits inside a five-byte record"
    (planned.val.size == 5 && planned.val.alignment == 1)
  expectField planned.val [1] 2 (some 1) 16
  expectField planned.val [1, 0] 2 (some 1) 8
  expectField planned.val [1, 1] 3 (some 1) 8
  let image : Image planned.val.size := fun _ => 255
  let some written := writeInteger planned.property [1, 0] image ⟨.unsigned .w8, 0⟩
    | throw (IO.userError "nested packed path write failed")
  require "writing a nested child preserves its peer and the preceding field's shared byte"
    ((readInteger planned.property [1, 0] written).any (fun value => value.2.toNat == 0) &&
      (readInteger planned.property [1, 1] written).any (fun value => value.2.toNat == 255) &&
      (readInteger planned.property [2] written).any (fun value => value.2.toNat == 2^17 - 1))
  let requiresAddress := Schema.record [(.addressable, byte.2), byte]
  let guarded := Schema.record [integer .w1 .mayShareByte,
    (.mayShareByte, requiresAddress), (.mayShareByte, .integer wide)]
  let some guardedLayout := plan .natural guarded
    | throw (IO.userError "could not lay out nested addressable field")
  require "an addressable descendant prevents unaligned embedding of its parent"
    ((resolve guardedLayout [1]).any fun (place, _) => place.bitOffset.isNone)
  let oneWord := Schema.record [(.mayShareByte, .integer (.unsigned .w64))]
  let tiePreservesAlign ← expectPlan (.record [(.addressable, oneWord), integer .w1 .mayShareByte]) 16 8
  expectField tiePreservesAlign [0, 0] 0 none 64
  expectField tiePreservesAlign [1] 8 none 1
  let embeddedWord ← expectPlan (.record [(.mayShareByte, oneWord), integer .w1 .mayShareByte]) 9 1
  expectField embeddedWord [0, 0] 0 (some 0) 64
  expectField embeddedWord [1] 8 (some 0) 1
  let withUnit := Schema.record [(.mayShareByte, .integer (.unsigned .w5)),
    (.mayShareByte, .fixed 0 ⟨0, 1⟩)]
  let embedded ← expectPlan (.record [(.mayShareByte, .fixed 35 ⟨8, 8⟩),
    (.mayShareByte, withUnit)]) 5 1
  require "zero-width descendants do not prevent embedding"
    ((resolve embedded [1, 1]).any fun field =>
      field.1.bitStart == 40 && field.2.bits == 0 && field.bytes == 0)
  require "a zero-width value cannot claim a non-empty addressable slot"
    (plan .natural (.record [(.mayShareByte, .fixed 0 ⟨2, 2⟩)])).isNone
  IO.println "Cross-boundary nested record regressions passed"

def runPackedCodecs : IO Unit := do
  let readingSpec : ADTLayout.CompactADT :=
    ⟨2, 32, [⟨0, 0⟩, ⟨1, 32⟩, ⟨2, 13⟩]⟩
  have readingValid : readingSpec.Valid := by
    simp [readingSpec, ADTLayout.CompactADT.Valid]
  let reading := PackedCodec.tagged readingSpec readingValid
  let readingWithStatus := (PackedCodec.raw 5).product (reading.product (PackedCodec.raw 2))
  let schema := Schema.record [(.mayShareByte, .fixed 3 ⟨1, 1⟩),
    (.mayShareByte, .fixed 41 ⟨8, 8⟩), (.mayShareByte, .fixed 43 ⟨8, 8⟩)]
  let some planned := planVerified .natural schema
    | throw (IO.userError "could not plan record with a fixed-width product")
  require "fixed-width product layout uses eleven bytes" (planned.val.size == 11)
  let some field := PackedValueField.resolve planned.property [1] 41
    | throw (IO.userError "could not resolve the product interval")
  let some header := PackedValueField.resolve planned.property [0] 3
    | throw (IO.userError "could not resolve the header interval")
  require "the product and its header have unaligned offsets" (field.start == 43 && header.start == 84)
  require "resolution rejects a codec of the wrong width"
    (PackedValueField.resolve planned.property [1] 42).isNone
  let image : Image planned.val.size := fun _ => 255
  let readingValue : ADTLayout.CompactValue readingSpec :=
    ⟨1, 0x7fc00001, ⟨⟨1, 32⟩, by simp [readingSpec], rfl, by decide⟩⟩
  let written := field.store readingWithStatus image (21, readingValue, 2)
  require "unaligned nested product preserves a floating-point NaN payload"
    ((field.load readingWithStatus written).any fun (status, variant, flag) =>
      status == 21 && variant.tag == 1 && variant.payload == 0x7fc00001 && flag == 2)
  require "unaligned product store preserves its shared header byte"
    (header.load (.raw 3) written == some 7)
  require "tag decoder rejects an unused tag"
    (reading.decode 3).isNone
  require "tag decoder rejects a payload above its variant width"
    (reading.decode (BitVec.ofNat 34 (2 + 4 * 2^13))).isNone
  let innerSpec : ADTLayout.CompactADT := ⟨2, 0, [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩]⟩
  have innerValid : innerSpec.Valid := by
    simp [innerSpec, ADTLayout.CompactADT.Valid]
  let inner := PackedCodec.tagged innerSpec innerValid
  let wrapperSpec : ADTLayout.CompactADT := ⟨0, 2, [⟨0, 2⟩]⟩
  have wrapperValid : wrapperSpec.Valid := by
    simp [wrapperSpec, ADTLayout.CompactADT.Valid]
  let wrapped := (PackedCodec.tagged wrapperSpec wrapperValid).refine fun variant =>
    (inner.decode (BitVec.ofNat 2 variant.payload)).isSome = true
  require "variant payload refinement rejects an invalid tag within the width bound"
    ((wrapped.decode 3).isNone && (wrapped.decode 2).isSome)
  let checkNested := PackedType.tagged [.tagged [.raw 0, .raw 0, .raw 0]]
  require "declared nested variant shape accepts the third tag and rejects the spare code"
    (checkNested.check 2 && !checkNested.check 3)
  let signedRange := PackedType.range .w4 true (-3) 3
  require "signed interval codec accepts negative three and rejects negative four"
    (signedRange.check 13 && !signedRange.check 12)
  let idle : ADTLayout.CompactValue readingSpec :=
    ⟨0, 0, ⟨⟨0, 0⟩, by simp [readingSpec], rfl, by decide⟩⟩
  let replaced := field.store readingWithStatus written (21, idle, 2)
  require "variant replacement initializes unused payload bits and preserves its sibling"
    ((field.load readingWithStatus replaced).any (fun (_, variant, flag) =>
      variant.tag == 0 && variant.payload == 0 && flag == 2) &&
      header.load (.raw 3) replaced == some 7)
  let longSchema := Schema.record [(.mayShareByte, .fixed 65537 ⟨8208, 16⟩),
    (.mayShareByte, .fixed 15 ⟨2, 2⟩)]
  let long ← expectPlan longSchema 8194 1
  expectField long [1] 8192 (some 1) 15
  IO.println "Cross-boundary product and tagged codec regressions passed"

def runPackedRecordMachine : IO Unit := do
  let measurement := PackedType.tagged [.raw 0, .raw 32, .raw 13]
  let schema := PackedSchema.record [(.mayShareByte, .value (.raw 3) ⟨1, 1⟩),
    (.mayShareByte, .value measurement ⟨8, 8⟩),
    (.mayShareByte, .value (.raw 35) ⟨8, 8⟩)]
  let some record := PackedRecord.plan .natural schema 0
    | throw (IO.userError "could not plan packed measurement record")
  let values : List Nat → Option Nat
    | [0] => some 7
    | [1] => some (1 + 4 * 0x7fc00001)
    | [2] => some (2^35-1)
    | _ => none
  require "packed measurement record uses nine bytes"
    (record.layout.size == 9 && record.layout.alignment == 1)
  require "initialization rejects a missing declared leaf"
    (record.allocate {} (fun path => if path = [0] then none else values path)).isNone
  require "initialization rejects an invalid tag"
    (record.allocate {} (fun path => if path = [1] then some 3 else values path)).isNone
  let some memory := record.allocate { observations := [0xde, 0xad] } values
    | throw (IO.userError "could not initialize packed measurement record")
  let some (reading, borrowed) := memory.openScope [1] .shared
    | throw (IO.userError "could not open measurement view")
  require "logical sibling access is invalid even when the physical byte is reserved"
    (borrowed.readInScope reading [0]).isNone
  require "an incompatible sibling view cannot share the measurement's last byte"
    (borrowed.openScope [0] .exclusive).isNone
  let some payload := borrowed.openPayloadInScope reading [1]
    | throw (IO.userError "could not project active measurement payload")
  require "authorized measurement read preserves raw float bits"
    (borrowed.readPayloadInScope reading payload == some 0x7fc00001)
  let some released := borrowed.closeScope reading
    | throw (IO.userError "could not close measurement view")
  let some (writing, reserved) := released.openScope [] .exclusive
    | throw (IO.userError "could not reserve record for tag replacement")
  require "closed scope identity cannot authorize subsequent reads"
    (reserved.readInScope reading [1]).isNone
  let some updated := reserved.writeInScope writing [1] (1 + 4 * 0x80000000)
    | throw (IO.userError "could not replace measurement")
  require "a masked store reads exactly its two boundary bytes before older observations"
    (updated.heap.observations == [0xef, 0x2f, 0xde, 0xad])
  require "the previous payload is invalid even after replacement by the same tag"
    (updated.readPayloadInScope writing payload).isNone
  require "byte-machine writes preserve both logical neighbors"
    (updated.readInScope writing [0] == some 7 &&
      updated.readInScope writing [2] == some (2^35-1))
  let some current := updated.openPayloadInScope writing [1]
    | throw (IO.userError "could not project replacement measurement payload")
  require "replacement payload reads back signed zero's full bit pattern"
    (updated.readPayloadInScope writing current == some 0x80000000)
  IO.println "Cross-boundary typed record machine regressions passed"

def runAccess : IO Unit := do
  let inner := Schema.record [integer .w4 .mayShareByte, integer .w4 .mayShareByte,
    integer .w1 .mayShareByte, integer .w16]
  let schema := Schema.record [integer .w8, (.addressable, inner), integer .w8]
  let some planned := planVerified .natural schema
    | throw (IO.userError "could not plan the accessor fixture")
  let image : Image planned.val.size := fun _ => BitVec.ofNat 8 128
  let some word := writeInteger planned.property [1, 3] image
      ⟨.unsigned .w16, BitVec.ofNat 16 4660⟩
    | throw (IO.userError "nested wide value write failed")
  let some low := writeInteger planned.property [1, 0] word
      ⟨.unsigned .w4, BitVec.ofNat 4 10⟩
    | throw (IO.userError "first packed nibble write failed")
  require "first nibble write must preserve the high nibble"
    ((readInteger planned.property [1, 1] low).any fun value => value.2.toNat == 8)
  let some high := writeInteger planned.property [1, 1] low
      ⟨.unsigned .w4, BitVec.ofNat 4 5⟩
    | throw (IO.userError "second packed nibble write failed")
  require "second nibble write must preserve the low nibble"
    ((readInteger planned.property [1, 0] high).any fun value => value.2.toNat == 10)
  let some flagged := writeInteger planned.property [1, 2] high
      ⟨.unsigned .w1, BitVec.ofNat 1 1⟩
    | throw (IO.userError "packed flag write failed")
  require "physical image must preserve sibling bits and unrelated bytes"
    (flagged.toBytes == [52, 18, 90, 129, 128, 128])
  require "read nested word in little-endian order after packed writes"
    ((readInteger planned.property [1, 3] flagged).any fun value =>
      value.1 == .unsigned .w16 && value.2.toNat == 4660)
  require "reject mismatched signedness at the same width"
    (writeInteger planned.property [1, 0] flagged ⟨.signed .w4, BitVec.ofNat 4 10⟩).isNone
  require "record paths require a field type"
    (readInteger planned.property [1] flagged).isNone
  require "missing nested integer field"
    (readInteger planned.property [1, 5] flagged).isNone
  require "byte image round trip" ((Image.ofBytes [14, 19, 0]).toBytes == [14, 19, 0])
  IO.println "8 nested integer accessor regressions passed"

end Aethel.AutomaticLayout.Tests
