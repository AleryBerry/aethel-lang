import Aethel.LayoutAccess

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
