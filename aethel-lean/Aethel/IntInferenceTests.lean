import Aethel.IntInference
import Aethel.LayoutAccess
import Aethel.MIRValidator

namespace Aethel.IntInference.Tests

open Aethel Aethel.AutomaticLayout Aethel.MIRValidator

private def require (msg : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError msg)

private def runParsingAndABILayoutTests : IO Unit := do
  -- Arbitrary bit widths and rejections
  require "parse u1" (IntegerType.parse? "u1" == some (.unsigned .w1))
  require "parse i7" (IntegerType.parse? "i7" == some (.signed .w7))
  require "parse u3" (IntegerType.parse? "u3" == some (.unsigned .w3))
  require "parse i24" (IntegerType.parse? "i24" == some (.signed .w24))
  require "parse u128" (IntegerType.parse? "u128" == some (.unsigned .w128))
  require "parse u65535"
    ((IntegerType.parse? "u65535").any fun ty => ty.bits == 65535)
  require "reject u0" (IntegerType.parse? "u0").isNone
  require "reject i0" (IntegerType.parse? "i0").isNone
  require "reject leading zero u08" (IntegerType.parse? "u08").isNone
  require "reject leading zero i07" (IntegerType.parse? "i07").isNone
  require "reject u65536" (IntegerType.parse? "u65536").isNone
  require "reject trailing garbage u7x" (IntegerType.parse? "u7x").isNone

  -- Literal round-trips for non-power-of-two widths
  let i7 : IntegerType := .signed .w7
  let u3 : IntegerType := .unsigned .w3
  require "i7 fits -64..63" (decide (i7.Fits (-64) ∧ i7.Fits 63 ∧ ¬i7.Fits (-65) ∧ ¬i7.Fits 64))
  require "u3 fits 0..7" (decide (u3.Fits 0 ∧ u3.Fits 7 ∧ ¬u3.Fits (-1) ∧ ¬u3.Fits 8))
  if h : i7.Fits (-42) then
    require "i7 signed literal round-trip" (((IntegerType.signed .w7).literalValue (-42) h).toInt == -42)
  else
    throw (IO.userError "i7 should fit -42")

  -- Natural ABI alignment & size for arbitrary payloads
  require "i7 slot 1/1" (TargetIntegerABI.natural.slot i7 == ⟨1, 1⟩)
  require "i24 slot 4/4" (TargetIntegerABI.natural.slot (.signed .w24) == ⟨4, 4⟩)
  require "u48 slot 8/8" (TargetIntegerABI.natural.slot (.unsigned .w48) == ⟨8, 8⟩)
  require "u128 slot 16/16" (TargetIntegerABI.natural.slot (.unsigned .w128) == ⟨16, 16⟩)
  require "u256 slot 32/16" (TargetIntegerABI.natural.slot (.unsigned .w256) == ⟨32, 16⟩)

  -- First-fit-decreasing sub-byte packing for arbitrary widths
  let pair71 := Schema.record [(.mayShareByte, .integer i7), (.mayShareByte, .integer (.unsigned .w1))]
  let some plan71 := planVerified .natural pair71
    | throw (IO.userError "i7 + u1 plan failed")
  require "i7 + u1 packs into 1 byte" (plan71.val.size == 1 && plan71.val.alignment == 1)

  let pair35 := Schema.record [(.mayShareByte, .integer u3), (.mayShareByte, .integer (.unsigned .w5))]
  let some plan35 := planVerified .natural pair35
    | throw (IO.userError "u3 + u5 plan failed")
  require "u3 + u5 packs into 1 byte" (plan35.val.size == 1 && plan35.val.alignment == 1)

  let ffd := Schema.record
    [ (.mayShareByte, .integer i7)
    , (.mayShareByte, .integer (.unsigned .w5))
    , (.mayShareByte, .integer u3)
    , (.mayShareByte, .integer (.unsigned .w1)) ]
  let some planFfd := planVerified .natural ffd
    | throw (IO.userError "FFD [i7, u5, u3, u1] plan failed")
  require "FFD packs [i7, u5, u3, u1] into exact 2 bytes"
    (planFfd.val.size == 2 && planFfd.val.alignment == 1)

  -- Byte-image round-trip across arbitrary packed widths preserving sibling bits
  let img0 : Image planFfd.val.size := fun _ => BitVec.ofNat 8 0
  let some img1 := writeInteger planFfd.property [0] img0 ⟨i7, BitVec.ofInt 7 (-25)⟩
    | throw (IO.userError "write [0] i7 failed")
  let some img2 := writeInteger planFfd.property [1] img1 ⟨.unsigned .w5, BitVec.ofNat 5 19⟩
    | throw (IO.userError "write [1] u5 failed")
  let some img3 := writeInteger planFfd.property [2] img2 ⟨u3, BitVec.ofNat 3 6⟩
    | throw (IO.userError "write [2] u3 failed")
  let some img4 := writeInteger planFfd.property [3] img3 ⟨.unsigned .w1, BitVec.ofNat 1 1⟩
    | throw (IO.userError "write [3] u1 failed")
  match readInteger planFfd.property [0] img4,
        readInteger planFfd.property [1] img4,
        readInteger planFfd.property [2] img4,
        readInteger planFfd.property [3] img4 with
  | some ⟨k0, v0⟩, some ⟨k1, v1⟩, some ⟨k2, v2⟩, some ⟨k3, v3⟩ =>
    require "i7 value preserved" (k0 == i7 && v0.toInt == -25)
    require "u5 value preserved" (k1 == .unsigned .w5 && v1.toNat == 19)
    require "u3 value preserved" (k2 == u3 && v2.toNat == 6)
    require "u1 value preserved" (k3 == .unsigned .w1 && v3.toNat == 1)
  | _, _, _, _ => throw (IO.userError "FFD readback failed")

  -- MIRValidator accepts arbitrary bit-width integer fields
  let mirText :=
    "mir_version 1\n" ++
    "record ArbitrarySensor 8\n" ++
    "  field i7\n" ++
    "  field u1\n" ++
    "  field i24\n" ++
    "end_record\n"
  match validateMIRText mirText with
  | .ok cert =>
    require "MIRValidator validates i7/u1/i24 record"
      (cert == ⟨1, [("ArbitrarySensor", 8)], 0⟩)
  | .error err =>
    throw (IO.userError s!"MIRValidator rejected i7/u1/i24 record: {err}")

private def runInferenceAndOverflowTests : IO Unit := do
  -- Automatic minimum bit-width synthesis from ranges
  let rHealth : IntRange := ⟨0, 100, by decide⟩
  require "range 0..100 infers u7" (inferIntegerType rHealth == some (.unsigned .w7))
  let rTemp : IntRange := ⟨-50, 50, by decide⟩
  require "range -50..50 infers i7" (inferIntegerType rTemp == some (.signed .w7))
  let rI4Edge : IntRange := ⟨-8, 7, by decide⟩
  require "range -8..7 infers i4" (inferIntegerType rI4Edge == some (.signed .w4))
  let rU3Edge : IntRange := ⟨0, 7, by decide⟩
  require "range 0..7 infers u3" (inferIntegerType rU3Edge == some (.unsigned .w3))
  let rPosSigned : IntRange := ⟨-1, 0, by decide⟩
  require "range -1..0 infers i1" (inferIntegerType rPosSigned == some (.signed .w1))

  -- Unspecified arithmetic widens automatically at compile time (zero overflow)
  let Γ : Nat → Option IntRange
    | 0 => some rHealth
    | 1 => some (IntRange.ofType (.signed .w7)) -- -64..63
    | _ => none
  match inferExprType Γ (.mul (.var 0) (.var 1)) with
  | .ok (rProd, tyProd) =>
    require "health(0..100) * i7(-64..63) range is -6400..6300 and infers i14"
      (rProd.lo == -6400 && rProd.hi == 6300 && tyProd.bits == 14 &&
        tyProd == .signed (⟨14, by decide, by decide⟩ : IntegerWidth))
  | .error err =>
    throw (IO.userError s!"inference failed: {repr err}")

  -- Compile-time overflow rejection vs branch narrowing acceptance
  let envU8 := EnvValid.ofTypes fun
    | 0 | 1 => some (.unsigned .w8)
    | _ => none
  match checkExpr envU8 (.checkedCast (.unsigned .w8) (.add (.var 0) (.var 1))) with
  | .error (.potentialOverflow (.unsigned _) 0 510) => pure ()
  | other => throw (IO.userError s!"expected u8 overflow rejection, got {repr other}")

  -- Guarded narrowing (`a ≤ 100`, `b ≤ 155`) makes `checkedCast u8 (a + b)` verify statically
  let some aNarrow := (IntRange.ofType (.unsigned .w8)).narrowUpper? 100
    | throw (IO.userError "narrowUpper failed")
  let some bNarrow := (IntRange.ofType (.unsigned .w8)).narrowUpper? 155
    | throw (IO.userError "narrowUpper failed")
  let envNarrow : Nat → Option IntRange
    | 0 => some aNarrow
    | 1 => some bNarrow
    | _ => none
  match checkExpr envNarrow (.checkedCast (.unsigned .w8) (.add (.var 0) (.var 1))) with
  | .ok rSum =>
    require "guarded u8 add fits exactly 0..255" (rSum.lo == 0 && rSum.hi == 255)
  | .error err =>
    throw (IO.userError s!"guarded u8 add unexpectedly failed: {repr err}")

  -- Saturating and wrapping casts are always total and never fail compile-time checking
  match inferExprType envU8 (.satCast (.signed .w7) (.add (.var 0) (.var 1))) with
  | .ok (_, tySat) =>
    require "satCast i7 yields i7 range" (tySat == .signed .w7)
  | .error err =>
    throw (IO.userError s!"satCast failed: {repr err}")
  require "clampToType i7 saturates 500 to 63" (clampToType (.signed .w7) 500 == 63)
  require "clampToType i7 saturates -500 to -64" (clampToType (.signed .w7) (-500) == -64)
  require "wrapToType u7 wraps 130 to 2" (wrapToType (.unsigned .w7) 130 == 2)
  require "checkedAdd i7 rejects 50+30" (checkedAdd (.signed .w7) 50 30).isNone
  require "checkedAdd i7 accepts 40+23" (checkedAdd (.signed .w7) 40 23 == some 63)

def run : IO Unit := do
  runParsingAndABILayoutTests
  runInferenceAndOverflowTests
  IO.println "Arbitrary bit-width integer, auto-sizing, FFD packing, and overflow-prevention regressions passed"

end Aethel.IntInference.Tests
