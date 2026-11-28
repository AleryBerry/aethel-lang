import Aethel.Representation

namespace Aethel.Representation.Tests

open Functional Core Structured CoreAST Representation ADTLayout

private def runDenseDataTests : IO Unit := do
  let three := CoreType.sum .bool .unit
  let variant : DenseData three 3 := .sum .bool .unit
  let payload := CoreType.prod (.prod three three) (.prod three (.prod three three))
  let some schema := DenseData.ofType (.sum payload .unit) |
    throw (IO.userError "finite nested sum has no layout")
  let field : DenseDataField 1 (.sum payload .unit) :=
    ⟨244, .sum (.prod (.prod variant variant) (.prod variant (.prod variant variant))) .unit, ⟨0, by decide⟩⟩
  let absent := CoreExpr.inject false (payload, .unit) .unit
  let initial : AutomaticLayout.Image 1 := fun _ => 255
  let some encoded := field.store initial absent | throw (IO.userError "cannot encode vacant variant")
  if schema.1 != 244 || minTagBits schema.1 != 8 || (encoded 0).toNat != 243 || field.load encoded != some absent then
    throw (IO.userError "nested sum must fit into the spare codes of a single byte")
  if (field.load initial).isSome then
    throw (IO.userError "unused nested sum code decoded as a typed value")
  let mixed : DenseDataField 2 (.sum (.prod .byte .bool) .byte) :=
    ⟨768, .sum (.prod .byte .bool) .byte, ⟨3, by decide⟩⟩
  let image : AutomaticLayout.Image 2 := fun _ => 255
  let error := CoreExpr.inject false (.prod .byte .bool, .byte) (.int false 8 255)
  let ok := CoreExpr.inject true (.prod .byte .bool, .byte) (.pair (.int false 8 255) (.bool true))
  let some failed := mixed.store image error | throw (IO.userError "cannot encode the error payload")
  let some recovered := mixed.store failed ok | throw (IO.userError "cannot encode the recovered payload")
  if (failed.readBits 3 10).toNat != 767 || (recovered.readBits 3 10).toNat != 511 ||
      mixed.load recovered != some ok || (recovered.readBits 0 3).toNat != 7 ||
      (recovered.readBits 13 3).toNat != 7 then
    throw (IO.userError "changing a typed variant across bytes disturbed its payload or neighbors")
  let wrong := CoreExpr.inject true (.prod .byte .bool, .unit) (.pair (.int false 8 255) (.bool true))
  if (mixed.store image wrong).isSome ||
      (DenseData.ofType (.sum (.arrow .byte .byte .empty) .unit)).isSome then
    throw (IO.userError "dense layout accepted the wrong variant signature or a closure")

def runRepresentationTests : IO Unit := do
  -- Test 1: Primitives representation
  have hUnit : Represents .unit .unit [] := .unit
  have hBool : Represents (.bool true) .bool [1] := .bool true
  have hByte : Represents (.int false 8 42) CoreType.byte [42] := .byte 42
  have hUInt16 : Represents (.int false 16 1000) CoreType.uint16 [splitLow 1000, splitHigh 1000] := .uint16 1000
  have _ := hUnit; have _ := hBool; have _ := hByte; have _ := hUInt16

  -- Test 2: Products representation
  have hPair : Represents (.pair (.int false 8 10) (.int false 8 20)) (.prod .byte .byte) [10, 20] :=
    .prod (.byte 10) (.byte 20)
  have _ := hPair

  -- Test 3: ADT representation
  have hADT : Represents (.adt 5 (.int false 8 99)) (.adt 5 .byte) [5, 99] :=
    .adt 5 (.byte 99)
  have _ := hADT

  -- Test 4: Representation length check
  if typeSize (.prod .byte .byte) != some 2 || [10, 20].length != 2 then
    throw (IO.userError "pair length check failed")
  have _hLenThm : ∃ sz, typeSize (.prod .byte .byte) = some sz ∧ [10, 20].length = sz :=
    represents_length hPair

  -- Test 5: Decode booleans
  if decodeBool [1] != some (.bool true) then
    throw (IO.userError "decodeBool true failed")
  if decodeBool [0] != some (.bool false) then
    throw (IO.userError "decodeBool false failed")

  -- Test 6: Decode byte and UInt16
  if decodeByte [42] != some (.int false 8 42) then
    throw (IO.userError "decodeByte failed")
  let u16Val : UInt16 := 513 -- 1 + 2 * 256 -> [1, 2]
  if decodeUInt16LE_expr [splitLow u16Val, splitHigh u16Val] != some (.int false 16 513) then
    throw (IO.userError "decodeUInt16LE_expr failed")

  -- Test 7: Allocation simulation
  let emptyState : State := ⟨[], [], [], [], []⟩
  have hAlloc := rep_alloc_simulation emptyState 1 (.int false 8 77) CoreType.byte [77] (.byte 77)
  let stateWith1 := emptyState.addAllocation 1 [77]
  if stateWith1.byte ⟨1, 0⟩ != some 77 then
    throw (IO.userError "allocation simulation did not store byte 77")

  -- Test 8: Allocation preserves other
  let stateWith12 := stateWith1.addAllocation 2 [88]
  have hPresOther := rep_alloc_preserves_other stateWith1 2 1 [88] (by decide) 0 (.int false 8 77) CoreType.byte hAlloc
  if stateWith12.byte ⟨1, 0⟩ != some 77 || stateWith12.byte ⟨2, 0⟩ != some 88 then
    throw (IO.userError "allocation preserves other failed")

  -- Test 9: Read byte simulation
  have hReadByteThm : ∃ v : UInt8, CoreExpr.int false 8 77 = .int false 8 (Int.ofNat v.toNat) ∧
    stateWith1.byte ⟨1, 0⟩ = some v := rep_read_byte_simulation stateWith1 1 0 (.int false 8 77) hAlloc
  have _ := hReadByteThm

  -- Test 10: Read UInt16 simulation
  let stateU16 := emptyState.addAllocation 10 [splitLow u16Val, splitHigh u16Val]
  have hAllocU16 := rep_alloc_simulation emptyState 10 (.int false 16 513) CoreType.uint16 [splitLow u16Val, splitHigh u16Val] (.uint16 u16Val)
  have hReadU16Thm : ∃ v : UInt16, CoreExpr.int false 16 513 = .int false 16 (Int.ofNat v.toNat) ∧
    stateU16.byte ⟨10, 0⟩ = some (splitLow v) ∧ stateU16.byte ⟨10, 1⟩ = some (splitHigh v) :=
    rep_read_uint16_simulation stateU16 10 0 (.int false 16 513) hAllocU16
  have _ := hReadU16Thm
  if stateU16.byte ⟨10, 0⟩ != some (splitLow u16Val) || stateU16.byte ⟨10, 1⟩ != some (splitHigh u16Val) then
    throw (IO.userError "read uint16 bytes failed")

  -- Test 11: Write byte simulation
  let stateWritten := stateWith1.store ⟨1, 0⟩ 99
  have hWriteSim := rep_write_byte_simulation stateWith1 1 0 (.int false 8 77) 99 hAlloc
  have _ := hWriteSim
  if stateWritten.byte ⟨1, 0⟩ != some 99 then
    throw (IO.userError "write byte simulation failed to update byte")

  -- Test 12: Write preserves other allocation
  have hWriteOther := rep_write_preserves_other stateWith12 ⟨2, 0⟩ 123 1 0 (.int false 8 77) CoreType.byte (by decide) hPresOther
  have _ := hWriteOther

  -- Test 13: Destroy simulation
  let stateDestroyed2 := stateWith12.removeOwner 2
  have hDestroyPres := (rep_destroy_simulation stateWith12 2 1 (by decide) 0 (.int false 8 77) CoreType.byte).mpr hPresOther
  have _ := hDestroyPres
  if stateDestroyed2.allocation 2 != none then
    throw (IO.userError "removeOwner did not clear allocation 2")
  if stateDestroyed2.byte ⟨1, 0⟩ != some 77 then
    throw (IO.userError "destroying owner 2 altered owner 1")

  runDenseDataTests
  IO.println "17 logical-to-physical representation refinement regressions passed"

end Aethel.Representation.Tests
