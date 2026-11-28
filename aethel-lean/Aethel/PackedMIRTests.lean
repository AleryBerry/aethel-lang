import Aethel.PackedMIRSchedule

namespace Aethel.PackedMIR.Tests

open AutomaticLayout

private def contents : Module :=
  { version
    schema := .record [
      (.mayShareByte, .value (.raw 3) ⟨1, 1⟩),
      (.mayShareByte, .value (.tagged [.raw 0, .raw 32, .raw 13]) ⟨8, 8⟩),
      (.mayShareByte, .value (.raw 35) ⟨8, 8⟩)]
    layout := ⟨9, 1, [
      ⟨[0], 8, some 5, 3, 1⟩,
      ⟨[1], 4, some 3, 34, 5⟩,
      ⟨[2], 0, some 0, 35, 5⟩]⟩
    initial := [([0], 7), ([1], 1 + 4 * 0x7fc00001), ([2], 2^35-1)]
    operations := [
      .openScope 0 [] .exclusive,
      .capturePayload 0 0 [1] [4, 5, 6, 7, 8],
      .loadPayload 0 0 [4, 5, 6, 7, 8],
      .store 0 [1] [4, 5, 6, 7, 8] 0,
      .forgetPayload 0,
      .load 0 [0] [8],
      .load 0 [2] [0, 1, 2, 3, 4],
      .closeScope 0] }

private def require (name : String) (passed : Bool) : IO Unit :=
  unless passed do throw (IO.userError name)

example (image : Image 0) : ¬ image.InAllocation 0 ({} : Core.State) := by
  simp [Image.InAllocation, Core.ResourceState.extent, Core.State.resources]

def run : IO Unit := do
  let encoded := (Lean.toJson contents).compress
  let .ok parsed := parse encoded
    | throw (IO.userError "packed MIR JSON round-trip failed")
  let .ok accepted := validate parsed
    | throw (IO.userError "packed MIR rejected the typed measurement trace")
  let some program := accepted.kernelProgram
    | throw (IO.userError "packed MIR failed to extract the reference kernel program")
  require "the extracted kernel program rechecks all resources and store bytes"
    (accepted.checkKernelProgram program && Core.verifyResources program)
  let reads := program.countP fun op => match op with | .readView _ => true | _ => false
  let writes := program.countP fun op => match op with | .writeView _ _ => true | _ => false
  require "the kernel program retains payload reads and only the masked write's boundary reads"
    (reads == 18 && writes == 5)
  let .ok edgeTarget := validate { contents with target := ⟨246, 255⟩ }
    | throw (IO.userError "packed MIR rejected the last nine bytes of an 8-bit target")
  let some operands := edgeTarget.kernelTargetOperands 8
    | throw (IO.userError "packed MIR could not resolve the actual word-sized byte operands")
  let emitted := operands.map fun access => (access.address.toNat, access.writeValue)
  let readsAt (addresses : List Nat) := addresses.map fun address => (address, (none : Option UInt8))
  let expected := readsAt [250, 251, 252, 253, 254, 250, 251, 252, 253, 254, 250, 254] ++
    [(250, some 7), (251, some 0), (252, some 0), (253, some 0), (254, some 224)] ++
    readsAt [254, 246, 247, 248, 249, 250]
  require "target operands preserve instruction order and bound both masked edges"
    (emitted == expected && (edgeTarget.kernelTargetOperands 7).isNone)
  let forged := program.map fun op => match op with
    | .writeView view byte => .writeView view (byte + 1)
    | other => other
  require "permission-equivalent corruption of packed store bytes fails certificate checking"
    (Core.verifyResources forged && !(accepted.checkKernelProgram forged))
  require "packed MIR retains the NaN payload and both siblings"
    (accepted.final.observations.reverse == [0x7fc00001, 7, 2^35-1])
  require "the packed record's allocation is destroyed after its scopes close"
    (accepted.dropped.allocation accepted.record.owner).isNone
  require "packed initialization rejects a missing cross-boundary value"
    (accepted.record.allocate {} (fun path => if path == [2] then none else parsed.initialValue path)).isNone
  require "packed initialization rejects an out-of-width value in a shared byte"
    (accepted.record.allocate {} (fun path => if path == [0] then some 8 else parsed.initialValue path)).isNone
  require "packed initialization rejects reuse of a destroyed owner"
    (accepted.record.allocate accepted.dropped parsed.initialValue).isNone
  require "packed MIR rejects the legacy version in its own channel"
    (validate { contents with version := 1 }).isOk.not
  require "packed MIR rejects a forged record stride"
    (validate { contents with layout := { contents.layout with byteCount := 8 } }).isOk.not
  require "packed MIR rejects a field list in physical rather than declaration order"
    (validate { contents with layout := { contents.layout with fields := contents.layout.fields.reverse } }).isOk.not
  let wrongWidth := contents.layout.fields.map fun field =>
    if field.path == [1] then { field with width := 33 } else field
  require "packed MIR rejects a forged width for a cross-boundary leaf"
    (validate { contents with layout := { contents.layout with fields := wrongWidth } }).isOk.not
  let wrongSlot := contents.layout.fields.map fun field =>
    if field.path == [1] then { field with byteCount := 4 } else field
  require "packed MIR rejects a forged byte span for a cross-boundary leaf"
    (validate { contents with layout := { contents.layout with fields := wrongSlot } }).isOk.not
  require "packed MIR rejects a target bound below the record's ending address"
    (validate { contents with target := ⟨4096, 4104⟩ }).isOk.not
  let addressable : Module :=
    { version
      schema := .record [(.addressable, .value (.raw 35) ⟨8, 8⟩)]
      layout := ⟨8, 8, [⟨[0], 0, none, 35, 8⟩]⟩
      initial := [([0], 11)]
      operations := [.openScope 0 [] .shared, .load 0 [0] [0, 1, 2, 3, 4], .closeScope 0] }
  require "addressable storage keeps its target alignment and exact ending address"
    ((validate { addressable with target := ⟨8, 16⟩ }).isOk &&
      (validate { addressable with target := ⟨7, 16⟩ }).isOk.not)
  let some reading := accepted.record.field [1]
    | throw (IO.userError "could not resolve packed array field")
  require "an unaligned store reads only its two masked boundary bytes"
    (reading.2.mergeOffsets == [4, 8])
  let some twoBoundaryEntry := (Op.openScope 0 [] .exclusive).execute { memory := accepted.initial }
    | throw (IO.userError "could not open the two-boundary store scope")
  let some lowBoundary := twoBoundaryEntry.memory.heap.byte ⟨accepted.record.owner, 4⟩
    | throw (IO.userError "missing the two-boundary store's first byte")
  let some highBoundary := twoBoundaryEntry.memory.heap.byte ⟨accepted.record.owner, 8⟩
    | throw (IO.userError "missing the two-boundary store's last byte")
  let plain := twoBoundaryEntry.memory.writeInScopeProgram 0 [1] 0
  let resample := twoBoundaryEntry.memory.writeInScopeProgramFromSamples 0 [1] 0
  let low := lowBoundary.toBitVec
  let high := highBoundary.toBitVec
  require "a store spanning multiple bytes uses both boundary samples in offset order"
    (plain.isSome && decide (resample [low, high] = plain) && decide (resample [high, low] ≠ plain) &&
      decide (resample [low ^^^ 1, high] ≠ plain) && decide (resample [low, high ^^^ 128] ≠ plain))
  let region : PackedArrayRegion accepted.record.layout := ⟨4096, 2, 4114⟩
  require "adjacent rows use separate checked byte footprints"
    (region.addresses 0 reading.2 == some [4100, 4101, 4102, 4103, 4104] &&
      region.addresses 1 reading.2 == some [4109, 4110, 4111, 4112, 4113] &&
      (region.addresses 2 reading.2).isNone)
  let nearLimit : PackedArrayRegion accepted.record.layout := ⟨237, 2, 255⟩
  require "fixed-word row addresses reach the last byte below the exclusive target limit without wrapping"
    (some (reading.2.byteOffsets.map (fun byte => (nearLimit.wordAddress 8 1 byte).toNat)) ==
      nearLimit.addresses 1 reading.2 && nearLimit.addresses 1 reading.2 == some [250, 251, 252, 253, 254])
  let rows : Fin region.count → Image accepted.record.layout.size := fun row _ => if row.val = 0 then 0 else 255
  let image := region.encodeRows rows
  let codec := PackedCodec.raw reading.1.width
  let changed := region.writeValue image 0 reading.2 codec (BitVec.ofNat _ 12345)
  require "a packed array field write round-trips without changing the next row"
    ((region.readValue changed 0 reading.2 codec).any (fun bits => bits.toNat == 12345) &&
      (region.readValue changed 1 reading.2 codec).any (fun bits => bits.toNat == 2^34 - 1))
  let owner : Core.OwnerId := 17
  let some allocated := region.allocateRows {} owner rows
    | throw (IO.userError "the byte kernel rejected a bounded packed array allocation")
  let aliases : Core.Program := (List.range 5).map (fun id => .alias id owner (13 + id) .exclusive)
  let targets : List Structured.AccessTarget := (List.range 5).map Structured.AccessTarget.handle
  let some accessible := Core.run allocated aliases
    | throw (IO.userError "could not authorize the second row's packed field")
  let value := BitVec.ofNat reading.1.width 12345
  let some written := region.writeMachine codec accessible owner 1 reading.2 targets value
    | throw (IO.userError "the byte kernel rejected an authorized packed row store")
  let expectedImage := region.writeValue image 1 reading.2 codec value
  require "the packed array byte kernel agrees with the row image including boundary bits and adjacent rows"
    (region.readMachine codec written owner 1 reading.2 targets == some value &&
      (written.allocation owner).any (fun allocation => allocation.bytes == expectedImage.toBytes) &&
      decide (written.resources = accessible.resources))
  require "packed array accesses reject out-of-bounds rows, another row's handles, and short target limits"
    ((region.writeMachine codec accessible owner 0 reading.2 targets value).isNone &&
      (region.readMachine codec written owner 2 reading.2 targets).isNone &&
      ({ region with limit := 4113 }.allocateRows {} owner rows).isNone)
  let overlapping := contents.layout.fields.map fun field =>
    if field.path == [1] then { field with bitOffset := some 0 } else field
  require "packed MIR rejects a forged overlapping offset even at the correct stride"
    (validate { contents with layout := { contents.layout with fields := overlapping } }).isOk.not
  require "packed MIR rejects a missing shared boundary byte"
    (validate { contents with operations := [
      .openScope 0 [] .exclusive, .store 0 [1] [4, 5, 6, 7] 0, .closeScope 0] }).isOk.not
  require "packed MIR rejects a stale payload after replacing it with the same tag"
    (validate { contents with operations := [
      .openScope 0 [] .exclusive, .capturePayload 0 0 [1] [4, 5, 6, 7, 8],
      .store 0 [1] [4, 5, 6, 7, 8] (1 + 4 * 0x80000000), .loadPayload 0 0 [4, 5, 6, 7, 8],
      .forgetPayload 0, .closeScope 0] }).isOk.not
  require "packed MIR rejects borrowing and accessing a sibling through shared physical bytes"
    (validate { contents with operations := [
      .openScope 0 [1] .shared, .load 0 [0] [8], .closeScope 0] }).isOk.not
  require "packed MIR rejects invalid logical codes at the correct width"
    (validate { contents with operations := [
      .openScope 0 [] .exclusive, .store 0 [1] [4, 5, 6, 7, 8] 3,
      .closeScope 0] }).isOk.not
  require "closing a reborrow restores the parent view"
    (validate { contents with operations := [
      .openScope 0 [] .exclusive, .reborrow 1 0 [1] .shared,
      .load 1 [1] [4, 5, 6, 7, 8], .closeScope 1,
      .store 0 [1] [4, 5, 6, 7, 8] 0, .closeScope 0] }).isOk
  require "packed MIR suspends parent access while its child reborrow is active"
    (validate { contents with operations := [
      .openScope 0 [] .exclusive, .reborrow 1 0 [1] .shared,
      .store 0 [1] [4, 5, 6, 7, 8] 0, .closeScope 1, .closeScope 0] }).isOk.not
  let disjointFork := { contents with operations := [
    .openScope 0 [] .exclusive,
    .fork 0 [⟨[0], [8], some 2⟩, ⟨[2], [0, 1, 2, 3, 4], none⟩],
    .load 0 [0] [8], .closeScope 0] }
  let .ok joined := validate disjointFork
    | throw (IO.userError "packed MIR rejected disjoint fork accesses")
  require "disjoint fork writes and reads agree with their logical fields"
    (joined.final.observations.reverse == [2^35-1, 2])
  let .ok readFirst := validate { disjointFork with operations := [
    .openScope 0 [] .exclusive,
    .fork 0 [⟨[2], [0, 1, 2, 3, 4], none⟩, ⟨[0], [8], some 2⟩],
    .load 0 [0] [8], .closeScope 0] }
    | throw (IO.userError "packed MIR rejected the same fork with its read first")
  require "reordering the read before a disjoint masked store preserves its value"
    (readFirst.final.observations == joined.final.observations)
  let stores : List Task := [⟨[0], [8], some 2⟩, ⟨[2], [0, 1, 2, 3, 4], some 12345⟩]
  let withSchedule (tasks : List Task) := { contents with operations := [
    .openScope 0 [] .exclusive, .fork 0 tasks,
    .load 0 [0] [8], .load 0 [1] [4, 5, 6, 7, 8], .load 0 [2] [0, 1, 2, 3, 4], .closeScope 0] }
  let .ok forward := validate (withSchedule stores)
    | throw (IO.userError "packed MIR rejected separate masked stores in source order")
  let .ok backward := validate (withSchedule stores.reverse)
    | throw (IO.userError "packed MIR rejected separate masked stores in reverse order")
  let forwardBytes := (forward.final.memory.heap.allocation forward.record.owner).map (·.bytes)
  let backwardBytes := (backward.final.memory.heap.allocation backward.record.owner).map (·.bytes)
  require "masked stores in either order preserve their shared logical sibling"
    (forwardBytes.isSome && forwardBytes == backwardBytes &&
      forward.final.observations.reverse == [2, 1 + 4 * 0x7fc00001, 12345] &&
      forward.final.observations == backward.final.observations)
  let some byteProgram := forward.kernelProgram
    | throw (IO.userError "could not extract the disjoint masked fork")
  let setup := byteProgram.takeWhile (fun op => !op.isByteAccess)
  let forkBytes := (byteProgram.drop setup.length).take 8
  let some forkState := (Op.openScope 0 [] .exclusive).execute { memory := forward.initial }
    | throw (IO.userError "could not open the checked fork scope")
  let some [firstTask, secondTask] := tasksKernelPrograms 0 forkState stores
    | throw (IO.userError "the kernel did not emit one instruction group per task")
  let locations := List.map (fun offset : Nat => (⟨forward.record.owner, offset⟩ : ByteLocation))
  let decode := ScopedForkJoin.TaskFootprint.ofProgram forkState.memory.heap.resources
  require "the emitted groups have exactly the checked read and write locations"
    (decide (forkBytes = firstTask ++ secondTask) &&
      decide (decode firstTask = some ⟨locations [8], locations [8]⟩) &&
      decide (decode secondTask = some ⟨locations [4], locations [0, 1, 2, 3, 4]⟩))
  let interleaved := secondTask.take 1 ++ firstTask.take 1 ++ secondTask.drop 1 ++ firstTask.drop 1
  let some opened := Core.run {} setup
    | throw (IO.userError "could not reconstruct the fork's starting reservations")
  let some serial := Core.run opened forkBytes
    | throw (IO.userError "could not replay the serial byte fork")
  let some concurrent := Core.run opened interleaved
    | throw (IO.userError "interleaved packed stores lost byte authority")
  let picks := [1, 0, 1, 1, 1, 1, 1, 0]
  let some (scheduled, dynamic) := forward.runForkSchedule 1 picks
    | throw (IO.userError "the dynamic scheduler rejected the admitted masked interleaving")
  require "dynamic packed scheduling executes the regenerated bytes in task order"
    (decide (scheduled = interleaved) && decide (dynamic = concurrent))
  require "dynamic packed scheduling rejects missing, exhausted, or out-of-range task picks"
    ((forward.runForkSchedule 1 (picks.take 7)).isNone &&
      (forward.runForkSchedule 1 (picks ++ [0])).isNone &&
      (forward.runForkSchedule 1 (2 :: picks)).isNone && (forward.runForkSchedule 0 []).isNone)
  require "interleaving between a masked read and write preserves bytes and reservations"
    (setup.length == 28 && forkBytes.length == 8 && forkBytes.all Core.Instruction.isByteAccess &&
      decide (serial.allocations = concurrent.allocations) &&
      decide (opened.resources = concurrent.resources))
  let some firstSample := opened.byte ⟨forward.record.owner, 8⟩
    | throw (IO.userError "missing the first mask's boundary byte")
  let some secondSample := opened.byte ⟨forward.record.owner, 4⟩
    | throw (IO.userError "missing the second mask's boundary byte")
  require "each mask observes its own boundary byte after an interleaved sibling access"
    (firstSample != secondSample && serial.observations.take 2 == [secondSample, firstSample] &&
      concurrent.observations.take 2 == [firstSample, secondSample])
  let rebuild := forkState.memory.writeInScopeProgramFromSamples 0
  require "the interleaved samples regenerate the same store operands for each task"
    (decide (rebuild [0] 2 ((concurrent.observations.take 1).map UInt8.toBitVec) = some firstTask) &&
      decide (rebuild [2] 12345 (((concurrent.observations.drop 1).take 1).map UInt8.toBitVec) = some secondTask) &&
      (rebuild [0] 2 []).isNone && decide (rebuild [0] 2 [0] ≠ some firstTask))
  require "a packed fork write conflicts with a read of its boundary byte"
    (validate { contents with operations := [
      .openScope 0 [] .exclusive,
      .fork 0 [⟨[1], [4, 5, 6, 7, 8], some 0⟩, ⟨[2], [0, 1, 2, 3, 4], none⟩],
      .closeScope 0] }).isOk.not
  require "two fork writes with disjoint bits still conflict on their shared byte"
    (validate { contents with operations := [
      .openScope 0 [] .exclusive,
      .fork 0 [⟨[1], [4, 5, 6, 7, 8], some 0⟩, ⟨[0], [8], some 3⟩],
      .closeScope 0] }).isOk.not
  require "every fork names a live parent scope, even with no tasks"
    (validate { contents with operations := [.fork 99 []] }).isOk.not
  let unitSchema : PackedSchema := .record [(.mayShareByte, .value (.tagged [.raw 0]) ⟨0, 1⟩)]
  let some unitRecord := PackedRecord.plan .natural unitSchema 0
    | throw (IO.userError "could not plan a zero-byte record")
  let unitLayout := describe unitRecord
  let zeroModule : Module := {
    version
    schema := unitSchema
    layout := unitLayout
    initial := [([0], 0)]
    operations := [.openScope 0 [] .exclusive,
      .capturePayload 0 0 [0] [], .fork 0 [⟨[0], [], some 0⟩, ⟨[0], [], none⟩, ⟨[0], [], some 0⟩],
      .forgetPayload 0, .closeScope 0] }
  let .ok zeroBytes := validate zeroModule
    | throw (IO.userError "packed MIR rejected a fork in a live zero-byte record")
  require "a zero-byte record has a live owner until destruction"
    ((zeroBytes.final.memory.heap.allocation zeroBytes.record.owner).any (·.bytes.isEmpty) &&
      zeroBytes.final.observations == [0] && zeroBytes.final.memory.generation [0] == 2 &&
      (zeroBytes.dropped.allocation zeroBytes.record.owner).isNone)
  require "zero-width operations emit no target byte operands"
    ((zeroBytes.kernelTargetOperands 64).any List.isEmpty)
  let some (zeroScheduled, zeroHeap) := zeroBytes.runForkSchedule 2 []
    | throw (IO.userError "the scheduler rejected empty byte groups for zero-width tasks")
  require "zero-width tasks need no choices and preserve the live zero-byte allocation"
    (zeroScheduled.isEmpty && (zeroHeap.allocation zeroBytes.record.owner).any (·.bytes.isEmpty) &&
      (zeroBytes.runForkSchedule 2 [0]).isNone)
  require "a zero-byte fork replacement invalidates the captured variant payload"
    (validate { zeroModule with operations := [
      .openScope 0 [] .exclusive, .capturePayload 0 0 [0] [], .fork 0 [⟨[0], [], some 0⟩],
      .loadPayload 0 0 [], .forgetPayload 0, .closeScope 0] }).isOk.not
  let small := PackedType.addressable 1 (.raw 8)
  let word := PackedType.addressable 4 (.raw 32)
  let flatPayload := PackedType.addressable 4 (.product (.padding 0 24 small) word)
  let union (payloadTy : PackedType) (before after : Nat) := PackedType.addressable 4
    (.tagged [.padding before (64 + after) (.raw 0), .padding before after payloadTy])
  let unionSchema (ty : PackedType) (alignment : Nat) : PackedSchema :=
    .record [(.mayShareByte, .value ty ⟨12, alignment⟩)]
  let payload := 7 + 0x12345678 * 2 ^ 32
  let replacement := 5 + 0xabcdef01 * 2 ^ 32
  let initial := 1 + payload * 2 ^ 32
  let replaced := 1 + replacement * 2 ^ 32
  let bytes := List.range 12
  let alignedVariant : Module := {
    version
    schema := unionSchema (union flatPayload 31 0) 4
    layout := ⟨12, 4, [⟨[0], 0, none, 96, 12⟩]⟩
    initial := [([0], initial)]
    operations := [.openScope 0 [] .exclusive, .capturePayload 0 0 [0] bytes,
      .loadPayload 0 0 bytes, .store 0 [0] bytes replaced, .forgetPayload 0,
      .capturePayload 0 1 [0] bytes, .loadPayload 0 1 bytes, .forgetPayload 1, .closeScope 0] }
  let .ok aligned := validate alignedVariant
    | throw (IO.userError "packed MIR rejected the aligned variant payload")
  require "aligned payload capture skips union padding and preserves the payload's word offset"
    (aligned.final.observations.reverse == [payload, replacement])
  require "an aligned same-tag store invalidates the previous payload capture"
    (validate { alignedVariant with operations := [.openScope 0 [] .exclusive,
      .capturePayload 0 0 [0] bytes, .store 0 [0] bytes replaced, .loadPayload 0 0 bytes,
      .forgetPayload 0, .closeScope 0] }).isOk.not
  let firstSteps : List PackedType.FieldStep := [.unwrapAddressable, .left, .unpad, .unwrapAddressable]
  let wordSteps : List PackedType.FieldStep := [.unwrapAddressable, .right, .unwrapAddressable]
  let projectedOps := [.openScope 0 [] .exclusive, .capturePayload 0 0 [0] bytes,
    .loadPayloadField 0 0 1 firstSteps bytes, .loadPayloadField 0 0 1 wordSteps bytes,
    .forgetPayload 0, .closeScope 0]
  let .ok projected := validate { alignedVariant with operations := projectedOps }
    | throw (IO.userError "packed MIR rejected aligned projected payload loads")
  let some projectedKernel := projected.kernelProgram
    | throw (IO.userError "packed MIR failed to extract the projected payload reads")
  require "typed projected loads skip slot padding and retain the original byte permissions"
    (projected.final.observations.reverse == [7, 0x12345678] &&
      projected.checkKernelProgram projectedKernel &&
      projectedKernel.countP (fun op => match op with | .readView _ => true | _ => false) == 36)
  require "a projected same-tag load rejects the old generation"
    (validate { alignedVariant with operations := [.openScope 0 [] .exclusive,
      .capturePayload 0 0 [0] bytes, .store 0 [0] bytes replaced,
      .loadPayloadField 0 0 1 wordSteps bytes, .forgetPayload 0, .closeScope 0] }).isOk.not
  require "a projected load rejects a selector that treats addressability as a product"
    (validate { alignedVariant with operations := [.openScope 0 [] .exclusive,
      .capturePayload 0 0 [0] bytes, .loadPayloadField 0 0 1 [.right] bytes,
      .forgetPayload 0, .closeScope 0] }).isOk.not
  require "a projected load rejects a forged footprint that omits the tag"
    (validate { alignedVariant with operations := [.openScope 0 [] .exclusive,
      .capturePayload 0 0 [0] bytes, .loadPayloadField 0 0 1 wordSteps [8, 9, 10, 11],
      .forgetPayload 0, .closeScope 0] }).isOk.not
  require "a projected load rejects an expected tag different from the capture"
    (validate { alignedVariant with operations := [.openScope 0 [] .exclusive,
      .capturePayload 0 0 [0] bytes, .loadPayloadField 0 0 0 wordSteps bytes,
      .forgetPayload 0, .closeScope 0] }).isOk.not
  let compactProjection : Module := { contents with
    schema := .record [
      (.mayShareByte, .value (.raw 3) ⟨1, 1⟩),
      (.mayShareByte, .value (.tagged [.raw 0, .product (.raw 5) (.raw 27), .raw 13]) ⟨8, 8⟩),
      (.mayShareByte, .value (.raw 35) ⟨8, 8⟩)]
    initial := [([0], 7), ([1], 1 + 4 * (23 + 32 * 0x7123456)), ([2], 2^35-1)]
    operations := [.openScope 0 [] .shared, .capturePayload 0 0 [1] [4, 5, 6, 7, 8],
      .loadPayloadField 0 0 1 [.left] [4, 5, 6, 7, 8],
      .loadPayloadField 0 0 1 [.right] [4, 5, 6, 7, 8], .forgetPayload 0, .closeScope 0] }
  let .ok serialized := parse (Lean.toJson compactProjection).compress
    | throw (IO.userError "projected payload MIR JSON round-trip failed")
  let .ok compact := validate serialized
    | throw (IO.userError "packed MIR rejected compact projected payload loads")
  require "compact projected loads recover adjacent fields crossing byte boundaries"
    (compact.final.observations.reverse == [23, 0x7123456])
  let .ok updatedSibling := validate { compactProjection with operations := [
    .openScope 0 [] .exclusive, .capturePayload 0 0 [1] [4, 5, 6, 7, 8],
    .store 0 [0] [8] 3, .loadPayloadField 0 0 1 [.right] [4, 5, 6, 7, 8],
    .forgetPayload 0, .load 0 [0] [8], .closeScope 0] }
    | throw (IO.userError "packed MIR invalidated a capture after a sibling write in the shared byte")
  require "a sibling write in the shared boundary byte preserves the captured payload field"
    (updatedSibling.final.observations.reverse == [0x7123456, 3])
  let borrowedRead (scope : Nat) := [
    .openScope 0 [] .exclusive, .capturePayload 0 0 [1] [4, 5, 6, 7, 8],
    .reborrow 1 0 [1] .shared, .loadPayloadField scope 0 1 [.right] [4, 5, 6, 7, 8],
    .closeScope 1, .forgetPayload 0, .closeScope 0]
  let .ok activeChild := validate { compactProjection with operations := borrowedRead 1 }
    | throw (IO.userError "packed MIR rejected a projected read through the active child scope")
  require "only the active reborrow may use the captured payload field"
    (activeChild.final.observations == [0x7123456] &&
      (validate { compactProjection with operations := borrowedRead 0 }).isOk.not)
  require "inactive payload requirements reject a misaligned interior even when initializing the empty tag"
    (validate { alignedVariant with
      schema := unionSchema (union flatPayload 7 24) 4
      initial := [([0], 0)]
      operations := [] }).isOk.not
  let misalignedWord := PackedType.addressable 4 (.product small (.padding 0 24 word))
  require "an aligned payload still rejects a misaligned scalar field"
    (PackedRecord.plan .natural (unionSchema (union misalignedWord 31 0) 4) 0).isNone
  require "a padded union rejects a slot with insufficient base alignment"
    (PackedRecord.plan .natural (unionSchema (union flatPayload 31 0) 1) 0).isNone
  IO.println "Typed packed MIR regressions passed"

end Aethel.PackedMIR.Tests
