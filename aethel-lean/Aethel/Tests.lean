import Aethel

namespace Aethel.Tests

private def expect (name : String) (condition : Bool) : IO Unit := do
  unless condition do throw (IO.userError s!"FAILED: {name}")

private def emptyFacts : FactEnv := ⟨[]⟩
private def guarded : FactEnv := ⟨[(.value 0, .value 1)]⟩

/-- Named semantic regressions; these are not the future full-language litmus corpus. -/
def named : List (String × Bool) := [
  ("empty regex rejects epsilon", !(Regex.empty : Regex Nat).accepts []),
  ("epsilon accepts epsilon", (Regex.epsilon : Regex Nat).accepts []),
  ("epsilon rejects symbol", !(Regex.epsilon : Regex Nat).accepts [0]),
  ("atom consumes exactly one symbol", (Regex.atom 3).accepts [3]),
  ("atom rejects extra symbols", !(Regex.atom 3).accepts [3, 3]),
  ("nullable sequence follows right derivative",
    (Regex.seq (.alt .epsilon (.atom 0)) (.atom 1)).accepts [1]),
  ("star accepts zero iterations", (Regex.star (.atom (2 : Nat))).accepts []),
  ("star handles nullable body", (Regex.star (.alt .epsilon (.atom 2))).accepts [2, 2]),
  ("star rejects wrong symbol", !(Regex.star (.atom 2)).accepts [2, 3]),
  ("empty regex only matches epsilon vacuously", (Regex.empty : Regex Nat).onlyEmpty),
  ("epsilon-only star is safe", (Regex.star (.alt .empty .epsilon) : Regex Nat).onlyEmpty),
  ("empty product has no nonempty words", (Regex.seq .empty (.atom (1 : Nat))).onlyEmpty),
  ("unbounded nonempty star is not epsilon-only", !(Regex.star (.atom (1 : Nat))).onlyEmpty),
  ("outbound summary permits epsilon aliases",
    BorrowSummary.checkOutbound ⟨2, fun _ _ => (Regex.epsilon : Regex Nat)⟩ 0),
  ("outbound summary detects one descendant",
    !BorrowSummary.checkOutbound ⟨2, fun _ target =>
      if target == 1 then Regex.atom (0 : Nat) else .epsilon⟩ 0),
  ("distinct prefixes share residual epsilon",
    ((Regex.alt (.atom (0 : Nat)) (.atom 1)).deriv 0).accepts [] &&
    ((Regex.alt (.atom (0 : Nat)) (.atom 1)).deriv 1).accepts []),
  ("different fields separate", pathsDisjoint emptyFacts [.field 0] [.field 1]),
  ("same field conflicts", !pathsDisjoint emptyFacts [.field 0] [.field 0]),
  ("parent overlaps descendant", !pathsDisjoint emptyFacts [.field 0] [.field 0, .field 1]),
  ("root overlaps every child", !pathsDisjoint emptyFacts [] [.field 1]),
  ("nested sibling fields separate",
    pathsDisjoint emptyFacts [.field 0, .field 1] [.field 0, .field 2]),
  ("different constants separate", pathsDisjoint emptyFacts [.index (.const 0)] [.index (.const 1)]),
  ("different names need evidence", !pathsDisjoint emptyFacts [.index (.value 0)] [.index (.value 1)]),
  ("guard proves index separation", pathsDisjoint guarded [.index (.value 0)] [.index (.value 1)]),
  ("guard is symmetric", pathsDisjoint guarded [.index (.value 1)] [.index (.value 0)]),
  ("unrelated guard proves nothing", !pathsDisjoint guarded [.index (.value 0)] [.index (.value 2)]),
  ("join drops one-sided guard", !(guarded.join emptyFacts).provesNe (.value 0) (.value 1)),
  ("join preserves common guard", (guarded.join guarded).provesNe (.value 0) (.value 1)),
  ("adjacent half-open slices separate", Interval.disjoint ⟨0, 4⟩ ⟨4, 8⟩),
  ("overlapping slices conflict", !Interval.disjoint ⟨0, 5⟩ ⟨4, 8⟩),
  ("empty interior slice separates", Interval.disjoint ⟨3, 3⟩ ⟨0, 8⟩),
  ("shared readers may share bytes",
    Footprint.compatible ⟨[⟨0, 0⟩], []⟩ ⟨[⟨0, 0⟩], []⟩),
  ("packed sibling setters conflict physically",
    !(packedSetterFootprint ⟨0, 0⟩).compatible (packedSetterFootprint ⟨0, 0⟩)),
  ("same offsets in separate allocations separate",
    (packedSetterFootprint ⟨0, 0⟩).compatible (packedSetterFootprint ⟨1, 0⟩)),
  ("writer conflicts with reader",
    !Footprint.compatible ⟨[], [⟨0, 0⟩]⟩ ⟨[⟨0, 0⟩], []⟩),
  ("valid reordered record", RecordLayout.check ⟨16, 8, [⟨0, 8, 8⟩, ⟨8, 4, 4⟩]⟩),
  ("overlapping fields rejected", !RecordLayout.check ⟨8, 4, [⟨0, 4, 4⟩, ⟨0, 4, 4⟩]⟩),
  ("out-of-extent field rejected", !RecordLayout.check ⟨8, 8, [⟨8, 1, 1⟩]⟩),
  ("zero alignment rejected", !RecordLayout.check ⟨8, 0, []⟩),
  ("misaligned field rejected", !RecordLayout.check ⟨8, 4, [⟨1, 4, 4⟩]⟩),
  ("stride must respect field alignment", !RecordLayout.check ⟨12, 4, [⟨0, 8, 8⟩]⟩),
  ("empty record supported", RecordLayout.check ⟨0, 1, []⟩),
  ("aligned vector at base", checkAccess 64 64 0 32 32 1024),
  ("second Vec8 is only 32-aligned", !checkAccess 64 64 32 32 64 1024),
  ("second Vec8 valid at actual alignment", checkAccess 64 64 32 32 32 1024),
  ("misaligned subview rejected", !checkAccess 64 64 4 32 32 1024),
  ("out-of-bounds access rejected", !checkAccess 64 64 48 32 16 1024),
  ("address-space overflow rejected", !checkAccess 64 1000 0 4 4 1024),
  ("zero-width access rejected", !checkAccess 64 64 0 0 4 1024),
  ("aligned scalar subrange", ScalarRange.check ⟨64, 32, 4, 7, 4, 4⟩ 1024 64),
  ("scalar subrange rejects a misaligned start", !ScalarRange.check ⟨64, 32, 2, 7, 4, 4⟩ 1024 64),
  ("scalar subrange rejects an invalid stride", !ScalarRange.check ⟨64, 32, 0, 7, 4, 8⟩ 1024 64),
  ("empty scalar subrange at the allocation end", ScalarRange.check ⟨64, 32, 32, 0, 4, 4⟩ 1024 64),
  ("scalar subrange cannot exceed the ABI size limit", !ScalarRange.check ⟨64, 32, 0, 8, 4, 4⟩ 1024 31),
  ("u1 packs into the last bit of a byte", (IntegerType.unsigned .w1).checkPackedByte 7),
  ("u4 cannot cross a packed byte boundary", !(IntegerType.unsigned .w4).checkPackedByte 5),
  ("addressable u1 occupies a byte",
    (TargetIntegerABI.natural.place (.unsigned .w1) 3).any fun f =>
      f.offset == 3 && f.size == 1 && f.alignment == 1),
  ("natural i32 placement aligns the current cursor",
    (TargetIntegerABI.natural.place (.signed .w32) 3).any fun f =>
      f.offset == 4 && f.size == 4 && f.alignment == 4),
  ("target ABI can supply a padded u8 slot",
    ((⟨fun _ => ⟨4, 4⟩⟩ : TargetIntegerABI).place (.unsigned .w8) 5).any fun f =>
      f.offset == 8 && f.size == 4 && f.alignment == 4),
  ("integer slot rejects insufficient byte capacity",
    ((⟨fun _ => ⟨1, 1⟩⟩ : TargetIntegerABI).place (.signed .w32) 0).isNone),
  ("integer slot rejects non-power-of-two alignment",
    ((⟨fun _ => ⟨6, 3⟩⟩ : TargetIntegerABI).place (.unsigned .w8) 0).isNone),
  ("integer slot rejects stride that breaks element alignment",
    ((⟨fun _ => ⟨6, 4⟩⟩ : TargetIntegerABI).place (.signed .w32) 0).isNone),
  ("a single addressable u1 record shrinks under alignment ordering",
    SingleFlagLayout.declarationOrder.check && SingleFlagLayout.alignmentOrder.check &&
      SingleFlagLayout.declarationOrder.size == 12 && SingleFlagLayout.alignmentOrder.size == 8),
  ("four flags leave both layouts at the same stride",
    (FlagRecordLayout.unpacked 4).size == FlagRecordLayout.packed.size),
  ("five flags shrink the aligned record by four bytes",
    (FlagRecordLayout.unpacked 5).check && FlagRecordLayout.packed.check &&
      (FlagRecordLayout.unpacked 5).size == FlagRecordLayout.packed.size + 4),
  ("packed flags and payload occupy their proved byte offsets",
    let value : FlagRecordLayout.Value 5 := ⟨BitVec.ofNat 5 21, fun i => i.val.toUInt8 + 10⟩
    FlagRecordLayout.packedBytes value (by decide) == [10, 11, 12, 13, 21, 0, 0, 0]),
  ("packed low setter preserves upper", highNibble (setLowNibble 171 ⟨2, by decide⟩) == 10),
  ("packed high setter preserves lower", lowNibble (setHighNibble 171 ⟨2, by decide⟩) == 11)
]

def run : IO Unit := do
  for (name, ok) in named do expect name ok
  IO.println s!"{named.length} named foundational regressions passed"

  -- Independent interval oracle enumerates all member indices rather than
  -- reimplementing the endpoint comparison used by the checker.
  let mut intervals := 0
  for alo in [:9] do
    for ahi in [alo:9] do
      for blo in [:9] do
        for bhi in [blo:9] do
          let a : Interval := ⟨alo, ahi⟩
          let b : Interval := ⟨blo, bhi⟩
          let common := (List.range 9).any fun i =>
            decide (alo ≤ i ∧ i < ahi ∧ blo ≤ i ∧ i < bhi)
          expect s!"intervals [{alo},{ahi}), [{blo},{bhi})" (a.disjoint b == !common)
          intervals := intervals + 1
  IO.println s!"{intervals} interval cases matched the enumerated-set oracle"

  let mut aligned := 0
  for alignment in [1, 2, 4, 8, 16, 32, 64] do
    for offset in [:129] do
      let result := alignUp offset alignment
      expect "aligned result" (decide (offset ≤ result ∧ result % alignment = 0))
      for candidate in [offset:result] do
        expect "minimal padding" (decide (candidate % alignment ≠ 0))
      aligned := aligned + 1
  IO.println s!"{aligned} alignment cases checked against every smaller candidate"

  let mut packed := 0
  for byte in [:256] do
    for value in List.finRange 16 do
      let n := value.val
      let low := setLowNibble byte value
      let high := setHighNibble byte value
      expect "packed write trace" (decide (low < 256 ∧ high < 256 ∧
        lowNibble low = n ∧ highNibble low = highNibble byte ∧
        highNibble high = n ∧ lowNibble high = lowNibble byte))
      packed := packed + 1
  IO.println s!"{packed} packed-byte update cases passed"

  let table : ScalarTable := fun i f => i * 100 + f
  let mut slots := 0
  for length in [1:9] do
    for fields in [1:9] do
      for i in [:length] do
        for f in [:fields] do
          let expected := i * 100 + f
          expect "scalar AoS/SoA read agreement"
            (encodeAoS table fields (aosSlot fields i f) == expected &&
             encodeSoA table length (soaSlot length i f) == expected)
          slots := slots + 1
  IO.println s!"{slots} scalar AoS/SoA read cases passed"

  let mut observations := 0
  for length in [1:9] do
    for fields in [1:9] do
      let mut aos := encodeAoS table fields
      let mut soa := encodeSoA table length
      for i in [:length] do
        for f in [:fields] do
          let value := 1000 + i * fields + f
          aos := writeSlot aos (aosSlot fields i f) value
          soa := writeSlot soa (soaSlot length i f) value
          for j in [:length] do
            for g in [:fields] do
              -- Independent trace oracle: row-major predecessors have been
              -- overwritten; successors must retain the original values.
              let expected := if j < i || (j == i && g ≤ f)
                then 1000 + j * fields + g else j * 100 + g
              expect "scalar AoS/SoA mutation trace and frame"
                (aos (aosSlot fields j g) == expected &&
                 soa (soaSlot length j g) == expected)
              observations := observations + 1
  IO.println s!"{observations} scalar AoS/SoA mutation/frame observations passed"

  let statuses : List Status := [.idle, .dead] ++
    (List.finRange 4).map Status.moving ++ (List.finRange 16).map Status.poisoned
  for bits in [:256] do
    let expected := statuses.find? fun status => status.encode == bits
    expect s!"sum tag/payload decoding of {bits}" (Status.decode bits == expected)
  IO.println "256 sum-tag encoding/invalid-payload cases passed"

end Aethel.Tests
