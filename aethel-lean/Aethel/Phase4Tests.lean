import Aethel.LawFrameDischarge
import Aethel.LawFalsifier
import Aethel.LawAutoProver
import Aethel.ConstitutionalLaws
import Aethel.RecordRuntime

namespace Aethel.Phase4.Tests

open Aethel Aethel.Core Aethel.AutomaticLayout Aethel.CacheLayout Aethel.CategoricalFusion
open Aethel.LawFrameDischarge Aethel.LawFalsifier Aethel.LawAutoProver Aethel.ConstitutionalLaws

private def require (msg : String) (ok : Bool) : IO Unit := do
  unless ok do throw (IO.userError msg)

private def initBuffer (lay : CollectionLayout) (len fields : Nat) (bTable : Nat → Nat → UInt8) :
    Core.State :=
  let bytes := (List.range (len * fields)).map fun addr =>
    match lay with
    | .aos => bTable (addr / fields) (addr % fields)
    | .soa => bTable (addr % len) (addr / len)
    | .aosoa w =>
      let tileSize := fields * w
      let tile := addr / tileSize
      let rem := addr % tileSize
      bTable (tile * w + rem % w) (rem / w)
  ({} : Core.State).addAllocation 0 bytes

private def runTier0FrameTests : IO Unit := do
  -- Record effect frame checker (pos=[0], vel=[1] written -> health=[2], team=[3] preserved)
  let movEff : Effect := ⟨[[0], [1]], [[0], [1]], []⟩
  require "Tier 0 movement_safe preserves health and team"
    (checkEffectPreserves movEff [[2], [3]])
  require "Tier 0 self-write is rejected"
    (!checkEffectPreserves ⟨[], [[0]], []⟩ [[0]])
  require "Tier 0 parent-prefix write is rejected"
    (!checkEffectPreserves ⟨[], [[]], []⟩ [[0, 1]])

  -- Bit-packed record (u4 + u4 + u1): mutating [0] preserves siblings [1] and [2]
  let schema : Schema := .record
    [ (.mayShareByte, .integer (.unsigned .w4))
    , (.mayShareByte, .integer (.unsigned .w4))
    , (.mayShareByte, .integer (.unsigned .w1)) ]
  let some planned := planVerified .natural schema
    | throw (IO.userError "Tier 0 packed record planning failed")
  let some img0 := initializeRecord planned.property (fun
    | [0] => some ⟨.unsigned .w4, BitVec.ofNat 4 3⟩
    | [1] => some ⟨.unsigned .w4, BitVec.ofNat 4 6⟩
    | [2] => some ⟨.unsigned .w1, BitVec.ofNat 1 1⟩
    | _ => none)
    | throw (IO.userError "Tier 0 packed record initialization failed")
  let some img1 := writeInteger planned.property [0] img0 ⟨.unsigned .w4, BitVec.ofNat 4 11⟩
    | throw (IO.userError "Tier 0 packed record write failed")
  match readInteger planned.property [0] img1,
        readInteger planned.property [1] img1,
        readInteger planned.property [2] img1 with
  | some ⟨.unsigned .w4, v0⟩, some ⟨.unsigned .w4, v1⟩, some ⟨.unsigned .w1, v2⟩ =>
    require "Tier 0 updated leaf [0] changed" (v0 == BitVec.ofNat 4 11)
    require "Tier 0 packed sibling leaf [1] preserved" (v1 == BitVec.ofNat 4 6)
    require "Tier 0 packed sibling leaf [2] preserved" (v2 == BitVec.ofNat 1 1)
  | _, _, _ => throw (IO.userError "Tier 0 packed record readback failed")

  -- Collection multi-pass frame preservation across AoS, SoA, and Tiled AoSoA (tileWidth = 8)
  require "Tier 0 collection preserves [2] across [0, 1] passes"
    (checkCollectionPreserves [0, 1] [2])
  require "Tier 0 collection rejects written field in preserves"
    (!checkCollectionPreserves [0, 1] [1, 2])
  let len := 20
  let fields := 3
  let bTable : Nat → Nat → UInt8 := fun i f => (i * 7 + f).toUInt8
  let passes : List (Nat × (UInt8 → UInt8)) := [(0, fun b => b + 1), (1, fun b => b * 2)]
  for lay in [CollectionLayout.aos, .soa, .aosoa 8] do
    let st0 := initBuffer lay len fields bTable
    let stAfter := applyFieldPasses 0 lay len fields passes st0
    for i in List.range len do
      let locPres : ByteLocation := ⟨0, collectionSlot lay len fields i 2⟩
      require "Tier 0 collection frame preserves field 2" (stAfter.byte locPres == st0.byte locPres)

private def runTier1FalsifierTests : IO Unit := do
  require "Tier 1 Status round-trip proved exhaustively"
    (verifyExhaustive statusDomain (fun s => Status.decode (Status.encode s) == some s) == .proved)
  require "Tier 1 constant Status decoder falsified at .dead"
    (verifyExhaustive statusDomain (fun s => some Status.idle == some s) == .falsified .dead)
  require "Tier 1 UInt8 saturating self-sub equals 0"
    (verifyExhaustive u8Domain (fun b => saturatingSubU8 b b == 0) == .proved)
  require "Tier 1 UInt8 wrapping sub falsified at 1"
    (verifyExhaustive u8Domain (fun b => decide (wrappingSubU8 0 b ≤ 0)) == .falsified 1)
  let cands : List (UInt8 × UInt8) := [(0, 0), (0, 1), (5, 2)]
  let prop := fun p : UInt8 × UInt8 => !(decide (wrappingSubU8 p.1 p.2 > p.1))
  let paused := boundedFalsify prop 1 cands
  require "Tier 1 bounded search pauses after 1 step" (paused == .pending [(0, 1), (5, 2)])
  require "Tier 1 bounded search resumes and agrees with full run"
    (boundedFalsify prop 4 cands == .found (0, 1) &&
     boundedFalsify prop (1 + 3) cands == boundedFalsify prop 3 [(0, 1), (5, 2)])

private def runTier2AutoProverTests : IO Unit := do
  require "Tier 2 proves bounded_damage universally"
    (autoProveNorm [] 12 exprBoundedDamage)
  require "Tier 2 proves damage_exact universally under dmg <= hp"
    (autoProveNorm [] 12 exprDamageRecovery)
  require "Tier 2 proves add commutativity"
    (autoProveNorm [] 12 exprAddComm)
  require "Tier 2 proves min(a, b) <= a + c"
    (autoProveNorm [] 12 exprMinLeAdd)
  let linGoal : LawProp :=
    .le (.add (.mulConst 2 (.var 0)) (.const 1))
        (.add (.add (.mulConst 3 (.var 0)) (.var 1)) (.const 5))
  require "Tier 2 proves 2*x + 1 <= 3*x + y + 5"
    (autoProveNorm [] 12 linGoal)
  require "Tier 2 proves x + 1 != x"
    (autoProveNorm [] 12 (.ne (.add (.var 0) (.const 1)) (.var 0)))
  require "Tier 2 symbolic falsifier catches buggy additive damage"
    (falsifySymbolic 6 [] exprBuggyDamage == some (0, 1, 0))
  let nonCommSub : LawProp := .eq (.sub (.var 0) (.var 1)) (.sub (.var 1) (.var 0))
  require "Tier 2 symbolic falsifier catches non-commutativity of Nat sub"
    ((falsifySymbolic 6 [] nonCommSub).isSome)

private def runTier3AndGateTests : IO Unit := do
  match checkConstitution 12 6 validEntityConstitution with
  | .allPassed reports =>
    let tiers := reports.map LawReport.outcome
    let expected :=
      [ GateOutcome.admitted .tier0Frame
      , GateOutcome.admitted .tier0Frame
      , GateOutcome.admitted .tier1Finite
      , GateOutcome.admitted .tier2Symbolic
      , GateOutcome.admitted .tier2Symbolic
      , GateOutcome.admitted .tier3CachedProof ]
    require "Tier 3 validEntityConstitution admits all 4 tiers" (tiers == expected)
  | .blocked _ =>
    throw (IO.userError "validEntityConstitution unexpectedly blocked")

  for badSuite in [buggyDamageConstitution, buggyFrameConstitution, buggyDecoderConstitution] do
    match checkConstitution 12 6 badSuite with
    | .allPassed _ => throw (IO.userError "buggy constitution unexpectedly passed")
    | .blocked reports =>
      require "buggy constitution yields blockedCounterexample"
        (reports.any fun r => match r.outcome with | .blockedCounterexample _ => true | _ => false)

  match checkConstitution 12 6 [.uncached compactStatusLaw] with
  | .allPassed _ => throw (IO.userError "uncached deep invariant unexpectedly passed")
  | .blocked reports =>
    require "uncached deep invariant fails closed with blockedUnproved"
      (reports.any fun r => match r.outcome with | .blockedUnproved _ => true | _ => false)

def run : IO Unit := do
  runTier0FrameTests
  runTier1FalsifierTests
  runTier2AutoProverTests
  runTier3AndGateTests
  IO.println "Phase 4 constitutional laws, frame discharge, falsifier, and symbolic auto-prover regressions passed"

end Aethel.Phase4.Tests
