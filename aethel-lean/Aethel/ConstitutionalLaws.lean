import Aethel.LawFrameDischarge
import Aethel.LawFalsifier
import Aethel.LawAutoProver
import Aethel.ADTLayout
import Aethel.CategoricalFusion

namespace Aethel.ConstitutionalLaws

open Aethel Aethel.LawFrameDischarge Aethel.LawFalsifier Aethel.LawAutoProver Aethel.ADTLayout

/-!
## Tier 3 & Unified Zero-Proof Constitutional Gate (`laws.aethel`)

Unifies the 4-tier invisible verification backend behind declarative human-facing laws:
- Tier 0: Instant O(1) structural & frame discharge (`preservesRecord`, `preservesCollection`)
- Tier 1: Exhaustive finite checking & bounded counterexample falsification
- Tier 2: Automated symbolic decision & proof synthesis (`autoProveNorm`, `falsifySymbolic`)
- Tier 3: Kernel-verified proof cache (`PLift law.Holds`) with fail-closed admission
-/

inductive ConstitutionalLaw : Type 1 where
  | preservesRecord (name : String) (eff : Effect) (preserved : List (List Nat))
  | preservesCollection (name : String) (writtenFields preservedFields : List Nat)
  | alwaysFinite (name : String) {α : Type} (dom : FiniteDomain α) (reprFn : α → String) (prop : α → Bool)
  | neverFinite (name : String) {α : Type} (dom : FiniteDomain α) (reprFn : α → String) (forbidden : α → Bool)
  | alwaysSymbolic (name : String) (hyps : List LawProp) (goal : LawProp)
  | neverSymbolic (name : String) (hyps : List LawProp) (forbidden : LawProp)
  | deepInvariant (name : String) (claim : Prop)

def ConstitutionalLaw.alwaysFiniteRepr (name : String) {α : Type} [Repr α]
    (dom : FiniteDomain α) (prop : α → Bool) : ConstitutionalLaw :=
  .alwaysFinite name dom (fun x => toString (repr x)) prop

def ConstitutionalLaw.neverFiniteRepr (name : String) {α : Type} [Repr α]
    (dom : FiniteDomain α) (forbidden : α → Bool) : ConstitutionalLaw :=
  .neverFinite name dom (fun x => toString (repr x)) forbidden

def ConstitutionalLaw.name : ConstitutionalLaw → String
  | .preservesRecord n _ _ => n
  | .preservesCollection n _ _ => n
  | .alwaysFinite n _ _ _ => n
  | .neverFinite n _ _ _ => n
  | .alwaysSymbolic n _ _ => n
  | .neverSymbolic n _ _ => n
  | .deepInvariant n _ => n

/-- Independent mathematical specification of constitutional law satisfaction. -/
def ConstitutionalLaw.Holds : ConstitutionalLaw → Prop
  | .preservesRecord _ eff preserved => EffectPreserves eff preserved
  | .preservesCollection _ writtenFields preservedFields =>
    CollectionPreserves writtenFields preservedFields
  | .alwaysFinite (α := α) _ _ _ prop => ∀ x : α, prop x = true
  | .neverFinite (α := α) _ _ _ forbidden => ∀ x : α, forbidden x = false
  | .alwaysSymbolic _ hyps goal =>
    ∀ env : Nat → Nat, (∀ h ∈ hyps, h.Holds env) → goal.Holds env
  | .neverSymbolic _ hyps forbidden =>
    ∀ env : Nat → Nat, (∀ h ∈ hyps, h.Holds env) → ¬ forbidden.Holds env
  | .deepInvariant _ claim => claim

structure CachedLawEntry : Type 1 where
  law : ConstitutionalLaw
  cached : Option (PLift law.Holds) := none

def CachedLawEntry.uncached (law : ConstitutionalLaw) : CachedLawEntry :=
  ⟨law, none⟩

def CachedLawEntry.withCachedProof (law : ConstitutionalLaw) (proof : law.Holds) : CachedLawEntry :=
  ⟨law, some ⟨proof⟩⟩

inductive DischargeTier where
  | tier0Frame
  | tier1Finite
  | tier2Symbolic
  | tier3CachedProof
  deriving Repr, DecidableEq

inductive GateOutcome where
  | admitted (tier : DischargeTier)
  | blockedCounterexample (witness : String)
  | blockedUnproved (reason : String)
  deriving Repr, DecidableEq

structure LawReport where
  name : String
  outcome : GateOutcome
  deriving Repr, DecidableEq

inductive ConstitutionResult where
  | allPassed (reports : List LawReport)
  | blocked (reports : List LawReport)
  deriving Repr, DecidableEq

private def checkCachedOrFail (entry : CachedLawEntry) (fallbackReason : String) : GateOutcome :=
  match entry.cached with
  | some _ => .admitted .tier3CachedProof
  | none => .blockedUnproved fallbackReason

def checkEntry (symbolicFuel : Nat := 12) (falsifyBound : Nat := 6) (entry : CachedLawEntry) :
    GateOutcome :=
  match entry.law with
  | .preservesRecord _ eff preserved =>
    if checkEffectPreserves eff preserved then .admitted .tier0Frame
    else .blockedCounterexample "effect writes or invalidates a preserved field path"
  | .preservesCollection _ writtenFields preservedFields =>
    if checkCollectionPreserves writtenFields preservedFields then .admitted .tier0Frame
    else .blockedCounterexample "collection pass mutates a preserved field index"
  | .alwaysFinite _ dom reprFn prop =>
    match verifyExhaustive dom prop with
    | .proved => .admitted .tier1Finite
    | .falsified w => .blockedCounterexample (reprFn w)
  | .neverFinite _ dom reprFn forbidden =>
    match verifyExhaustive dom (fun x => !(forbidden x)) with
    | .proved => .admitted .tier1Finite
    | .falsified w => .blockedCounterexample (reprFn w)
  | .alwaysSymbolic _ hyps goal =>
    if autoProveNorm hyps symbolicFuel goal then .admitted .tier2Symbolic
    else
      match falsifySymbolic falsifyBound hyps goal with
      | some (v0, v1, v2) =>
        .blockedCounterexample s!"v0={v0}, v1={v1}, v2={v2}"
      | none =>
        checkCachedOrFail entry "symbolic goal not auto-proved and no cached proof supplied"
  | .neverSymbolic _ hyps forbidden =>
    if autoProveNorm hyps symbolicFuel (.not forbidden) then .admitted .tier2Symbolic
    else
      match falsifySymbolic falsifyBound hyps (.not forbidden) with
      | some (v0, v1, v2) =>
        .blockedCounterexample s!"v0={v0}, v1={v1}, v2={v2}"
      | none =>
        checkCachedOrFail entry "forbidden condition not auto-refuted and no cached proof supplied"
  | .deepInvariant _ _ =>
    checkCachedOrFail entry "deep invariant requires a Tier 3 kernel-checked proof"

def checkConstitution (symbolicFuel : Nat := 12) (falsifyBound : Nat := 6)
    (entries : List CachedLawEntry) : ConstitutionResult :=
  let reports := entries.map fun e => ⟨e.law.name, checkEntry symbolicFuel falsifyBound e⟩
  let anyBlocked := reports.any fun r =>
    match r.outcome with
    | .admitted _ => false
    | _ => true
  if anyBlocked then .blocked reports else .allPassed reports

private theorem checkCachedOrFail_sound {entry : CachedLawEntry} {reason : String} {tier : DischargeTier}
    (hAdm : checkCachedOrFail entry reason = .admitted tier) :
    entry.law.Holds := by
  dsimp [checkCachedOrFail] at hAdm
  cases hC : entry.cached with
  | none =>
    rw [hC] at hAdm
    cases hAdm
  | some proof =>
    exact proof.down

theorem checkEntry_admitted_sound {fuel bound : Nat} {entry : CachedLawEntry} {tier : DischargeTier}
    (hAdm : checkEntry fuel bound entry = .admitted tier) :
    entry.law.Holds := by
  cases entry with
  | mk law cached =>
    cases law with
    | preservesRecord _ eff preserved =>
      dsimp [checkEntry] at hAdm
      split at hAdm
      · next hChk => exact (checkEffectPreserves_correct eff preserved).mp hChk
      · cases hAdm
    | preservesCollection _ written preserved =>
      dsimp [checkEntry] at hAdm
      split at hAdm
      · next hChk => exact (checkCollectionPreserves_correct written preserved).mp hChk
      · cases hAdm
    | alwaysFinite _ dom reprFn prop =>
      dsimp [checkEntry] at hAdm
      cases hV : verifyExhaustive dom prop with
      | falsified _ =>
        rw [hV] at hAdm
        cases hAdm
      | proved =>
        exact (verifyExhaustive_proved_iff dom prop).mp hV
    | neverFinite _ dom reprFn forbidden =>
      dsimp [checkEntry] at hAdm
      cases hV : verifyExhaustive dom (fun x => !(forbidden x)) with
      | falsified _ =>
        rw [hV] at hAdm
        cases hAdm
      | proved =>
        intro x
        have hNot := (verifyExhaustive_proved_iff dom (fun x => !(forbidden x))).mp hV x
        simpa using hNot
    | alwaysSymbolic _ hyps goal =>
      dsimp [checkEntry] at hAdm
      split at hAdm
      · next hPrv => exact autoProveNorm_sound hPrv
      · cases hFal : falsifySymbolic bound hyps goal with
        | some witness =>
          rw [hFal] at hAdm
          cases hAdm
        | none =>
          rw [hFal] at hAdm
          exact checkCachedOrFail_sound hAdm
    | neverSymbolic _ hyps forbidden =>
      dsimp [checkEntry] at hAdm
      split at hAdm
      · next hPrv =>
        intro env hHyps
        exact autoProveNorm_sound hPrv env hHyps
      · cases hFal : falsifySymbolic bound hyps (.not forbidden) with
        | some witness =>
          rw [hFal] at hAdm
          cases hAdm
        | none =>
          rw [hFal] at hAdm
          exact checkCachedOrFail_sound hAdm
    | deepInvariant _ claim =>
      dsimp [checkEntry] at hAdm
      exact checkCachedOrFail_sound hAdm

theorem checkEntry_counterexample_refutes {fuel bound : Nat} {entry : CachedLawEntry}
    {witness : String}
    (hBlk : checkEntry fuel bound entry = .blockedCounterexample witness) :
    ¬ entry.law.Holds := by
  cases entry with
  | mk law cached =>
    cases law with
    | preservesRecord _ eff preserved =>
      dsimp [checkEntry] at hBlk
      split at hBlk
      · cases hBlk
      · next hChk =>
        intro hHolds
        have hTrue := (checkEffectPreserves_correct eff preserved).mpr hHolds
        exact hChk hTrue
    | preservesCollection _ written preserved =>
      dsimp [checkEntry] at hBlk
      split at hBlk
      · cases hBlk
      · next hChk =>
        intro hHolds
        have hTrue := (checkCollectionPreserves_correct written preserved).mpr hHolds
        exact hChk hTrue
    | alwaysFinite _ dom reprFn prop =>
      dsimp [checkEntry] at hBlk
      cases hV : verifyExhaustive dom prop with
      | proved =>
        rw [hV] at hBlk
        cases hBlk
      | falsified w =>
        exact (verifyExhaustive_falsified_sound hV).2
    | neverFinite _ dom reprFn forbidden =>
      dsimp [checkEntry] at hBlk
      cases hV : verifyExhaustive dom (fun x => !(forbidden x)) with
      | proved =>
        rw [hV] at hBlk
        cases hBlk
      | falsified w =>
        intro hHolds
        have ⟨_, hNotAll⟩ := verifyExhaustive_falsified_sound hV
        exact hNotAll fun x => by simp [hHolds x]
    | alwaysSymbolic _ hyps goal =>
      dsimp [checkEntry] at hBlk
      split at hBlk
      · cases hBlk
      · cases hFal : falsifySymbolic bound hyps goal with
        | none =>
          rw [hFal] at hBlk
          dsimp [checkCachedOrFail] at hBlk
          cases cached <;> cases hBlk
        | some witness =>
          obtain ⟨v0, v1, v2⟩ := witness
          exact falsifySymbolic_sound hFal
    | neverSymbolic _ hyps forbidden =>
      dsimp [checkEntry] at hBlk
      split at hBlk
      · cases hBlk
      · cases hFal : falsifySymbolic bound hyps (.not forbidden) with
        | none =>
          rw [hFal] at hBlk
          dsimp [checkCachedOrFail] at hBlk
          cases cached <;> cases hBlk
        | some witness =>
          intro hHolds
          obtain ⟨v0, v1, v2⟩ := witness
          exact falsifySymbolic_sound hFal hHolds
    | deepInvariant _ _ =>
      dsimp [checkEntry, checkCachedOrFail] at hBlk
      cases cached <;> cases hBlk

private def isNotAdmitted (r : LawReport) : Bool :=
  match r.outcome with
  | .admitted _ => false
  | _ => true

theorem checkConstitution_allPassed_sound {fuel bound : Nat}
    {entries : List CachedLawEntry} {reports : List LawReport}
    (hPass : checkConstitution fuel bound entries = .allPassed reports) :
    ∀ entry ∈ entries, entry.law.Holds := by
  dsimp [checkConstitution] at hPass
  split at hPass
  · cases hPass
  · next hNoBlock =>
    intro entry hMem
    have hAnyFalse :
        (entries.map fun e => ⟨e.law.name, checkEntry fuel bound e⟩).any isNotAdmitted = false := by
      cases hAny : (entries.map fun e => ⟨e.law.name, checkEntry fuel bound e⟩).any isNotAdmitted with
      | false => rfl
      | true => exact False.elim (hNoBlock hAny)
    have hNotIn : isNotAdmitted ⟨entry.law.name, checkEntry fuel bound entry⟩ = false := by
      cases hIs : isNotAdmitted ⟨entry.law.name, checkEntry fuel bound entry⟩ with
      | false => rfl
      | true =>
        have hTrue :
            (entries.map fun e => ⟨e.law.name, checkEntry fuel bound e⟩).any isNotAdmitted = true :=
          List.any_eq_true.mpr ⟨⟨entry.law.name, checkEntry fuel bound entry⟩,
            List.mem_map.mpr ⟨entry, hMem, rfl⟩, hIs⟩
        rw [hAnyFalse] at hTrue
        cases hTrue
    cases hOut : checkEntry fuel bound entry with
    | admitted tier => exact checkEntry_admitted_sound hOut
    | blockedCounterexample w => simp [isNotAdmitted, hOut] at hNotIn
    | blockedUnproved r => simp [isNotAdmitted, hOut] at hNotIn

theorem checkConstitution_allPassed_of_admitted {fuel bound : Nat}
    {entries : List CachedLawEntry}
    (hAll : ∀ entry ∈ entries, ∃ tier, checkEntry fuel bound entry = .admitted tier) :
    ∃ reports, checkConstitution fuel bound entries = .allPassed reports := by
  let reports : List LawReport := entries.map fun e => ⟨e.law.name, checkEntry fuel bound e⟩
  refine ⟨reports, ?_⟩
  dsimp [checkConstitution]
  have hAnyFalse :
      (reports.any fun r => match r.outcome with | .admitted _ => false | _ => true) = false := by
    cases hAny :
        (reports.any fun r => match r.outcome with | .admitted _ => false | _ => true) with
    | false => rfl
    | true =>
      obtain ⟨r, hrMem, hrPred⟩ := List.any_eq_true.mp hAny
      obtain ⟨e, heMem, rfl⟩ := List.mem_map.mp hrMem
      obtain ⟨tier, hAdm⟩ := hAll e heMem
      simp [hAdm] at hrPred
  simp [reports, hAnyFalse]

theorem checkConstitution_blocks_invalid {fuel bound : Nat}
    {entries : List CachedLawEntry}
    (hBad : ∃ entry ∈ entries, ¬ entry.law.Holds) :
    ∀ reports, checkConstitution fuel bound entries ≠ .allPassed reports := by
  intro reports hPass
  obtain ⟨entry, hMem, hNotHolds⟩ := hBad
  exact hNotHolds (checkConstitution_allPassed_sound hPass entry hMem)

theorem checkConstitution_blocks_counterexample {fuel bound : Nat}
    {entries : List CachedLawEntry} {entry : CachedLawEntry} {witness : String}
    (hMem : entry ∈ entries)
    (hBlk : checkEntry fuel bound entry = .blockedCounterexample witness) :
    ∃ reports, checkConstitution fuel bound entries = .blocked reports := by
  let reports : List LawReport := entries.map fun e => ⟨e.law.name, checkEntry fuel bound e⟩
  refine ⟨reports, ?_⟩
  dsimp [checkConstitution]
  have hAny :
      (reports.any fun r => match r.outcome with | .admitted _ => false | _ => true) = true := by
    apply List.any_eq_true.mpr
    refine ⟨⟨entry.law.name, checkEntry fuel bound entry⟩, List.mem_map.mpr ⟨entry, hMem, rfl⟩, ?_⟩
    rw [hBlk]
  simp [reports, hAny]

/-! ## Named Constitutional Suites Covering All 4 Tiers -/

def exprDamageExceeds : LawProp :=
  .lt (.var 0) (.sub (.var 0) (.var 1))

def exprBuggyDamageExceeds : LawProp :=
  .lt (.var 0) (.add (.var 0) (.var 1))

def compactStatusLaw : ConstitutionalLaw :=
  .deepInvariant "compact_status_round_trip"
    (∀ val : CompactValue statusCompactADT,
      statusCompactADT.decode (statusCompactADT.encode val) = some (val.tag, val.payload))

def validEntityConstitution : List CachedLawEntry :=
  [ .uncached (.preservesRecord "movement_preserves_health_team" ⟨[[0], [1]], [[0], [1]], []⟩ [[2], [3]])
  , .uncached (.preservesCollection "soa_pos_vel_preserves_health" [0, 1] [2])
  , .uncached (.alwaysFiniteRepr "status_round_trip" statusDomain
      (fun s => Status.decode (Status.encode s) == some s))
  , .uncached (.neverSymbolic "bounded_damage" [] exprDamageExceeds)
  , .uncached (.alwaysSymbolic "damage_exact" [] exprDamageRecovery)
  , .withCachedProof compactStatusLaw (fun val => CompactADT.decode_encode statusCompactADT_valid val)
  ]

def buggyDamageConstitution : List CachedLawEntry :=
  [ .uncached (.neverSymbolic "buggy_additive_damage" [] exprBuggyDamageExceeds) ]

def buggyFrameConstitution : List CachedLawEntry :=
  [ .uncached (.preservesRecord "buggy_frame" ⟨[], [[0]], []⟩ [[0]]) ]

def buggyDecoderConstitution : List CachedLawEntry :=
  [ .uncached (.alwaysFiniteRepr "buggy_const_decoder" statusDomain
      (fun s => some Status.idle == some s)) ]

theorem validEntityConstitution_holds :
    ∀ entry ∈ validEntityConstitution, entry.law.Holds := by
  intro entry hMem
  simp only [validEntityConstitution, List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (checkEffectPreserves_correct _ _).mp movement_frame_discharged
  · exact (checkCollectionPreserves_correct _ _).mp (by decide)
  · intro s
    simp [Status.decode_encode s]
  · intro env _ hBad
    exact law_bounded_damage_proved (env 0) (env 1) hBad
  · intro env _ hLe
    exact law_damage_recovery_proved (env 0) (env 1) hLe
  · intro val
    exact CompactADT.decode_encode statusCompactADT_valid val

theorem validEntityConstitution_admitted :
    ∃ reports, checkConstitution 12 6 validEntityConstitution = .allPassed reports := by
  apply checkConstitution_allPassed_of_admitted
  intro entry hMem
  simp only [validEntityConstitution, List.mem_cons, List.not_mem_nil, or_false] at hMem
  rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl
  · refine ⟨.tier0Frame, ?_⟩
    dsimp [checkEntry, CachedLawEntry.uncached]
    rw [movement_frame_discharged]
    rfl
  · refine ⟨.tier0Frame, ?_⟩
    dsimp [checkEntry, CachedLawEntry.uncached]
    rw [show checkCollectionPreserves [0, 1] [2] = true by decide]
    rfl
  · refine ⟨.tier1Finite, ?_⟩
    dsimp [checkEntry, CachedLawEntry.uncached, ConstitutionalLaw.alwaysFiniteRepr]
    rw [status_roundTrip_exhaustive]
  · refine ⟨.tier2Symbolic, ?_⟩
    dsimp [checkEntry, CachedLawEntry.uncached]
    rw [show autoProveNorm [] 12 (.not exprDamageExceeds) = true by decide]
    rfl
  · refine ⟨.tier2Symbolic, ?_⟩
    dsimp [checkEntry, CachedLawEntry.uncached]
    rw [show autoProveNorm [] 12 exprDamageRecovery = true by decide]
    rfl
  · exact ⟨.tier3CachedProof, rfl⟩

theorem buggyDamageConstitution_blocked :
    ∃ reports, checkConstitution 12 6 buggyDamageConstitution = .blocked reports := by
  apply checkConstitution_blocks_counterexample
    (entry := .uncached (.neverSymbolic "buggy_additive_damage" [] exprBuggyDamageExceeds))
    (witness := "v0=0, v1=1, v2=0")
  · simp [buggyDamageConstitution]
  · dsimp [checkEntry, CachedLawEntry.uncached]
    rw [show autoProveNorm [] 12 (.not exprBuggyDamageExceeds) = false by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [show falsifySymbolic 6 [] (.not exprBuggyDamageExceeds) = some (0, 1, 0) by decide]
    rfl

theorem buggyFrameConstitution_blocked :
    ∃ reports, checkConstitution 12 6 buggyFrameConstitution = .blocked reports := by
  apply checkConstitution_blocks_counterexample
    (entry := .uncached (.preservesRecord "buggy_frame" ⟨[], [[0]], []⟩ [[0]]))
    (witness := "effect writes or invalidates a preserved field path")
  · simp [buggyFrameConstitution]
  · dsimp [checkEntry, CachedLawEntry.uncached]
    rw [self_write_frame_rejected]
    rfl

theorem buggyDecoderConstitution_blocked :
    ∃ reports, checkConstitution 12 6 buggyDecoderConstitution = .blocked reports := by
  apply checkConstitution_blocks_counterexample
    (entry := .uncached (.alwaysFiniteRepr "buggy_const_decoder" statusDomain
      (fun s => some Status.idle == some s)))
    (witness := toString (repr Status.dead))
  · simp [buggyDecoderConstitution]
  · dsimp [checkEntry, CachedLawEntry.uncached, ConstitutionalLaw.alwaysFiniteRepr]
    rw [show verifyExhaustive statusDomain (fun s => Status.idle == s) = .falsified .dead by decide]

end Aethel.ConstitutionalLaws
