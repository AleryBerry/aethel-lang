import Aethel.PermissionLattice
import Aethel.AffineIndex
import Aethel.FunctionSummaries
import Aethel.LawFrameDischarge

namespace Aethel.InterprocBorrow

open Aethel Aethel.Core Aethel.Permissions Aethel.LawFrameDischarge

/-!
## Stage A Inter-Procedural & Advanced Borrow Verification

Builds kernel-checked MIR verification bridges for:
1. Two-phase lazy permission traces (`reserved` -> `activeExclusive` / `frozen`)
   over `PermissionLattice.lean`.
2. Transitive inter-procedural effect composition (`Effect.union`) and returned
   caller-rooted view origin validation (`Origin`).
3. Affine index (`i != j`, `i + 1`) and symbolic half-open slice (`arr[0..mid]` vs
   `arr[mid..n]`) disjointness certificates over `AffineIndex.lean`.
-/

/-- Canonical empty-view initial permission state for a single local record/slice buffer. -/
def initPermState (allocSize : Nat) : PermState :=
  { base := ({} : Core.State).addAllocation 0 (List.replicate allocSize 0), pviews := [] }

theorem initPermState_valid (allocSize : Nat) : (initPermState allocSize).Valid := by
  refine ⟨List.Pairwise.nil, ?_⟩
  intro v hv
  cases hv

/-- Independent mathematical specification of a legal two-phase permission trace
that releases all borrowed views before return. -/
def PermTraceValid (allocSize : Nat) (trace : List PermInstr) : Prop :=
  ∃ final, PermRuns (initPermState allocSize) trace final ∧ final.Valid ∧ final.pviews = []

/-- Executable validator for a serialized two-phase borrow trace. -/
def verifyPermTrace (allocSize : Nat) (trace : List PermInstr) : Bool :=
  match runPerm (initPermState allocSize) trace with
  | some final => final.pviews.isEmpty
  | none => false

theorem verifyPermTrace_correct (allocSize : Nat) (trace : List PermInstr) :
    verifyPermTrace allocSize trace = true ↔ PermTraceValid allocSize trace := by
  dsimp [verifyPermTrace, PermTraceValid]
  constructor
  · intro hOk
    cases hRun : runPerm (initPermState allocSize) trace with
    | none => simp [hRun] at hOk
    | some final =>
      rw [hRun] at hOk
      dsimp only at hOk
      have hRuns := runPerm_sound hRun
      have hValid := hRuns.preserves_valid (initPermState_valid allocSize)
      have hEmpty : final.pviews = [] := by
        cases hp : final.pviews with
        | nil => rfl
        | cons _ _ => simp [hp] at hOk
      exact ⟨final, hRuns, hValid, hEmpty⟩
  · rintro ⟨final, hRuns, _, hEmpty⟩
    have hRun := runPerm_complete hRuns
    rw [hRun]
    simp [hEmpty]

/-- Positive witness: two-phase `reserved` mutable view coexists with a concurrent
`shared` read until the reader releases, then activates and writes safely. -/
theorem twoPhase_read_before_write_valid :
    verifyPermTrace 8
      [ .reserve 0 ⟨0, 0⟩ .reserved
      , .reserve 1 ⟨0, 0⟩ .shared
      , .read 1
      , .release 1
      , .activate 0
      , .write 0 42
      , .release 0 ] = true ∧
    PermTraceValid 8
      [ .reserve 0 ⟨0, 0⟩ .reserved
      , .reserve 1 ⟨0, 0⟩ .shared
      , .read 1
      , .release 1
      , .activate 0
      , .write 0 42
      , .release 0 ] := by
  have h : verifyPermTrace 8
      [ .reserve 0 ⟨0, 0⟩ .reserved
      , .reserve 1 ⟨0, 0⟩ .shared
      , .read 1
      , .release 1
      , .activate 0
      , .write 0 42
      , .release 0 ] = true := rfl
  exact ⟨h, (verifyPermTrace_correct 8 _).mp h⟩

/-- Positive witness: early release of a shared reader immediately permits an
exclusive reservation and write in the same block without extra lexical nesting. -/
theorem early_release_reborrow_valid :
    verifyPermTrace 8
      [ .reserve 0 ⟨0, 0⟩ .shared
      , .read 0
      , .release 0
      , .reserve 1 ⟨0, 0⟩ .reserved
      , .activate 1
      , .write 1 9
      , .release 1 ] = true ∧
    PermTraceValid 8
      [ .reserve 0 ⟨0, 0⟩ .shared
      , .read 0
      , .release 0
      , .reserve 1 ⟨0, 0⟩ .reserved
      , .activate 1
      , .write 1 9
      , .release 1 ] := by
  have h : verifyPermTrace 8
      [ .reserve 0 ⟨0, 0⟩ .shared
      , .read 0
      , .release 0
      , .reserve 1 ⟨0, 0⟩ .reserved
      , .activate 1
      , .write 1 9
      , .release 1 ] = true := rfl
  exact ⟨h, (verifyPermTrace_correct 8 _).mp h⟩

/-- Negative counterexample: activating a reserved exclusive view while a shared
reader is still active is rejected. -/
theorem twoPhase_activate_while_shared_rejected :
    verifyPermTrace 8
      [ .reserve 0 ⟨0, 0⟩ .reserved
      , .reserve 1 ⟨0, 0⟩ .shared
      , .activate 0
      , .release 1
      , .release 0 ] = false := rfl

/-- Transitive call-graph effect composition: a compound effect preserves a frame
if and only if every constituent callee effect preserves it. -/
theorem effectPreserves_union_iff (e1 e2 : Effect) (preserved : List (List Nat)) :
    EffectPreserves (e1.union e2) preserved ↔
      EffectPreserves e1 preserved ∧ EffectPreserves e2 preserved := by
  simp only [EffectPreserves, Effect.union, List.mem_append]
  constructor
  · intro h
    refine ⟨fun p hp => ⟨fun w hw => (h p hp).1 w (Or.inl hw), fun i hi => (h p hp).2 i (Or.inl hi)⟩,
            fun p hp => ⟨fun w hw => (h p hp).1 w (Or.inr hw), fun i hi => (h p hp).2 i (Or.inr hi)⟩⟩
  · rintro ⟨h1, h2⟩ p hp
    refine ⟨?_, ?_⟩
    · intro w hw
      rcases hw with hw1 | hw2
      · exact (h1 p hp).1 w hw1
      · exact (h2 p hp).1 w hw2
    · intro i hi
      rcases hi with hi1 | hi2
      · exact (h1 p hp).2 i hi1
      · exact (h2 p hp).2 i hi2

theorem checkEffectPreserves_union (e1 e2 : Effect) (preserved : List (List Nat)) :
    checkEffectPreserves (e1.union e2) preserved =
      (checkEffectPreserves e1 preserved && checkEffectPreserves e2 preserved) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true, checkEffectPreserves_correct, effectPreserves_union_iff]

/-- Executable check for returned view origin validity against caller parameters. -/
def checkReturnedOrigin : Origin → Nat → Bool
  | .param i, paramCount => decide (i < paramCount)
  | .global, _ => true
  | .fresh, _ => false

/-- Independent specification: returned views must resolve to a live caller handle or global. -/
def ReturnedOriginValid (origin : Origin) (args : List HandleId) : Prop :=
  match origin with
  | .param _ => ∃ h, origin.resolve args = some h
  | .global => True
  | .fresh => False

theorem checkReturnedOrigin_sound {origin : Origin} {args : List HandleId}
    (h : checkReturnedOrigin origin args.length = true) :
    ReturnedOriginValid origin args := by
  cases origin with
  | param i =>
    simp only [checkReturnedOrigin, decide_eq_true_eq] at h
    exact ⟨args[i], Origin.resolve_param_in_bounds h⟩
  | global => trivial
  | fresh => cases h

/-- Negative counterexample: returning a view rooted in a stack-local allocation is rejected. -/
theorem returned_local_origin_rejected (args : List HandleId) :
    checkReturnedOrigin .fresh args.length = false ∧ ¬ ReturnedOriginValid .fresh args := by
  exact ⟨rfl, fun h => h⟩

/-- Disjointness goals emitted for guarded element indexing and split slicing. -/
inductive MIRDisjointGoal where
  | idxNe (a b : IdxExpr)
  | sliceDisjoint (s1 s2 : SymbolicSlice)
  deriving Repr, DecidableEq

/-- Certificate pairing an established order-fact context with a disjointness goal. -/
structure MIRDisjointCert where
  env : OrderFactEnv
  goal : MIRDisjointGoal
  deriving Repr

/-- Independent mathematical specification: under every valuation satisfying `c.env`,
the two accesses refer to distinct indices or disjoint half-open intervals. -/
def MIRDisjointCert.Valid (c : MIRDisjointCert) : Prop :=
  ∀ ν : Nat → Nat, c.env.Valid ν →
    match c.goal with
    | .idxNe a b => a.eval ν ≠ b.eval ν
    | .sliceDisjoint s1 s2 => ∀ idx, ¬ ((s1.eval ν).Contains idx ∧ (s2.eval ν).Contains idx)

def checkDisjointCert (c : MIRDisjointCert) : Bool :=
  match c.goal with
  | .idxNe a b => c.env.provesNe a b
  | .sliceDisjoint s1 s2 => c.env.slicesDisjoint s1 s2

theorem checkDisjointCert_sound {c : MIRDisjointCert}
    (h : checkDisjointCert c = true) : c.Valid := by
  intro ν hEnv
  cases hGoal : c.goal with
  | idxNe a b =>
    simp only [checkDisjointCert, hGoal] at h
    exact OrderFactEnv.provesNe_sound hEnv h
  | sliceDisjoint s1 s2 =>
    simp only [checkDisjointCert, hGoal] at h
    intro idx
    exact OrderFactEnv.slicesDisjoint_sound hEnv h

/-- Positive witness: `if i != j` proves `arr[i]` and `arr[j]` disjoint. -/
theorem cert_guarded_ne_valid :
    let cert : MIRDisjointCert :=
      ⟨{ base := FactEnv.assumeNe {} (.value 0) (.value 1) }, .idxNe (.value 0) (.value 1)⟩
    checkDisjointCert cert = true ∧ cert.Valid := by
  have h : checkDisjointCert
      ⟨{ base := FactEnv.assumeNe {} (.value 0) (.value 1) }, .idxNe (.value 0) (.value 1)⟩ = true := rfl
  exact ⟨h, checkDisjointCert_sound h⟩

/-- Positive witness: affine offset `i` vs `i + 1` is unconditionally disjoint. -/
theorem cert_adjacent_offset_valid :
    let cert : MIRDisjointCert := ⟨{}, .idxNe (.value 0) (.add (.value 0) (.const 1))⟩
    checkDisjointCert cert = true ∧ cert.Valid := by
  have h : checkDisjointCert
      ⟨{}, .idxNe (.value 0) (.add (.value 0) (.const 1))⟩ = true := rfl
  exact ⟨h, checkDisjointCert_sound h⟩

/-- Positive witness: half-open slices `arr[0..mid]` and `arr[mid..n]` are disjoint. -/
theorem cert_split_slice_valid :
    let cert : MIRDisjointCert :=
      ⟨{}, .sliceDisjoint ⟨.const 0, .value 0⟩ ⟨.value 0, .value 1⟩⟩
    checkDisjointCert cert = true ∧ cert.Valid := by
  have h : checkDisjointCert
      ⟨{}, .sliceDisjoint ⟨.const 0, .value 0⟩ ⟨.value 0, .value 1⟩⟩ = true := rfl
  exact ⟨h, checkDisjointCert_sound h⟩

/-- Negative counterexample: unguarded `arr[i]` vs `arr[j]` fails validation. -/
theorem cert_unguarded_indices_rejected :
    checkDisjointCert ⟨{}, .idxNe (.value 0) (.value 1)⟩ = false := rfl

end Aethel.InterprocBorrow
