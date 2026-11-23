import Aethel.CoreSoundnessFull

namespace Aethel.CoreSoundness.Tests

open Functional Core Structured CoreAST CoreSemantics CoreSoundness

def run : IO Unit := do
  let emptyState : State := ⟨[], [], [], [], []⟩

  -- Test 1: Value effect emptiness on primitives
  have hValNat : Value (.nat 42) := .nat 42
  have hNatTyped : WellTyped [] (.nat 42) .nat .empty := .nat [] 42
  have hEffNatEq : Effect.empty = Effect.empty := value_effect_empty hValNat hNatTyped
  have _ := hEffNatEq

  -- Test 2: Value effect emptiness on composite pairs
  have hValPair : Value (.pair (.nat 1) (.bool true)) := .pair (.nat 1) (.bool true)
  have hPairTyped : WellTyped [] (.pair (.nat 1) (.bool true)) (.prod .nat .bool) .empty := by
    have hp := WellTyped.pair (.nat [] 1) (.bool [] true)
    simp only [Effect.union_empty_left] at hp
    exact hp
  have hEffPairEq : Effect.empty = Effect.empty := value_effect_empty hValPair hPairTyped
  have _ := hEffPairEq

  -- Test 3: Progress on irreducible value
  have hSeqNat : IsSequentialCore (.nat 100) := .nat 100
  have hProgVal : Value (.nat 100) ∨ ∃ s' e', Step emptyState (.nat 100) s' e' :=
    progress (.nat 100) hSeqNat .nat .empty (.nat [] 100) emptyState
  have _ := hProgVal

  -- Test 4: Progress on redex (pair projection)
  have hSeqProj : IsSequentialCore (.fst (.pair (.nat 10) (.nat 20))) :=
    .fst (.pair (.nat 10) (.nat 20))
  have hProjTyped : WellTyped [] (.fst (.pair (.nat 10) (.nat 20))) .nat .empty := by
    have hp := WellTyped.pair (.nat [] 10) (.nat [] 20)
    simp only [Effect.union_empty_left] at hp
    exact .fst hp
  have hProgRedex : Value (.fst (.pair (.nat 10) (.nat 20))) ∨ ∃ s' e', Step emptyState (.fst (.pair (.nat 10) (.nat 20))) s' e' :=
    progress (.fst (.pair (.nat 10) (.nat 20))) hSeqProj .nat .empty hProjTyped emptyState
  have _ := hProgRedex

  -- Test 5: Progress on let-binding
  have hSeqLet : IsSequentialCore (.letBind 0 (.nat 5) (.var 0)) :=
    .letBind 0 (.nat 5) (.var 0)
  have hLetTyped : WellTyped [] (.letBind 0 (.nat 5) (.var 0)) .nat .empty := by
    have hV : WellTyped [] (.nat 5) .nat .empty := .nat [] 5
    have hB : WellTyped [(0, .nat)] (.var 0) .nat .empty := .var 0 rfl
    have hL := WellTyped.letBind 0 hV hB
    simp only [Effect.union_empty_left] at hL
    exact hL
  have hProgLet : Value (.letBind 0 (.nat 5) (.var 0)) ∨ ∃ s' e', Step emptyState (.letBind 0 (.nat 5) (.var 0)) s' e' :=
    progress (.letBind 0 (.nat 5) (.var 0)) hSeqLet .nat .empty hLetTyped emptyState
  have _ := hProgLet

  -- Test 6: Progress on lambda application (beta redex)
  have hSeqApp : IsSequentialCore (.app (.lam 0 .nat (.var 0) .empty) (.nat 77)) :=
    .app (.lam 0 .nat .empty (.var 0)) (.nat 77)
  have hAppTyped : WellTyped [] (.app (.lam 0 .nat (.var 0) .empty) (.nat 77)) .nat .empty := by
    have hLam : WellTyped [] (.lam 0 .nat (.var 0) .empty) (.arrow .nat .nat .empty) .empty :=
      .lam 0 .nat .empty (.var 0 rfl)
    have hArg : WellTyped [] (.nat 77) .nat .empty := .nat [] 77
    have hA := WellTyped.app hLam hArg
    simp only [Effect.union_empty_left] at hA
    exact hA
  have hProgApp : Value (.app (.lam 0 .nat (.var 0) .empty) (.nat 77)) ∨ ∃ s' e', Step emptyState (.app (.lam 0 .nat (.var 0) .empty) (.nat 77)) s' e' :=
    progress (.app (.lam 0 .nat (.var 0) .empty) (.nat 77)) hSeqApp .nat .empty hAppTyped emptyState
  have _ := hProgApp

  -- Test 7: Progress on loop unrolling
  have hSeqLoop : IsSequentialCore (.loop (.bool true) .unit) :=
    .loop (.bool true) .unit
  have hLoopTyped : WellTyped [] (.loop (.bool true) .unit) .unit .empty := by
    have hC : WellTyped [] (.bool true) .bool .empty := .bool [] true
    have hB : WellTyped [] .unit .unit .empty := .unit []
    have hL := WellTyped.loop hC hB
    simp only [Effect.union_empty_left] at hL
    exact hL
  have hProgLoop : Value (.loop (.bool true) .unit) ∨ ∃ s' e', Step emptyState (.loop (.bool true) .unit) s' e' :=
    progress (.loop (.bool true) .unit) hSeqLoop .unit .empty hLoopTyped emptyState
  have _ := hProgLoop

  -- Test 8: Progress on matchBool true
  have hSeqMatch : IsSequentialCore (.matchTag (.bool true) 1 (.nat 1) (.nat 0)) :=
    .matchTag 1 (.bool true) (.nat 1) (.nat 0)
  have hMatchTyped : WellTyped [] (.matchTag (.bool true) 1 (.nat 1) (.nat 0)) .nat .empty := by
    have hS : WellTyped [] (.bool true) .bool .empty := .bool [] true
    have hT : WellTyped [] (.nat 1) .nat .empty := .nat [] 1
    have hF : WellTyped [] (.nat 0) .nat .empty := .nat [] 0
    have hM := WellTyped.matchBool hS hT hF
    simp only [Effect.union_empty_left] at hM
    exact hM
  have hProgMatch : Value (.matchTag (.bool true) 1 (.nat 1) (.nat 0)) ∨ ∃ s' e', Step emptyState (.matchTag (.bool true) 1 (.nat 1) (.nat 0)) s' e' :=
    progress (.matchTag (.bool true) 1 (.nat 1) (.nat 0)) hSeqMatch .nat .empty hMatchTyped emptyState
  have _ := hProgMatch

  -- Test 9: Context weakening preserves closed typing
  have hWeakened : WellTyped [(0, .nat), (1, .bool)] (.nat 99) .nat .empty :=
    wellTyped_closed_weaken (.nat [] 99) [(0, .nat), (1, .bool)]
  have _ := hWeakened

  -- Test 10: Value substitution theorem
  have hSubstStep := substitution_step (val := .nat 42) (.nat 42) (.nat [] 42) (.var 0) (ctx := [])
    (varId := 0) (tyBody := .nat) (effBody := .empty) (.var 0 rfl)
  have _ := hSubstStep

  -- Test 11: Preservation on projection step
  have hStepProj := Step.fst_val (s := emptyState) (.nat 10) (.nat 20)
  have hPresProj := preservation hStepProj hProjTyped
  have _ : ∃ eff', WellTyped [] (CoreExpr.nat 10) .nat eff' := hPresProj

  -- Test 12: Preservation on beta reduction
  have hStepBeta := Step.app_beta (s := emptyState) 0 .nat (.var 0) .empty (.nat 77)
  have hPresBeta := preservation hStepBeta hAppTyped
  have _ : ∃ eff', WellTyped [] (subst 0 (.nat 77) (.var 0)) .nat eff' := hPresBeta

  -- Test 13: Preservation on loop unrolling
  have hStepLoop := Step.loop_step (s := emptyState) (cond := .bool true) (body := .unit)
  have hPresLoop := preservation hStepLoop hLoopTyped
  have _ : ∃ eff', WellTyped [] (.matchTag (.bool true) 1 (.letBind 0 .unit (.loop (.bool true) .unit)) .unit) .unit eff' := hPresLoop

  -- Test 14: Proof erasure simulation
  have hErasedSim := proof_erasure_simulation hStepBeta
  have _ : ErasedStep emptyState
    (erase (.app (.lam 0 .nat (.var 0) .empty) (.nat 77)))
    emptyState
    (erase (subst 0 (.nat 77) (.var 0))) := hErasedSim

  -- Test 15: Proof erasure independence
  have hStepApp1 := Step.app_beta (s := emptyState) 0 .nat (.var 0) .empty (.nat 42)
  have heqApp : erase (.app (.lam 0 .nat (.var 0) .empty) (.nat 42)) =
                erase (.app (.lam 0 .bool (.var 0) ⟨[[1, 2]], [], []⟩) (.nat 42)) := rfl
  have hErasureIndep := proof_erasure_same_step
    (.app (.lam 0 .nat (.var 0) .empty) (.nat 42))
    (.app (.lam 0 .bool (.var 0) ⟨[[1, 2]], [], []⟩) (.nat 42))
    heqApp hStepApp1
  have _ : ErasedStep emptyState
    (erase (.app (.lam 0 .bool (.var 0) ⟨[[1, 2]], [], []⟩) (.nat 42)))
    emptyState
    (erase (subst 0 (.nat 42) (.var 0))) := hErasureIndep

  IO.println "15 unified sequential core soundness and proof erasure regressions passed"

end Aethel.CoreSoundness.Tests
