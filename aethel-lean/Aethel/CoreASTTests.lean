import Aethel.CoreAST
import Aethel.CoreSemantics

namespace Aethel.CoreAST.Tests

open Functional Core Structured CoreAST CoreSemantics

def runCoreASTTests : IO Unit := do
  -- Test 1: Value classification of primitives
  if !isVal .unit then throw (IO.userError "unit should be a value")
  if !isVal (.bool true) then throw (IO.userError "bool should be a value")
  if !isVal (.nat 42) then throw (IO.userError "nat should be a value")
  if !isVal (.int false 8 255) then throw (IO.userError "uint8 should be a value")
  if isVal (.var 0) then throw (IO.userError "var should not be a value")

  -- Test 2: Pairs and nested values
  let pVal := CoreExpr.pair (.nat 1) (.bool false)
  if !isVal pVal then throw (IO.userError "pair of values should be a value")
  let pNonVal := CoreExpr.pair (.nat 1) (.var 0)
  if isVal pNonVal then throw (IO.userError "pair with var should not be a value")

  -- Test 3: ADT values
  let adtVal := CoreExpr.adt 10 (.nat 100)
  if !isVal adtVal then throw (IO.userError "adt with val payload should be value")

  -- Test 4: Variable substitution
  let eVar := CoreExpr.var 0
  let eSub := subst 0 (.nat 99) eVar
  if eSub != .nat 99 then throw (IO.userError "subst failed on matching var")
  let eOther := subst 1 (.nat 99) eVar
  if eOther != .var 0 then throw (IO.userError "subst altered non-matching var")

  -- Test 5: Lexical shadowing in letBind and lam
  let eLetShadow := CoreExpr.letBind 0 (.var 0) (.var 0)
  let eLetSub := subst 0 (.nat 99) eLetShadow
  -- rhs is substituted, but inner body is shadowed:
  if eLetSub != CoreExpr.letBind 0 (.nat 99) (.var 0) then
    throw (IO.userError "subst did not respect let shadowing")

  let eLamShadow := CoreExpr.lam 0 .nat (.var 0) .empty
  let eLamSub := subst 0 (.nat 99) eLamShadow
  if eLamSub != eLamShadow then
    throw (IO.userError "subst did not respect lam shadowing")

  -- Test 6: Static typing of primitives
  have hUnit : WellTyped [] .unit .unit .empty := .unit []
  have hBool : WellTyped [] (.bool true) .bool .empty := .bool [] true
  have hNat : WellTyped [] (.nat 10) .nat .empty := .nat [] 10
  have hByte : WellTyped [] (.int false 8 128) CoreType.byte .empty := .int [] false 8 128
  have _ := hUnit; have _ := hBool; have _ := hNat; have _ := hByte

  -- Test 7: Static typing of pairs and projections
  have hPair : WellTyped [] (.pair (.bool true) (.nat 5)) (.prod .bool .nat) .empty :=
    .pair (.bool [] true) (.nat [] 5)
  have hFst : WellTyped [] (.fst (.pair (.bool true) (.nat 5))) .bool .empty :=
    .fst hPair
  have hSnd : WellTyped [] (.snd (.pair (.bool true) (.nat 5))) .nat .empty :=
    .snd hPair
  have _ := hFst; have _ := hSnd

  -- Test 8: Let binding typing
  have hLet : WellTyped [] (.letBind 0 (.bool true) (.var 0)) .bool .empty :=
    .letBind 0 (.bool [] true) (.var 0 rfl)
  have _ := hLet

  -- Test 9: Lambda and Application typing with effect tracking
  let effRead : Effect := ⟨[[0, 1]], [], []⟩
  have hLam : WellTyped [] (.lam 0 .byte (.readHandle 0 1) effRead) (.arrow .byte .byte effRead) .empty :=
    .lam 0 .byte effRead (.readHandle [(0, .byte)] 0 1)
  have hApp : WellTyped [] (.app (.lam 0 .byte (.readHandle 0 1) effRead) (.int false 8 0)) .byte effRead := by
    have hArg : WellTyped [] (.int false 8 0) .byte .empty := .int [] false 8 0
    have happ := WellTyped.app hLam hArg
    simp only [Effect.union_empty_left] at happ
    exact happ
  have _ := hApp

  -- Test 10: Step reduction of projection
  let emptyState : State := ⟨[], [], [], [], []⟩
  have hValA : Value (.nat 1) := .nat 1
  have hValB : Value (.bool false) := .bool false
  have hStepFst := Step.fst_val (s := emptyState) hValA hValB
  have hStepSnd := Step.snd_val (s := emptyState) hValA hValB
  have _ := hStepFst; have _ := hStepSnd

  -- Test 11: Step reduction of ADT match hit and miss
  have hValP : Value (.nat 7) := .nat 7
  have hHit := Step.match_hit (s := emptyState) 1 (p := .nat 7) (onM := .nat 100) (onE := .nat 0) hValP
  have hMiss := Step.match_miss (s := emptyState) 2 1 (by decide) (p := .nat 7) (onM := .nat 100) (onE := .nat 0) hValP
  have _ := hHit; have _ := hMiss

  -- Test 12: Step reduction of beta reduction
  have hBeta := Step.app_beta (s := emptyState) 0 .nat (.var 0) .empty (v := .nat 42) (.nat 42)
  have _ := hBeta

  -- Test 13: Loop step unrolling
  have hLoop := Step.loop_step (s := emptyState) (cond := .bool true) (body := .unit)
  have _ := hLoop

  -- Test 14: Value impossibility on stepping expressions
  -- Prove that if a value could step, it would yield False
  have hValCantStep : ∀ s' e', ¬ Step emptyState (.nat 1) s' e' := by
    intro s' e' hstep
    exact step_val_impossible hstep (.nat 1)
  have _ := hValCantStep

  -- Test 15: Step determinism
  have hDet := Step.deterministic hStepFst hStepFst
  have _hDetVerified : emptyState = emptyState ∧ CoreExpr.nat 1 = CoreExpr.nat 1 := hDet

  IO.println "15 unified sequential core AST and operational semantics regressions passed"

end Aethel.CoreAST.Tests
