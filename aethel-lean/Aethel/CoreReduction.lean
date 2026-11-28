import Aethel.CoreChecking

namespace Aethel.CoreSemantics

open Core CoreAST

structure Reduction (expression : CoreExpr) where
  next : CoreExpr
  steps : ∀ state, Step state expression state next

private def projectValue (pickFirst : Bool) (expression : CoreExpr) :
    Option (Reduction (if pickFirst then .fst expression else .snd expression)) :=
  match expression with
  | .pair first second =>
    if ready : isVal first = true ∧ isVal second = true then
      have firstVal := (isVal_correct first).mp ready.1
      have secondVal := (isVal_correct second).mp ready.2
      match pickFirst with
      | true => some ⟨first, fun _ => .fst_val firstVal secondVal⟩
      | false => some ⟨second, fun _ => .snd_val firstVal secondVal⟩
    else none
  | _ => none

private def selectValue (input : CoreExpr) (tag : Nat) (yes no : CoreExpr) :
    Option (Reduction (.matchTag input tag yes no)) :=
  match input with
  | .adt actual payload =>
    if ready : isVal payload = true then
      if same : actual = tag then
        some ⟨yes, fun _ => same ▸ .match_hit actual ((isVal_correct payload).mp ready)⟩
      else
        some ⟨no, fun _ => .match_miss actual tag same ((isVal_correct payload).mp ready)⟩
    else none
  | .bool true =>
    if same : tag = 1 then some ⟨yes, fun _ => same.symm ▸ .match_bool_true⟩ else none
  | .bool false =>
    if same : tag = 1 then some ⟨no, fun _ => same.symm ▸ .match_bool_false⟩ else none
  | _ => none

private def selectSum (input : CoreExpr) (binder : Nat) (onLeft onRight : CoreExpr) :
    Option (Reduction (.matchSum input binder onLeft onRight)) :=
  match input with
  | .inject side variants payload =>
    if ready : isVal payload = true then
      some ⟨.letBind binder payload (if side then onLeft else onRight),
        fun _ => .sum_select side variants binder ((isVal_correct payload).mp ready)⟩
    else none
  | _ => none

/-- One call-by-value reduction, with a witness from the small-step semantics. -/
def reduce : (expression : CoreExpr) → Option (Reduction expression)
  | .pair first second =>
    if ready : isVal first = true then
      (reduce second).map fun move => ⟨.pair first move.next, fun state =>
        .pair_right ((isVal_correct first).mp ready) (move.steps state)⟩
    else
      (reduce first).map fun move => ⟨.pair move.next second, fun state => .pair_left (move.steps state)⟩
  | .fst product =>
    (projectValue true product).orElse fun _ =>
      (reduce product).map fun move => ⟨.fst move.next, fun state => .fst_eval (move.steps state)⟩
  | .snd product =>
    (projectValue false product).orElse fun _ =>
      (reduce product).map fun move => ⟨.snd move.next, fun state => .snd_eval (move.steps state)⟩
  | .inject side variants payload =>
    (reduce payload).map fun move => ⟨.inject side variants move.next, fun state =>
      .inject_eval side variants (move.steps state)⟩
  | .matchSum input binder onLeft onRight =>
    (selectSum input binder onLeft onRight).orElse fun _ => (reduce input).map fun move =>
      ⟨.matchSum move.next binder onLeft onRight, fun state => .sum_eval binder (move.steps state)⟩
  | .adt tag payload =>
    (reduce payload).map fun move => ⟨.adt tag move.next, fun state => .adt_eval tag (move.steps state)⟩
  | .matchTag input tag yes no =>
    (selectValue input tag yes no).orElse fun _ => (reduce input).map fun move =>
      ⟨.matchTag move.next tag yes no, fun state => .match_eval tag (move.steps state)⟩
  | .letBind id value body =>
    if ready : isVal value = true then
      some ⟨subst id value body, fun _ => .let_subst id ((isVal_correct value).mp ready)⟩
    else (reduce value).map fun move =>
      ⟨.letBind id move.next body, fun state => .let_eval id (move.steps state)⟩
  | .app function arg =>
    if functionReady : isVal function = true then
      if argReady : isVal arg = true then
        match function with
        | .lam param type body effect =>
          some ⟨subst param arg body, fun _ => .app_beta param type body effect ((isVal_correct arg).mp argReady)⟩
        | _ => none
      else (reduce arg).map fun move =>
        ⟨.app function move.next, fun state => .app_arg ((isVal_correct function).mp functionReady)
          (move.steps state)⟩
    else (reduce function).map fun move => ⟨.app move.next arg, fun state => .app_fn (move.steps state)⟩
  | .loop test body => some ⟨.matchTag test 1 (.letBind 0 body (.loop test body)) .unit, fun _ => .loop_step⟩
  | _ => none

private theorem Step.not_ready {state nextState : State} {expression next : CoreExpr}
    (step : Step state expression nextState next) : isVal expression = false :=
  Bool.eq_false_iff.mpr fun ready => step_val_impossible step ((isVal_correct _).mp ready)

private theorem orElse_has_reduction {α : Type} (first second : Option α)
    (available : second.isSome = true) :
    (first.orElse fun _ => second).isSome = true := by
  cases first
  · exact available
  · rfl

private theorem Step.has_reduction {state nextState : State} {expression next : CoreExpr}
    (step : Step state expression nextState next) : (reduce expression).isSome = true := by
  induction step with
  | pair_left step ih => simp [reduce, step.not_ready, ih]
  | pair_right value _ ih => simp [reduce, (isVal_correct _).mpr value, ih]
  | fst_eval _ ih => rw [reduce]; exact orElse_has_reduction _ _ (by simpa using ih)
  | snd_eval _ ih => rw [reduce]; exact orElse_has_reduction _ _ (by simpa using ih)
  | fst_val first second => simp [reduce, projectValue, (isVal_correct _).mpr first, (isVal_correct _).mpr second,
      Option.orElse]
  | snd_val first second => simp [reduce, projectValue, (isVal_correct _).mpr first, (isVal_correct _).mpr second,
      Option.orElse]
  | inject_eval _ _ _ ih => simp [reduce, ih]
  | sum_eval _ _ ih => rw [reduce]; exact orElse_has_reduction _ _ (by simpa using ih)
  | sum_select _ _ _ ready => simp [reduce, selectSum, (isVal_correct _).mpr ready, Option.orElse]
  | adt_eval _ _ ih => simp [reduce, ih]
  | match_eval _ _ ih => rw [reduce]; exact orElse_has_reduction _ _ (by simpa using ih)
  | match_hit _ value => simp [reduce, selectValue, (isVal_correct _).mpr value, Option.orElse]
  | match_miss _ _ different value =>
    simp [reduce, selectValue, (isVal_correct _).mpr value, different, Option.orElse]
  | match_bool_true => rfl
  | match_bool_false => rfl
  | let_eval _ step ih => simp [reduce, step.not_ready, ih]
  | let_subst _ value => simp [reduce, (isVal_correct _).mpr value]
  | app_fn step ih => simp [reduce, step.not_ready, ih]
  | app_arg value step ih => simp [reduce, (isVal_correct _).mpr value, step.not_ready, ih]
  | app_beta _ _ _ _ value => simp [reduce, isVal, (isVal_correct _).mpr value]
  | loop_step => rfl

theorem reduce_correct (state nextState : State) (expression next : CoreExpr) :
    (reduce expression).map Reduction.next = some next ∧ nextState = state
      ↔ Step state expression nextState next := by
  constructor
  · rintro ⟨found, sameState⟩
    subst nextState
    obtain ⟨reduction, _, rfl⟩ := Option.map_eq_some_iff.mp found
    exact reduction.steps state
  · intro step
    obtain ⟨reduction, found⟩ := Option.isSome_iff_exists.mp step.has_reduction
    obtain ⟨sameState, sameResult⟩ := step.deterministic (reduction.steps state)
    exact ⟨Option.map_eq_some_iff.mpr ⟨reduction, found, sameResult.symm⟩, sameState⟩

inductive Reduces (state : State) : CoreExpr → CoreExpr → Prop where
  | refl (expression : CoreExpr) : Reduces state expression expression
  | step : Step state expression state next → Reduces state next final → Reduces state expression final

theorem Reduces.append {state : State} {expression middle final : CoreExpr}
    (first : Reduces state expression middle) (rest : Reduces state middle final) :
    Reduces state expression final := by
  induction first with
  | refl => exact rest
  | step first _ ih => exact .step first (ih rest)

theorem Reduces.under {state : State} {expression final : CoreExpr}
    (ran : Reduces state expression final) (wrap : CoreExpr → CoreExpr)
    (lift : ∀ {before after}, Step state before state after → Step state (wrap before) state (wrap after)) :
    Reduces state (wrap expression) (wrap final) := by
  induction ran with
  | refl => exact .refl _
  | step first _ ih => exact .step (lift first) ih

theorem Reduces.in_state {original : State} {expression final : CoreExpr}
    (reductions : Reduces original expression final) (state : State) :
    Reduces state expression final := by
  induction reductions with
  | refl => exact .refl _
  | step step _ ih =>
    have found := ((reduce_correct ..).mpr step).1
    exact .step ((reduce_correct ..).mp ⟨found, rfl⟩) ih

def ReductionOrder (next before : CoreExpr) : Prop :=
  Step {} before {} next

theorem Reduces.accessible {expression final : CoreExpr} (ran : Reduces {} expression final)
    (value : Value final) : Acc ReductionOrder expression := by
  induction ran with
  | refl =>
    constructor
    intro _ impossible
    exact False.elim (step_val_impossible impossible value)
  | step first _ ih =>
    constructor
    intro next other
    have same := (first.deterministic other).2
    exact same ▸ ih value

abbrev TerminatingExpr := { expression : CoreExpr // Acc ReductionOrder expression }

private instance : WellFoundedRelation TerminatingExpr where
  rel := InvImage ReductionOrder Subtype.val
  wf := ⟨fun expression => InvImage.accessible Subtype.val expression.property⟩

/-- Evaluate using proved termination. The accessibility witness and
permission-independent step proofs erase from the executable. -/
def reduceUntilValue (expression : TerminatingExpr) : CoreExpr :=
  match reduce expression.val with
  | none => expression.val
  | some reduction =>
    reduceUntilValue ⟨reduction.next, expression.property.inv (reduction.steps {})⟩
termination_by expression
decreasing_by exact reduction.steps {}

theorem reduceUntilValue_correct {expression final : CoreExpr}
    (ran : Reduces {} expression final) (value : Value final) (accessible : Acc ReductionOrder expression) :
    reduceUntilValue ⟨expression, accessible⟩ = final := by
  induction ran with
  | refl =>
    rw [reduceUntilValue]
    split
    · rfl
    · rename_i reduction _
      exact False.elim (step_val_impossible (reduction.steps {}) value)
  | step first _ ih =>
    obtain ⟨reduction, found, rfl⟩ := Option.map_eq_some_iff.mp ((reduce_correct ..).mpr first).1
    rw [reduceUntilValue, found]
    exact ih value _

theorem Reduces.final_unique {expression left right : CoreExpr}
    (first : Reduces {} expression left) (second : Reduces {} expression right)
    (leftValue : Value left) (rightValue : Value right) : left = right :=
  let accessible := first.accessible leftValue
  (reduceUntilValue_correct first leftValue accessible).symm.trans
    (reduceUntilValue_correct second rightValue accessible)

theorem Reduces.preservation {state : State} {expression final : CoreExpr}
    (reductions : Reduces state expression final) {type : CoreType} {effect : Effect}
    (typed : WellTyped [] expression type effect) :
    ∃ remaining, WellTyped [] final type remaining := by
  induction reductions generalizing effect with
  | refl => exact ⟨effect, typed⟩
  | step step _ ih =>
    obtain ⟨_, nextTyped⟩ := CoreSoundness.preservation step typed
    exact ih nextTyped

end Aethel.CoreSemantics
