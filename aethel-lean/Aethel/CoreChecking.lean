import Aethel.CoreSoundnessFull

namespace Aethel.CoreAST

open Core

structure Inferred (context : Ctx) (expression : CoreExpr) where
  type : CoreType
  effect : Effect
  typed : WellTyped context expression type effect

private def Inferred.asType {context : Ctx} {expression : CoreExpr}
    (checked : Inferred context expression) (expected : CoreType) :
    Option { effect : Effect // WellTyped context expression expected effect } :=
  if same : checked.type = expected then
    some ⟨checked.effect, same ▸ checked.typed⟩
  else none

/-- Syntax-directed inference for the declarative core typing judgment. -/
def infer : (context : Ctx) → (expression : CoreExpr) → Option (Inferred context expression)
  | ctx, .unit => some ⟨.unit, .empty, .unit ctx⟩
  | ctx, .bool value => some ⟨.bool, .empty, .bool ctx value⟩
  | ctx, .nat value => some ⟨.nat, .empty, .nat ctx value⟩
  | ctx, .int signed bits value =>
    if fits : LiteralFits signed bits value then
      some ⟨.int signed bits, .empty, .int ctx signed bits value fits⟩
    else none
  | ctx, .pair first second => do
    let first ← infer ctx first
    let second ← infer ctx second
    return ⟨.prod first.type second.type, first.effect.union second.effect,
      .pair first.typed second.typed⟩
  | ctx, .fst pair => do
    let pair ← infer ctx pair
    match shape : pair.type with
    | .prod first _ => return ⟨first, pair.effect, .fst (shape ▸ pair.typed)⟩
    | _ => none
  | ctx, .snd pair => do
    let pair ← infer ctx pair
    match shape : pair.type with
    | .prod _ second => return ⟨second, pair.effect, .snd (shape ▸ pair.typed)⟩
    | _ => none
  | ctx, .adt tag payload => do
    let payload ← infer ctx payload
    return ⟨.adt tag payload.type, payload.effect, .adt tag payload.typed⟩
  | ctx, .matchTag input tag yes no => do
    let input ← infer ctx input
    let yes ← infer ctx yes
    let no ← (← infer ctx no).asType yes.type
    let effect := input.effect.union (yes.effect.union no.val)
    match shape : input.type with
    | .adt _ _ =>
      return ⟨yes.type, effect, .matchTag tag (shape ▸ input.typed) yes.typed no.property⟩
    | .bool =>
      if same : tag = 1 then
        return ⟨yes.type, effect, same.symm ▸ .matchBool (shape ▸ input.typed) yes.typed no.property⟩
      else none
    | _ => none
  | ctx, .var id =>
    match found : ctx.lookup id with
    | some type => some ⟨type, .empty, .var id found⟩
    | none => none
  | ctx, .letBind id value body => do
    let value ← infer ctx value
    let body ← infer ((id, value.type) :: ctx) body
    return ⟨body.type, value.effect.union body.effect, .letBind id value.typed body.typed⟩
  | ctx, .alloc size value => some ⟨.handle .byte, _, .alloc ctx size value⟩
  | ctx, .readHandle handle offset => some ⟨.byte, _, .readHandle ctx handle offset⟩
  | ctx, .writeHandle handle offset value => do
    let value ← (← infer ctx value).asType .byte
    return ⟨.unit, _, .writeHandle handle offset value.property⟩
  | ctx, .borrowView view handle mode offset body => do
    let body ← infer ((view, .view .byte mode) :: ctx) body
    return ⟨body.type, body.effect, .borrowView view handle mode offset body.typed⟩
  | ctx, .readView view => some ⟨.byte, _, .readView ctx view⟩
  | ctx, .writeView view value => do
    let value ← (← infer ctx value).asType .byte
    return ⟨.unit, _, .writeView view value.property⟩
  | ctx, .lam parameter type body effect => do
    let body ← infer ((parameter, type) :: ctx) body
    if same : body.effect = effect then
      return ⟨.arrow type body.type effect, .empty, .lam parameter type effect (same ▸ body.typed)⟩
    else none
  | ctx, .app function argument => do
    let function ← infer ctx function
    match shape : function.type with
    | .arrow input output effect =>
      let argument ← (← infer ctx argument).asType input
      return ⟨output, function.effect.union (argument.val.union effect),
        .app (shape ▸ function.typed) argument.property⟩
    | _ => none
  | ctx, .loop guard body => do
    let guard ← (← infer ctx guard).asType .bool
    let body ← (← infer ctx body).asType .unit
    return ⟨.unit, _, .loop guard.property body.property⟩
  | _, .abort _ => none

theorem infer_complete {ctx : Ctx} {expression : CoreExpr} {type : CoreType} {effect : Effect}
    (typed : WellTyped ctx expression type effect) :
    infer ctx expression = some ⟨type, effect, typed⟩ := by
  induction typed <;> simp [infer, *, Inferred.asType, bind, pure]
  case var context id type found =>
    split
    · rename_i actual lookup
      have same := Option.some.inj (lookup.symm.trans found)
      subst actual
      rfl
    · simp_all

theorem infer_correct (ctx : Ctx) (expression : CoreExpr) (type : CoreType) (effect : Effect) :
    (infer ctx expression).map (fun result => (result.type, result.effect)) = some (type, effect)
      ↔ WellTyped ctx expression type effect := by
  constructor
  · intro inferred
    obtain ⟨result, _, equal⟩ := Option.map_eq_some_iff.mp inferred
    cases equal
    exact result.typed
  · intro typed
    rw [infer_complete typed]
    rfl

theorem Inferred.progress {expression : CoreExpr} (inferred : Inferred [] expression)
    (sequential : CoreSoundness.IsSequentialCore expression) (state : State) :
    Value expression ∨ ∃ nextState next, CoreSemantics.Step state expression nextState next :=
  CoreSoundness.progress expression sequential inferred.type inferred.effect inferred.typed state

theorem Inferred.preservation {expression next : CoreExpr} {state nextState : State}
    (inferred : Inferred [] expression) (step : CoreSemantics.Step state expression nextState next) :
    ∃ checked : Inferred [] next, infer [] next = some checked ∧ checked.type = inferred.type := by
  obtain ⟨effect, typed⟩ := CoreSoundness.preservation step inferred.typed
  exact ⟨⟨inferred.type, effect, typed⟩, infer_complete typed, rfl⟩

end Aethel.CoreAST
