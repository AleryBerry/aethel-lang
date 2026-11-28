import Aethel.CoreSoundnessFull

namespace Aethel.CoreAST

/-- Substitute rigid type parameters without changing effects or term binders. -/
def CoreType.specialize (resolve : String → CoreType) : CoreType → CoreType
  | .parameter name => resolve name
  | .prod left right => .prod (left.specialize resolve) (right.specialize resolve)
  | .sum left right => .sum (left.specialize resolve) (right.specialize resolve)
  | .adt tag payload => .adt tag (payload.specialize resolve)
  | .handle cell => .handle (cell.specialize resolve)
  | .view cell mode => .view (cell.specialize resolve) mode
  | .arrow input output effect => .arrow (input.specialize resolve) (output.specialize resolve) effect
  | type => type

def CoreExpr.specialize (resolve : String → CoreType) : CoreExpr → CoreExpr
  | .pair left right => .pair (left.specialize resolve) (right.specialize resolve)
  | .fst value => .fst (value.specialize resolve)
  | .snd value => .snd (value.specialize resolve)
  | .inject side (left, right) value =>
    .inject side (left.specialize resolve, right.specialize resolve) (value.specialize resolve)
  | .matchSum value binder left right =>
    .matchSum (value.specialize resolve) binder (left.specialize resolve) (right.specialize resolve)
  | .adt tag value => .adt tag (value.specialize resolve)
  | .matchTag value tag selected alternative =>
    .matchTag (value.specialize resolve) tag (selected.specialize resolve) (alternative.specialize resolve)
  | .letBind binder value body => .letBind binder (value.specialize resolve) (body.specialize resolve)
  | .writeHandle id offset value => .writeHandle id offset (value.specialize resolve)
  | .borrowView id owner mode offset body => .borrowView id owner mode offset (body.specialize resolve)
  | .writeView id value => .writeView id (value.specialize resolve)
  | .lam binder input body effect => .lam binder (input.specialize resolve) (body.specialize resolve) effect
  | .app function argument => .app (function.specialize resolve) (argument.specialize resolve)
  | .loop condition body => .loop (condition.specialize resolve) (body.specialize resolve)
  | expression => expression

def specializeCtx (resolve : String → CoreType) (ctx : Ctx) : Ctx :=
  ctx.map fun (slot, type) => (slot, type.specialize resolve)

private theorem specializeCtx_lookup (resolve : String → CoreType) (ctx : Ctx) (slot : Nat) :
    (specializeCtx resolve ctx).lookup slot = (ctx.lookup slot).map (CoreType.specialize resolve) := by
  induction ctx with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨id, type⟩ := pair
    change Ctx.lookup ((id, type.specialize resolve) :: specializeCtx resolve rest) slot =
      (Ctx.lookup ((id, type) :: rest) slot).map (CoreType.specialize resolve)
    simp only [Ctx.lookup] at ih
    by_cases same : id = slot <;> simp [Ctx.lookup, same, ih]

theorem WellTyped.specialize {ctx : Ctx} {expression : CoreExpr} {type : CoreType} {effect : Effect}
    (checked : WellTyped ctx expression type effect) (resolve : String → CoreType) :
    WellTyped (specializeCtx resolve ctx) (expression.specialize resolve) (type.specialize resolve) effect := by
  induction checked with
  | unit _ => exact .unit _
  | bool _ value => exact .bool _ value
  | nat _ value => exact .nat _ value
  | int _ signed width value fits => exact .int _ signed width value fits
  | pair _ _ left right => exact .pair left right
  | fst _ product => exact .fst product
  | snd _ product => exact .snd product
  | inject side variants _ ready =>
    cases side <;> exact .inject _ _ ready
  | matchSum binder _ _ _ input left right => exact .matchSum binder input left right
  | adt tag _ payload => exact .adt tag payload
  | matchTag tag _ _ _ input left right => exact .matchTag tag input left right
  | matchBool _ _ _ input left right => exact .matchBool input left right
  | var slot found => exact .var slot (by rw [specializeCtx_lookup, found]; rfl)
  | letBind slot _ _ binding body => exact .letBind slot binding body
  | alloc _ size init => exact .alloc _ size init
  | readHandle _ id offset => exact .readHandle _ id offset
  | writeHandle id offset _ value => exact .writeHandle id offset value
  | borrowView id owner mode offset _ body => exact .borrowView id owner mode offset body
  | readView _ id => exact .readView _ id
  | writeView id _ value => exact .writeView id value
  | lam parameter _ effect _ body => exact .lam parameter _ effect body
  | app _ _ function argument => exact .app function argument
  | loop _ _ condition body => exact .loop condition body

theorem CoreExpr.specialize_erases (resolve : String → CoreType) (expression : CoreExpr) :
    CoreSoundness.erase (expression.specialize resolve) = CoreSoundness.erase expression := by
  induction expression <;> simp [specialize, CoreSoundness.erase, *]

end Aethel.CoreAST
