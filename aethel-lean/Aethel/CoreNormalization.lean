import Aethel.CoreReduction

namespace Aethel.CoreAST

open Core CoreSemantics

theorem WellTyped.subst_unbound {ctx : Ctx} {expression : CoreExpr} {type : CoreType} {effect : Effect}
    (typed : WellTyped ctx expression type effect) {name : Nat} (unbound : ctx.lookup name = none)
    (replacement : CoreExpr) : subst name replacement expression = expression := by
  induction typed <;> try simp [subst, *]
  case var binding type found =>
    by_cases same : binding = name
    · rw [same, unbound] at found
      contradiction
    · simp [same]
  all_goals
    intro different
    apply_assumption
    rw [CoreSoundness.lookup_tail (Ne.symm different), unbound]

theorem WellTyped.closed_subst {expression : CoreExpr} {type : CoreType} {effect : Effect}
    (typed : WellTyped [] expression type effect) (name : Nat) (replacement : CoreExpr) :
    subst name replacement expression = expression :=
  typed.subst_unbound rfl replacement

private theorem subst_commute {first second : Nat} {left right : CoreExpr}
    (different : first ≠ second) (leftClosed : subst second right left = left)
    (rightClosed : subst first left right = right) (expression : CoreExpr) :
    subst first left (subst second right expression) = subst second right (subst first left expression) := by
  induction expression <;> try simp [subst, *]
  all_goals
    split <;> split <;> simp_all [subst]

def Computable (type : CoreType) (value : CoreExpr) : Prop :=
  Value value ∧ WellTyped [] value type .empty ∧
    match type with
    | .arrow input output _ =>
      ∀ argument, Computable input argument →
        ∃ result, Reduces {} (.app value argument) result ∧ Computable output result
    | .prod left right =>
      ∃ first second, value = .pair first second ∧ Computable left first ∧ Computable right second
    | _ => True

theorem Computable.isValue {type : CoreType} {value : CoreExpr} (good : Computable type value) :
    Value value :=
  (Computable.eq_def .. ▸ good).1

theorem Computable.typed {type : CoreType} {value : CoreExpr} (good : Computable type value) :
    WellTyped [] value type .empty :=
  (Computable.eq_def .. ▸ good).2.1

abbrev Normalizes (type : CoreType) (expression : CoreExpr) :=
  ∃ result, Reduces {} expression result ∧ Computable type result

theorem Computable.applies {input output : CoreType} {effect : Effect} {function argument : CoreExpr}
    (ready : Computable (.arrow input output effect) function) (arg : Computable input argument) :
    Normalizes output (.app function argument) :=
  (Computable.eq_def .. ▸ ready).2.2 argument arg

theorem Computable.pair {left right : CoreType} {first second : CoreExpr}
    (a : Computable left first) (b : Computable right second) :
    Computable (.prod left right) (.pair first second) :=
  ⟨.pair a.isValue b.isValue, .pair a.typed b.typed, first, second, rfl, a, b⟩

theorem Normalizes.pair {left right : CoreType} {first second : CoreExpr}
    (a : Normalizes left first) (b : Normalizes right second) :
    Normalizes (.prod left right) (.pair first second) := by
  obtain ⟨firstValue, ranFirst, computableFirst⟩ := a
  obtain ⟨secondValue, ranSecond, computableSecond⟩ := b
  have preparedFirst := ranFirst.under (.pair · second) Step.pair_left
  have preparedSecond := ranSecond.under (.pair firstValue ·) (Step.pair_right computableFirst.isValue)
  exact ⟨_, preparedFirst.append preparedSecond, computableFirst.pair computableSecond⟩

theorem Normalizes.projectPair {left right : CoreType} {expression : CoreExpr}
    (pair : Normalizes (.prod left right) expression) (first : Bool) :
    Normalizes (if first then left else right) (expression.projectPair first) := by
  obtain ⟨value, ran, ready⟩ := pair
  obtain ⟨a, b, rfl, goodA, goodB⟩ := (Computable.eq_def .. ▸ ready).2.2
  cases first
  · exact ⟨b, (ran.under .snd Step.snd_eval).append
      (.step (.snd_val goodA.isValue goodB.isValue) (.refl _)), goodB⟩
  · exact ⟨a, (ran.under .fst Step.fst_eval).append
      (.step (.fst_val goodA.isValue goodB.isValue) (.refl _)), goodA⟩

def substituteAll (bindings : List (Nat × CoreExpr)) (expression : CoreExpr) : CoreExpr :=
  bindings.foldl (fun body (name, value) => subst name value body) expression

inductive ComputableBindings : Ctx → List (Nat × CoreExpr) → Prop where
  | empty : ComputableBindings [] []
  | cons : Computable type value → ComputableBindings ctx bindings →
      ComputableBindings ((name, type) :: ctx) ((name, value) :: bindings)

theorem ComputableBindings.ids {ctx : Ctx} {bindings : List (Nat × CoreExpr)}
    (assigned : ComputableBindings ctx bindings) : bindings.map Prod.fst = ctx.map Prod.fst := by
  induction assigned with
  | empty => rfl
  | cons _ _ rest => simp [rest]

theorem substituteAll_closed {expression : CoreExpr} {type : CoreType} {effect : Effect}
    (typed : WellTyped [] expression type effect) (bindings : List (Nat × CoreExpr)) :
    substituteAll bindings expression = expression := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
    simpa only [substituteAll, List.foldl_cons, typed.closed_subst] using ih

theorem ComputableBindings.closes {ctx : Ctx} {bindings : List (Nat × CoreExpr)}
    (assigned : ComputableBindings ctx bindings) {expression : CoreExpr} {type : CoreType} {effect : Effect}
    (typed : WellTyped ctx expression type effect) :
    WellTyped [] (substituteAll bindings expression) type effect := by
  induction assigned generalizing expression with
  | empty => exact typed
  | cons value _ rest =>
    exact rest (CoreSoundness.substitution_step value.isValue value.typed expression typed)

theorem ComputableBindings.atBinding {ctx : Ctx} {bindings : List (Nat × CoreExpr)}
    (assigned : ComputableBindings ctx bindings) {binding : Nat} {type : CoreType}
    (found : ctx.lookup binding = some type) : Computable type (substituteAll bindings (.var binding)) := by
  induction assigned with
  | empty => contradiction
  | @cons actual value ctx bindings name good rest ih =>
    by_cases same : binding = name
    · subst binding
      rw [CoreSoundness.lookup_head] at found
      cases found
      change Computable _ (substituteAll bindings (subst name value (.var name)))
      simpa only [subst, ite_true, substituteAll_closed good.typed] using good
    · rw [CoreSoundness.lookup_tail same] at found
      simpa only [substituteAll, List.foldl_cons, subst, ite_eq_right same] using ih found

theorem ComputableBindings.subst_commute {ctx : Ctx} {bindings : List (Nat × CoreExpr)}
    (assigned : ComputableBindings ctx bindings) {name : Nat} {value expression : CoreExpr}
    {type : CoreType} (closed : Computable type value) (fresh : name ∉ bindings.map Prod.fst) :
    substituteAll bindings (subst name value expression) =
      subst name value (substituteAll bindings expression) := by
  induction assigned generalizing expression with
  | empty => rfl
  | @cons actual term frame bindings binding good _ rest =>
    simp only [List.map_cons, List.mem_cons, not_or] at fresh
    obtain ⟨different, remaining⟩ := fresh
    change substituteAll bindings (subst binding term (subst name value expression)) =
      subst name value (substituteAll bindings (subst binding term expression))
    rw [CoreAST.subst_commute (Ne.symm different) (good.typed.closed_subst name value)
      (closed.typed.closed_subst binding term), rest remaining]

@[simp] theorem substituteAll_app (bindings : List (Nat × CoreExpr)) (function argument : CoreExpr) :
    substituteAll bindings (.app function argument) =
      .app (substituteAll bindings function) (substituteAll bindings argument) := by
  induction bindings generalizing function argument with
  | nil => rfl
  | cons binding rest ih => exact ih _ _

@[simp] theorem substituteAll_pair (bindings : List (Nat × CoreExpr)) (first second : CoreExpr) :
    substituteAll bindings (.pair first second) =
      .pair (substituteAll bindings first) (substituteAll bindings second) := by
  induction bindings generalizing first second with
  | nil => rfl
  | cons binding rest ih => exact ih _ _

@[simp] theorem substituteAll_projection (bindings : List (Nat × CoreExpr)) (expression : CoreExpr)
    (first : Bool) : substituteAll bindings (expression.projectPair first) =
      (substituteAll bindings expression).projectPair first := by
  cases first <;> induction bindings generalizing expression with
  | nil => rfl
  | cons binding rest ih => exact ih _

@[simp] theorem substituteAll_match (bindings : List (Nat × CoreExpr)) (input : CoreExpr) (tag : Nat)
    (yes no : CoreExpr) : substituteAll bindings (.matchTag input tag yes no) =
      .matchTag (substituteAll bindings input) tag (substituteAll bindings yes) (substituteAll bindings no) := by
  induction bindings generalizing input yes no with
  | nil => rfl
  | cons binding rest ih => exact ih _ _ _

theorem substituteAll_let (bindings : List (Nat × CoreExpr)) (name : Nat)
    (value body : CoreExpr) (fresh : name ∉ bindings.map Prod.fst) :
    substituteAll bindings (.letBind name value body) =
      .letBind name (substituteAll bindings value) (substituteAll bindings body) := by
  induction bindings generalizing value body with
  | nil => rfl
  | cons binding rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at fresh
    obtain ⟨different, remaining⟩ := fresh
    simpa only [substituteAll, List.foldl_cons, subst, ite_eq_right different] using
      ih (subst binding.1 binding.2 value) (subst binding.1 binding.2 body) remaining

theorem substituteAll_lambda (bindings : List (Nat × CoreExpr)) (name : Nat) (input : CoreType)
    (body : CoreExpr) (effect : Effect) (fresh : name ∉ bindings.map Prod.fst) :
    substituteAll bindings (.lam name input body effect) = .lam name input (substituteAll bindings body) effect := by
  induction bindings generalizing body with
  | nil => rfl
  | cons binding rest ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at fresh
    obtain ⟨different, remaining⟩ := fresh
    simpa only [substituteAll, List.foldl_cons, subst, ite_eq_right different] using
      ih (subst binding.1 binding.2 body) remaining

end Aethel.CoreAST
