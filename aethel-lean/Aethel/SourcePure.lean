import Aethel.SourceVerification
import Aethel.CoreNormalization

namespace Aethel.SourceVerification

open CoreAST CoreSemantics Lean

inductive PureExpr where
  | unit (written : Bool)
  | byte (value : UInt8)
  | boolean (value : Bool)
  | name (binding : String)
  | letBind (binding : String) (value body : PureExpr)
  | lambda (parameter : String) (input : CoreType) (body : PureExpr)
  | app (callee argument : PureExpr)
  | pair (parenthesized : Bool) (first second : PureExpr)
  | projection (first : Bool) (product : PureExpr)
  | branch (condition yes no : PureExpr)
  | inject (side : Bool) (variants : CoreType × CoreType) (payload : PureExpr)
  | resultCase (input : PureExpr) (leftFirst : Bool)
      (leftName : String) (onLeft : PureExpr) (rightName : String) (onRight : PureExpr)
  | grouped (expression : PureExpr)

def typeTokens : CoreType → Tokens
  | .unit => ["(", ")"]
  | .int false 8 => ["u8"]
  | .bool => ["bool"]
  | .arrow input output _ => ["fn", "("] ++ typeTokens input ++ [")", "->"] ++ typeTokens output
  | .prod first second => ["("] ++ typeTokens first ++ [","] ++ typeTokens second ++ [")"]
  | .sum left right => ["Result", "("] ++ typeTokens left ++ [","] ++ typeTokens right ++ [")"]
  | _ => []

private def variantName (side : Bool) : String := if side then "Ok" else "Err"

def PureExpr.tokens : PureExpr → Tokens
  | .unit true => ["(", ")"]
  | .unit false => []
  | .byte value => [byteToken value]
  | .boolean true => ["true"]
  | .boolean false => ["false"]
  | .name binding => [binding]
  | .letBind binding value body =>
    ["let", binding, "="] ++ value.tokens ++ [";"] ++ body.tokens
  | .lambda parameter input body =>
    ["fn", "(", parameter, ":"] ++ typeTokens input ++ [")", "{"] ++ body.tokens ++ ["}"]
  | .app callee argument => callee.tokens ++ ["("] ++ argument.tokens ++ [")"]
  | .pair parenthesized first second =>
    let members := first.tokens ++ [","] ++ second.tokens
    if parenthesized then ["("] ++ members ++ [")"] else members
  | .projection first product => product.tokens ++ [".", if first then "0" else "1"]
  | .branch condition yes no =>
    ["if"] ++ condition.tokens ++ ["{"] ++ yes.tokens ++ ["}", "else", "{"] ++ no.tokens ++ ["}"]
  | .inject side variants payload =>
    [variantName side, "("] ++ payload.tokens ++ [")", ":"] ++ typeTokens (.sum variants.1 variants.2)
  | .resultCase input leftFirst leftName onLeft rightName onRight =>
    let left := [variantName true, "(", leftName, ")", "->"] ++ onLeft.tokens
    let right := [variantName false, "(", rightName, ")", "->"] ++ onRight.tokens
    ["case"] ++ input.tokens ++ ["{"] ++ (if leftFirst then left ++ right else right ++ left) ++ ["}"]
  | .grouped expression => ["("] ++ expression.tokens ++ [")"]

def parsePureType : Nat → Tokens → Except Error (CoreType × Tokens)
  | 0, _ => .error (.syntax "pure type")
  | fuel + 1, input => match input with
    | "(" :: ")" :: rest => .ok (.unit, rest)
    | "(" :: rest => do
      let (first, rest) ← parsePureType fuel rest
      let (second, rest) ← parsePureType fuel (← expect [","] rest)
      return (.prod first second, ← expect [")"] rest)
    | "u8" :: rest => .ok (.byte, rest)
    | "bool" :: rest => .ok (.bool, rest)
    | "Result" :: "(" :: rest => do
      let (left, rest) ← parsePureType fuel rest
      let (right, rest) ← parsePureType fuel (← expect [","] rest)
      return (.sum left right, ← expect [")"] rest)
    | "fn" :: "(" :: rest => do
      let (domain, rest) ← parsePureType fuel rest
      let (codomain, rest) ← parsePureType fuel (← expect [")", "->"] rest)
      return (.arrow domain codomain .empty, rest)
    | _ => .error (.syntax "u8, bool, unit, pair, Result, or unary function type")

mutual
  private def parsePureBlock : Nat → Tokens → Except Error (PureExpr × Tokens)
    | 0, _ => .error (.syntax "expression block")
    | fuel + 1, "let" :: rest => do
      let (name, rest) ← readName false rest
      let (value, rest) ← parsePureExpr fuel (← expect ["="] rest)
      let (body, rest) ← parsePureBlock fuel (← expect [";"] rest)
      return (.letBind name value body, rest)
    | fuel + 1, rest => parsePureExpr fuel rest

  private def parsePureExpr : Nat → Tokens → Except Error (PureExpr × Tokens)
    | 0, _ => .error (.syntax "expression")
    | fuel + 1, input => do
      let (head, rest) ← parsePureAtom fuel input
      parsePureApply fuel head rest

  private def parsePureAtom : Nat → Tokens → Except Error (PureExpr × Tokens)
    | 0, _ => .error (.syntax "expression")
    | fuel + 1, input => match input with
      | "true" :: rest => .ok (.boolean true, rest)
      | "false" :: rest => .ok (.boolean false, rest)
      | "(" :: ")" :: rest => .ok (.unit true, rest)
      | "(" :: rest => do
        let (expression, rest) ← parsePureExpr fuel rest
        match rest with
        | "," :: rest => do
          let (second, rest) ← parsePureExpr fuel rest
          return (.pair true expression second, ← expect [")"] rest)
        | _ => return (.grouped expression, ← expect [")"] rest)
      | "fn" :: "(" :: rest => do
        let (name, rest) ← readName false rest
        let (type, rest) ← parsePureType fuel (← expect [":"] rest)
        let (body, rest) ← parsePureBlock fuel (← expect [")", "{"] rest)
        return (.lambda name type body, ← expect ["}"] rest)
      | "if" :: rest => do
        let (condition, rest) ← parsePureExpr fuel rest
        let (yes, rest) ← parsePureBlock fuel (← expect ["{"] rest)
        let (no, rest) ← parsePureBlock fuel (← expect ["}", "else", "{"] rest)
        return (.branch condition yes no, ← expect ["}"] rest)
      | "Ok" :: "(" :: rest => parsePureInjection fuel true rest
      | "Err" :: "(" :: rest => parsePureInjection fuel false rest
      | "case" :: rest => do
        let (input, rest) ← parsePureExpr fuel rest
        let (leftFirst, firstName, first, rest) ← parseResultArm fuel (← expect ["{"] rest)
        let (secondSide, secondName, second, rest) ← parseResultArm fuel rest
        if leftFirst == secondSide then throw (.syntax "case requires one Ok arm and one Err arm")
        let result := if leftFirst then .resultCase input true firstName first secondName second
          else .resultCase input false secondName second firstName first
        return (result, ← expect ["}"] rest)
      | _ =>
        if let .ok (value, rest) := parseByte input then .ok (.byte value, rest)
        else do
          let (name, rest) ← readName false input
          return (.name name, rest)

  private def parsePureInjection : Nat → Bool → Tokens → Except Error (PureExpr × Tokens)
    | 0, _, _ => .error (.syntax "Result constructor")
    | fuel + 1, side, input => do
      let (payload, rest) ← parsePureExpr fuel input
      let (annotation, rest) ← parsePureType fuel (← expect [")", ":"] rest)
      let .sum left right := annotation | throw (.syntax "Result constructor type annotation")
      return (.inject side (left, right) payload, rest)

  private def parseResultArm : Nat → Tokens → Except Error (Bool × String × PureExpr × Tokens)
    | fuel + 1, tag :: "(" :: rest => do
      let side := tag == variantName true
      if !(side || tag == variantName false) then throw (.syntax "expected Ok or Err arm")
      let (binder, rest) ← readName false rest
      let (body, rest) ← parsePureBlock fuel (← expect [")", "->"] rest)
      return (side, binder, body, rest)
    | _, _ => .error (.syntax "expected Ok or Err arm")

  private def parsePureApply : Nat → PureExpr → Tokens → Except Error (PureExpr × Tokens)
    | fuel + 1, callee, "(" :: ")" :: rest =>
      parsePureApply fuel (.app callee (.unit false)) rest
    | fuel + 1, callee, "(" :: rest => do
      let (argument, rest) ← parsePureArguments fuel rest
      parsePureApply fuel (.app callee argument) (← expect [")"] rest)
    | fuel + 1, product, "." :: member :: rest =>
      if member == "0" || member == "1" then
        parsePureApply fuel (.projection (member == "0") product) rest
      else .error (.syntax "pair projection .0 or .1")
    | 0, _, "(" :: _ => .error (.syntax "call argument")
    | 0, _, "." :: _ => .error (.syntax "pair projection")
    | _, callee, rest => .ok (callee, rest)

  private def parsePureArguments : Nat → Tokens → Except Error (PureExpr × Tokens)
    | 0, _ => .error (.syntax "call argument")
    | fuel + 1, input => do
      let (first, rest) ← parsePureExpr fuel input
      match rest with
      | "," :: tail =>
        let (remaining, rest) ← parsePureArguments fuel tail
        return (.pair false first remaining, rest)
      | _ => return (first, rest)
end

structure PureParameter where
  name : String
  type : CoreType

private def PureParameter.tokens (parameter : PureParameter) : Tokens :=
  [parameter.name, ":"] ++ typeTokens parameter.type

private def argumentType : List PureParameter → CoreType
  | [] => .unit
  | [parameter] => parameter.type
  | parameter :: rest => .prod parameter.type (argumentType rest)

structure PureFunction where
  name : String
  parameters : List PureParameter
  output : CoreType
  body : PureExpr

private def argumentBinding : String := "$arguments"

/-- Argument groups are represented by right-associated products. Each tail
is bound once so extracting later parameters does not repeat projections. -/
private def bindArguments (body : PureExpr) : List PureParameter → PureExpr
  | [] => body
  | [parameter] => .letBind parameter.name (.name argumentBinding) body
  | parameter :: rest =>
    .letBind parameter.name (.projection true (.name argumentBinding))
      (.letBind argumentBinding (.projection false (.name argumentBinding)) (bindArguments body rest))

def PureFunction.value (function : PureFunction) : PureExpr :=
  match function.parameters with
  | [parameter] => .lambda parameter.name parameter.type function.body
  | parameters => .lambda argumentBinding (argumentType parameters) (bindArguments function.body parameters)

def PureFunction.signature (function : PureFunction) : CoreType :=
  .arrow (argumentType function.parameters) function.output .empty

def PureFunction.tokens (function : PureFunction) : Tokens :=
  ["fn", function.name, "("] ++ (List.intersperse [","] (function.parameters.map PureParameter.tokens)).flatten ++
    [")", "->"] ++ typeTokens function.output ++ ["{"] ++ function.body.tokens ++ ["}"]

structure PureModule where
  functions : List PureFunction
  main : PureExpr

def PureModule.tokens (source : PureModule) : Tokens :=
  source.functions.flatMap PureFunction.tokens ++ byteMainPrefix ++ source.main.tokens ++ ["}"]

def PureModule.expression (source : PureModule) : PureExpr :=
  source.functions.foldr (fun definition rest => .letBind definition.name definition.value rest) source.main

private def parsePureParameters (budget : Nat) : Nat → Tokens → Except Error (List PureParameter × Tokens)
  | _, ")" :: rest => .ok ([], rest)
  | 0, _ => .error (.syntax "function parameters")
  | fuel + 1, input => do
    let (name, rest) ← readName false input
    let (type, rest) ← parsePureType budget (← expect [":"] rest)
    let parameter : PureParameter := ⟨name, type⟩
    match rest with
    | "," :: tail =>
      let (remaining, rest) ← parsePureParameters budget fuel tail
      return (parameter :: remaining, rest)
    | _ => return ([parameter], ← expect [")"] rest)

private def parsePureFunctions (budget : Nat) : Nat → Tokens → Except Error (List PureFunction × Tokens)
  | _, "fn" :: "main" :: rest => .ok ([], "fn" :: "main" :: rest)
  | 0, _ => .error (.syntax "fn main")
  | fuel + 1, input => do
    let (name, rest) ← readName false (← expect ["fn"] input)
    let (parameters, rest) ← parsePureParameters budget budget (← expect ["("] rest)
    let (output, rest) ← parsePureType budget (← expect ["->"] rest)
    let (body, rest) ← parsePureBlock budget (← expect ["{"] rest)
    let (remaining, rest) ← parsePureFunctions budget fuel (← expect ["}"] rest)
    return (⟨name, parameters, output, body⟩ :: remaining, rest)

structure ParsedPure (input : String) where
  source : PureModule
  spelled : tokens input = source.tokens

def parsePure (input : String) : Except Error (ParsedPure input) := do
  let source := tokens input
  let budget := 3 * source.length
  let (functions, rest) ← parsePureFunctions budget source.length source
  let (main, rest) ← parsePureBlock budget (← expect byteMainPrefix rest)
  let [] ← expect ["}"] rest | throw (.syntax "end of file")
  let module : PureModule := ⟨functions, main⟩
  if spelled : source = module.tokens then return ⟨module, spelled⟩
  else throw (.syntax "canonical pure fragment")

abbrev PureScope := List (String × Nat)

inductive PureLowers : PureScope → PureExpr → CoreExpr → Prop where
  | unit : PureLowers scope (.unit written) .unit
  | byte : PureLowers scope (.byte value) (.int false 8 value.toNat)
  | boolean : PureLowers scope (.boolean value) (.bool value)
  | name {scope : PureScope} : scope.lookup binding = some slot → PureLowers scope (.name binding) (.var slot)
  | letBind : PureLowers scope value compiledValue →
      PureLowers ((binding, scope.length) :: scope) body compiledBody →
      PureLowers scope (.letBind binding value body) (.letBind scope.length compiledValue compiledBody)
  | lambda : PureLowers ((parameter, scope.length) :: scope) body compiled →
      PureLowers scope (.lambda parameter input body) (.lam scope.length input compiled .empty)
  | app : PureLowers scope callee compiledCallee → PureLowers scope argument compiledArgument →
      PureLowers scope (.app callee argument) (.app compiledCallee compiledArgument)
  | pair : PureLowers scope first compiledFirst → PureLowers scope second compiledSecond →
      PureLowers scope (.pair parenthesized first second) (.pair compiledFirst compiledSecond)
  | projection : PureLowers scope product compiled →
      PureLowers scope (.projection first product) (compiled.projectPair first)
  | branch : PureLowers scope condition compiledCondition → PureLowers scope yes compiledYes →
      PureLowers scope no compiledNo →
      PureLowers scope (.branch condition yes no) (.matchTag compiledCondition 1 compiledYes compiledNo)
  | inject : PureLowers scope payload compiled →
      PureLowers scope (.inject side variants payload) (.inject side variants compiled)
  | resultCase : PureLowers scope input compiledInput →
      PureLowers ((leftName, scope.length) :: scope) onLeft compiledLeft →
      PureLowers ((rightName, scope.length) :: scope) onRight compiledRight →
      PureLowers scope (.resultCase input leftFirst leftName onLeft rightName onRight)
        (.matchSum compiledInput scope.length compiledLeft compiledRight)
  | grouped : PureLowers scope expression compiled → PureLowers scope (.grouped expression) compiled

private def lowerPure (scope : PureScope) :
    (expression : PureExpr) → Except Error { core : CoreExpr // PureLowers scope expression core }
  | .unit _ => .ok ⟨.unit, .unit⟩
  | .byte value => .ok ⟨.int false 8 value.toNat, .byte⟩
  | .boolean value => .ok ⟨.bool value, .boolean⟩
  | .name binding =>
    match found : scope.lookup binding with
    | some id => .ok ⟨.var id, .name found⟩
    | none => throw (.unknownBinding binding)
  | .letBind binding value body => do
    let value ← lowerPure scope value
    let body ← lowerPure ((binding, scope.length) :: scope) body
    return ⟨.letBind scope.length value.val body.val, .letBind value.property body.property⟩
  | .lambda parameter input body => do
    let body ← lowerPure ((parameter, scope.length) :: scope) body
    return ⟨.lam scope.length input body.val .empty, .lambda body.property⟩
  | .app callee argument => do
    let callee ← lowerPure scope callee
    let argument ← lowerPure scope argument
    return ⟨.app callee.val argument.val, .app callee.property argument.property⟩
  | .pair _ first second => do
    let first ← lowerPure scope first
    let second ← lowerPure scope second
    return ⟨.pair first.val second.val, .pair first.property second.property⟩
  | .projection first product => do
    let product ← lowerPure scope product
    return ⟨product.val.projectPair first, .projection product.property⟩
  | .branch condition yes no => do
    let condition ← lowerPure scope condition
    let yes ← lowerPure scope yes
    let no ← lowerPure scope no
    return ⟨.matchTag condition.val 1 yes.val no.val, .branch condition.property yes.property no.property⟩
  | .inject side variants payload => do
    let payload ← lowerPure scope payload
    return ⟨.inject side variants payload.val, .inject payload.property⟩
  | .resultCase input _ leftName onLeft rightName onRight => do
    let input ← lowerPure scope input
    let left ← lowerPure ((leftName, scope.length) :: scope) onLeft
    let right ← lowerPure ((rightName, scope.length) :: scope) onRight
    return ⟨.matchSum input.val scope.length left.val right.val,
      .resultCase input.property left.property right.property⟩
  | .grouped expression => do
    let expression ← lowerPure scope expression
    return ⟨expression.val, .grouped expression.property⟩

theorem PureLowers.unique {scope : PureScope} {expression : PureExpr} {first second : CoreExpr}
    (left : PureLowers scope expression first) (right : PureLowers scope expression second) :
    first = second := by
  induction left generalizing second with
  | unit => cases right; rfl
  | byte => cases right; rfl
  | boolean => cases right; rfl
  | name found =>
    cases right with
    | name same => rw [Option.some.inj (found.symm.trans same)]
  | letBind _ _ value body =>
    cases right with
    | letBind otherValue otherBody => rw [value otherValue, body otherBody]
  | lambda _ body =>
    cases right with
    | lambda other => rw [body other]
  | app _ _ callee argument =>
    cases right with
    | app otherCallee otherArgument => rw [callee otherCallee, argument otherArgument]
  | pair _ _ first second =>
    cases right with
    | pair otherFirst otherSecond => rw [first otherFirst, second otherSecond]
  | projection _ inside =>
    cases right with
    | projection other => rw [inside other]
  | branch _ _ _ condition yes no =>
    cases right with
    | branch otherCondition otherYes otherNo => rw [condition otherCondition, yes otherYes, no otherNo]
  | inject _ payload =>
    cases right with
    | inject other => rw [payload other]
  | resultCase _ _ _ input onLeft onRight =>
    cases right with
    | resultCase otherInput otherLeft otherRight => rw [input otherInput, onLeft otherLeft, onRight otherRight]
  | grouped _ inside =>
    cases right with
    | grouped other => exact inside other

private def ScopedIds (scope : PureScope) (ctx : Ctx) : Prop :=
  ∀ id ∈ ctx.map Prod.fst, id < scope.length

private theorem ScopedIds.fresh {scope : PureScope} {ctx : Ctx} {bindings : List (Nat × CoreExpr)}
    (scopeIds : ScopedIds scope ctx) (assigned : ComputableBindings ctx bindings) :
    scope.length ∉ bindings.map Prod.fst := by
  rw [assigned.ids]
  exact fun found => Nat.lt_irrefl _ (scopeIds _ found)

private theorem ScopedIds.push {scope : PureScope} {ctx : Ctx} (scopeIds : ScopedIds scope ctx)
    (name : String) (type : CoreType) :
    ScopedIds ((name, scope.length) :: scope) ((scope.length, type) :: ctx) := by
  intro id found
  simp only [List.map_cons, List.mem_cons] at found
  rcases found with rfl | outer
  · simp
  · exact Nat.lt_succ_of_lt (scopeIds _ outer)

private theorem normalizes_after_match {source actual yes no selected : CoreExpr} {type : CoreType}
    {tag : Nat} (scrutinee : Reduces {} source actual)
    (picked : CoreSemantics.Step {} (.matchTag actual tag yes no) {} selected)
    (arm : Normalizes type selected) : Normalizes type (.matchTag source tag yes no) := by
  obtain ⟨result, runs, good⟩ := arm
  have evaluated := scrutinee.under (.matchTag · tag yes no) (CoreSemantics.Step.match_eval tag)
  exact ⟨result, evaluated.append (.step picked runs), good⟩

private theorem PureLowers.normalizes {scope : PureScope} {expression : PureExpr} {core : CoreExpr}
    (lowered : PureLowers scope expression core) {ctx : Ctx} {bindings : List (Nat × CoreExpr)}
    {type : CoreType} {effect : Effect} (typed : WellTyped ctx core type effect)
    (assigned : ComputableBindings ctx bindings) (scopeIds : ScopedIds scope ctx) :
    Normalizes type (substituteAll bindings core) := by
  induction lowered generalizing ctx bindings type effect with
  | unit =>
    cases typed
    have literal := WellTyped.unit []
    rw [substituteAll_closed literal]
    exact ⟨_, .refl _, .unit, literal, trivial⟩
  | byte =>
    rename_i value
    cases typed with
    | int _ _ _ _ fits =>
      have literal : WellTyped [] (.int false 8 value.toNat) .byte .empty := .int [] false 8 _ fits
      rw [substituteAll_closed literal]
      exact ⟨_, .refl _, .int _ _ _, literal, trivial⟩
  | boolean =>
    rename_i value
    cases typed
    have literal := WellTyped.bool [] value
    rw [substituteAll_closed literal]
    exact ⟨_, .refl _, .bool value, literal, trivial⟩
  | name _ =>
    cases typed with
    | var _ found => exact ⟨_, .refl _, assigned.atBinding found⟩
  | @letBind scope value compiledValue binding body compiledBody _ _ ihValue ihBody =>
    cases typed with
    | letBind _ typedValue typedBody =>
      obtain ⟨ready, valueRuns, valueGood⟩ := ihValue typedValue assigned scopeIds
      obtain ⟨answer, bodyRuns, good⟩ := ihBody typedBody (.cons valueGood assigned) (scopeIds.push binding _)
      have fresh := scopeIds.fresh assigned
      rw [substituteAll_let _ _ _ _ fresh]
      have prepared := valueRuns.under (.letBind scope.length · (substituteAll bindings compiledBody))
        (CoreSemantics.Step.let_eval scope.length)
      have afterLet : Reduces {} (subst scope.length ready (substituteAll bindings compiledBody)) answer :=
        assigned.subst_commute valueGood fresh ▸ bodyRuns
      exact ⟨answer, prepared.append (.step (.let_subst scope.length valueGood.isValue) afterLet), good⟩
  | @lambda parameter scope body compiled input _ ihBody =>
    have fresh := scopeIds.fresh assigned
    have closureTyped := assigned.closes typed
    cases typed with
    | lam _ _ _ typedBody =>
      rw [substituteAll_lambda _ _ _ _ _ fresh] at closureTyped ⊢
      refine ⟨_, .refl _, .lam .., closureTyped, ?_⟩
      intro argument argumentGood
      obtain ⟨result, bodyRuns, good⟩ :=
        ihBody typedBody (.cons argumentGood assigned) (scopeIds.push parameter _)
      have afterCall : Reduces {} (subst scope.length argument (substituteAll bindings compiled)) result :=
        assigned.subst_commute argumentGood fresh ▸ bodyRuns
      exact ⟨result, .step (.app_beta _ _ _ _ argumentGood.isValue) afterCall, good⟩
  | @app scope callee compiledCallee argument compiledArgument _ _ ihCallee ihArgument =>
    cases typed with
    | app typedCallee typedArgument =>
      obtain ⟨function, calleeRuns, calleeGood⟩ := ihCallee typedCallee assigned scopeIds
      obtain ⟨value, argRuns, argGood⟩ := ihArgument typedArgument assigned scopeIds
      obtain ⟨answer, callRuns, good⟩ := calleeGood.applies argGood
      rw [substituteAll_app]
      have prepareCallee := calleeRuns.under (.app · (substituteAll bindings compiledArgument))
        CoreSemantics.Step.app_fn
      have prepareArgument := argRuns.under (.app function ·) (CoreSemantics.Step.app_arg calleeGood.isValue)
      exact ⟨answer, prepareCallee.append (prepareArgument.append callRuns), good⟩
  | pair _ _ ihFirst ihSecond =>
    cases typed with
    | pair typedFirst typedSecond =>
      rw [substituteAll_pair]
      exact (ihFirst typedFirst assigned scopeIds).pair (ihSecond typedSecond assigned scopeIds)
  | @projection scope product compiled first _ ih =>
    rw [substituteAll_projection]
    cases first
    · cases typed with
      | snd typedPair => exact (ih typedPair assigned scopeIds).projectPair false
    · cases typed with
      | fst typedPair => exact (ih typedPair assigned scopeIds).projectPair true
  | branch _ _ _ ihCondition ihYes ihNo =>
    rw [substituteAll_match]
    cases typed with
    | matchBool typedCondition typedYes typedNo =>
      obtain ⟨value, conditionRuns, good⟩ := ihCondition typedCondition assigned scopeIds
      obtain ⟨flag, rfl⟩ := CoreSemantics.canonical_bool good.isValue good.typed
      cases flag
      · exact normalizes_after_match conditionRuns .match_bool_false (ihNo typedNo assigned scopeIds)
      · exact normalizes_after_match conditionRuns .match_bool_true (ihYes typedYes assigned scopeIds)
    | matchTag _ typedCondition typedYes typedNo =>
      rename_i tag _ _ _ _
      obtain ⟨value, conditionRuns, good⟩ := ihCondition typedCondition assigned scopeIds
      obtain ⟨payload, rfl, ready⟩ := CoreSemantics.canonical_adt good.isValue good.typed
      by_cases hit : tag = 1
      · subst tag
        exact normalizes_after_match conditionRuns (.match_hit 1 ready) (ihYes typedYes assigned scopeIds)
      · exact normalizes_after_match conditionRuns (.match_miss tag 1 hit ready) (ihNo typedNo assigned scopeIds)
  | inject _ ih =>
    cases typed with
    | inject _ _ payload =>
      rw [substituteAll_inject]
      exact (ih payload assigned scopeIds).inject
  | @resultCase scope input compiledInput leftName onLeft compiledLeft rightName onRight compiledRight
      _ _ _ _ ihInput ihLeft ihRight =>
    cases typed with
    | matchSum _ inputTyped leftTyped rightTyped =>
      have fresh := scopeIds.fresh assigned
      rw [substituteAll_matchSum _ _ _ _ _ fresh]
      apply (ihInput inputTyped assigned scopeIds).matchSum
      intro side payload ready
      cases side
      · exact assigned.subst_commute ready fresh ▸
          ihRight rightTyped (.cons ready assigned) (scopeIds.push rightName _)
      · exact assigned.subst_commute ready fresh ▸
          ihLeft leftTyped (.cons ready assigned) (scopeIds.push leftName _)
  | grouped _ ih => exact ih typed assigned scopeIds

inductive PureModuleTrace (result : CoreType) : PureScope → Ctx → List PureFunction → PureExpr → CoreExpr → Prop where
  | main : PureLowers scope main core → WellTyped ctx core result .empty →
      PureModuleTrace result scope ctx [] main core
  | named : definition.name ∉ scope.map Prod.fst →
      (definition.parameters.map PureParameter.name).Nodup →
      PureLowers scope definition.value function →
      WellTyped ctx function definition.signature .empty →
      PureModuleTrace result ((definition.name, scope.length) :: scope)
        ((scope.length, definition.signature) :: ctx) rest main body →
      PureModuleTrace result scope ctx (definition :: rest) main (.letBind scope.length function body)

theorem PureModuleTrace.lowers {result : CoreType} {scope : PureScope} {ctx : Ctx} {functions : List PureFunction}
    {main : PureExpr} {expression : CoreExpr} (trace : PureModuleTrace result scope ctx functions main expression) :
    PureLowers scope (PureModule.expression ⟨functions, main⟩) expression := by
  induction trace with
  | main lowered _ => exact lowered
  | named _ _ lowered _ _ ih => exact .letBind lowered ih

theorem PureModuleTrace.typed {result : CoreType} {scope : PureScope} {ctx : Ctx} {functions : List PureFunction}
    {main : PureExpr} {expression : CoreExpr} (trace : PureModuleTrace result scope ctx functions main expression) :
    WellTyped ctx expression result .empty := by
  induction trace with
  | main _ checked => exact checked
  | named _ _ _ checked _ ih => exact WellTyped.letBind _ checked ih

theorem PureModuleTrace.normalizes {result : CoreType} {functions : List PureFunction}
    {main : PureExpr} {expression : CoreExpr} (trace : PureModuleTrace result [] [] functions main expression) :
    Normalizes result expression :=
  trace.lowers.normalizes trace.typed .empty (by simp [ScopedIds])

private def checkPureExpression (scope : PureScope) (ctx : Ctx) (expression : PureExpr) (expected : CoreType) :
    Except Error { core : CoreExpr // PureLowers scope expression core ∧ WellTyped ctx core expected .empty } := do
  let ⟨core, lowers⟩ ← lowerPure scope expression
  let some checked := CoreAST.infer ctx core | throw .coreType
  if exactType : checked.type = expected ∧ checked.effect = .empty then
    return ⟨core, lowers, exactType.1 ▸ exactType.2 ▸ checked.typed⟩
  else throw .coreType

private def lowerPureModule (main : PureExpr) (result : CoreType) :
    (scope : PureScope) → (ctx : Ctx) → (functions : List PureFunction) →
      Except Error { core : CoreExpr // PureModuleTrace result scope ctx functions main core }
  | scope, ctx, [] => do
    let checked ← checkPureExpression scope ctx main result
    return ⟨checked.val, .main checked.property.1 checked.property.2⟩
  | scope, ctx, definition :: rest => do
    if fresh : definition.name ∉ scope.map Prod.fst then
      if distinct : (definition.parameters.map PureParameter.name).Nodup then
        let function ← checkPureExpression scope ctx definition.value definition.signature
        let body ← lowerPureModule main result ((definition.name, scope.length) :: scope)
          ((scope.length, definition.signature) :: ctx) rest
        return ⟨.letBind scope.length function.val body.val,
          .named fresh distinct function.property.1 function.property.2 body.property⟩
      else throw (.duplicateParameter definition.name)
    else throw (.duplicateFunction definition.name)

structure VerifiedPure (input : String) where
  parsed : ParsedPure input
  expression : CoreExpr
  trace : PureModuleTrace .byte [] [] parsed.source.functions parsed.source.main expression

theorem VerifiedPure.terminates {input : String} (verified : VerifiedPure input) :
    Normalizes .byte verified.expression :=
  verified.trace.normalizes

private def VerifiedPure.normalForm {input : String} (verified : VerifiedPure input) : CoreExpr :=
  verified.terminates.normalForm

private theorem VerifiedPure.normalForm_runs {input : String} (verified : VerifiedPure input) :
    Reduces {} verified.expression verified.normalForm ∧ Computable .byte verified.normalForm :=
  verified.terminates.normalForm_correct

def verifyPure (input : String) : Except Error (VerifiedPure input) := do
  let parsed ← parsePure input
  let ⟨expression, trace⟩ ← lowerPureModule parsed.source.main .byte [] [] parsed.source.functions
  return ⟨parsed, expression, trace⟩

structure VerifiedPureDefinition {input : String} (verified : VerifiedPure input) (name : String)
    (result : CoreType) where
  expression : CoreExpr
  trace : PureModuleTrace result [] [] verified.parsed.source.functions (.name name) expression

def VerifiedPure.definition {input : String} (verified : VerifiedPure input) (name : String) (result : CoreType) :
    Except Error (VerifiedPureDefinition verified name result) := do
  let ⟨expression, trace⟩ ← lowerPureModule (.name name) result [] [] verified.parsed.source.functions
  return ⟨expression, trace⟩

theorem VerifiedPureDefinition.terminates {input : String} {verified : VerifiedPure input} {name : String}
    {result : CoreType} (selected : VerifiedPureDefinition verified name result) :
    Normalizes result selected.expression :=
  selected.trace.normalizes

structure PureResult (expression : CoreExpr) where
  value : Int
  fits : LiteralFits false 8 value
  ran : ∀ state, Reduces state expression (.int false 8 value)

def VerifiedPure.run {input : String} (verified : VerifiedPure input) :
    Except Error (PureResult verified.expression) :=
  match finished : verified.normalForm with
  | .int false 8 value =>
    have ran : Reduces {} verified.expression (.int false 8 value) :=
      finished ▸ verified.normalForm_runs.1
    .ok ⟨value, by
      have typed : WellTyped [] (.int false 8 value) .byte .empty :=
        finished ▸ verified.normalForm_runs.2.typed
      cases typed
      assumption, ran.in_state⟩
  | _ => .error .coreStuck

theorem VerifiedPure.run_total {input : String} (verified : VerifiedPure input) :
    ∃ result, verified.run = .ok result := by
  have good := verified.normalForm_runs.2
  obtain ⟨value, isByte⟩ := CoreSemantics.canonical_int good.isValue good.typed
  unfold VerifiedPure.run
  split
  · exact ⟨_, rfl⟩
  · rename_i impossible
    exact False.elim (impossible value isByte)

deriving instance ToJson, FromJson for Effect, CoreType, CoreExpr

structure PureMIR where
  version : Nat
  expression : CoreExpr
  deriving DecidableEq, ToJson, FromJson

def VerifiedPure.mir {input : String} (verified : VerifiedPure input) : PureMIR :=
  ⟨currentSourceMIRVersion, verified.expression⟩

structure MatchingPureMIR (input text : String) where
  accepted : VerifiedPure input
  decoded : decodeCanonicalMIR text = .ok accepted.mir

def verifyPureMIR (input text : String) : Except Error (MatchingPureMIR input text) := do
  let accepted ← verifyPure input
  let matched ← matchCanonicalMIR text accepted.mir
  return ⟨accepted, matched.down⟩

theorem MatchingPureMIR.corresponds {input text : String} (matching : MatchingPureMIR input text) :
    ∃ (source : PureModule) (core : CoreExpr),
      decodeCanonicalMIR text = .ok (⟨currentSourceMIRVersion, core⟩ : PureMIR) ∧
      tokens input = source.tokens ∧ PureModuleTrace .byte [] [] source.functions source.main core ∧
      WellTyped [] core .byte .empty :=
  ⟨matching.accepted.parsed.source, matching.accepted.expression, matching.decoded,
    matching.accepted.parsed.spelled, matching.accepted.trace, matching.accepted.trace.typed⟩

end Aethel.SourceVerification
