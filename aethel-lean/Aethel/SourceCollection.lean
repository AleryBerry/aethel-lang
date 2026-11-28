import Aethel.SourceVerification
import Aethel.IndexedBorrow

namespace Aethel.SourceVerification

open Core Functional Structured CacheLayout Lean

deriving instance ToJson, FromJson for CollectionLayout

inductive CollectionPlace where
  | cell (root : String) (index : ByteOperand String) (field : String)
  | binding (name : String)
  deriving Repr, DecidableEq, ToJson, FromJson

inductive CollectionBlock where
  | done
  | letByte (name : String) (value : ByteOperand CollectionPlace) (next : CollectionBlock)
  | assign (place : CollectionPlace) (value : ByteOperand CollectionPlace) (next : CollectionBlock)
  | branch (left : ByteOperand String) (comparison : Comparison) (right : ByteOperand String)
      (yes no next : CollectionBlock)
  | view (mode : AccessMode) (name : String) (place : CollectionPlace) (body next : CollectionBlock)
  deriving Repr, DecidableEq, ToJson, FromJson

structure CollectionMIR where
  version : Nat
  layout : CollectionLayout
  record : String
  root : String
  fields : List String
  initial : List (List UInt8)
  body : CollectionBlock
  result : CollectionPlace
  deriving Repr, DecidableEq, ToJson, FromJson

private def identifierTokens (name : String) : Tokens := [name]

private def CollectionPlace.tokens : CollectionPlace → Tokens
  | .cell root index field => [root, "["] ++ index.tokens identifierTokens ++ ["]", ".", field]
  | .binding name => [name]

private def CollectionBlock.tokens : CollectionBlock → Tokens
  | .done => []
  | .letByte name value next =>
    ["let", name, "="] ++ value.tokens CollectionPlace.tokens ++ [";"] ++ next.tokens
  | .assign place value next =>
    place.tokens ++ ["="] ++ value.tokens CollectionPlace.tokens ++ [";"] ++ next.tokens
  | .branch left compare right yes no next =>
    ["if"] ++ left.tokens identifierTokens ++ [comparisonToken compare] ++ right.tokens identifierTokens ++
      ["{"] ++ yes.tokens ++ ["}", "else", "{"] ++ no.tokens ++ ["}", ";"] ++ next.tokens
  | .view mode name place body next =>
    ["view", modeToken mode, name, "="] ++ place.tokens ++ ["{"] ++ body.tokens ++ ["}", ";"] ++ next.tokens

private def collectionLayoutTokens : CollectionLayout → Tokens
  | .aos => ["@layout", "(", "aos", ")"]
  | .soa => ["@layout", "(", "soa", ")"]
  | .aosoa width => ["@layout", "(", "aosoa", "(", toString width, ")", ")"]

def CollectionMIR.tokens (source : CollectionMIR) : Tokens :=
  collectionLayoutTokens source.layout ++ recordDeclarationTokens source.record source.fields ++ byteMainPrefix ++
    ["let", "mut", source.root, ":", "Collection",
      "(", source.record, ")", "=", "["] ++
    source.initial.flatMap (fun row => recordLiteralTokens source.record (source.fields.zip row) ++ [","]) ++
    ["]", ";"] ++ source.body.tokens ++ source.result.tokens ++ ["}"]

private def readIndex : Tokens → Except Error (ByteOperand String × Tokens) :=
  parseOperand (readName false)

private def readCollectionPlace (input : Tokens) : Except Error (CollectionPlace × Tokens) := do
  let (name, rest) ← readName false input
  match rest with
  | "[" :: rest =>
    let (index, rest) ← readIndex rest
    let (field, rest) ← readName false (← expect ["]", "."] rest)
    return (.cell name index field, rest)
  | _ => return (.binding name, rest)

private def readCollectionLayout : Tokens → Except Error ({layout : CollectionLayout // layout.Valid} × Tokens)
  | "@layout" :: "(" :: "aos" :: ")" :: rest => .ok (⟨.aos, trivial⟩, rest)
  | "@layout" :: "(" :: "soa" :: ")" :: rest => .ok (⟨.soa, trivial⟩, rest)
  | "@layout" :: "(" :: "aosoa" :: "(" :: width :: ")" :: ")" :: rest => do
    let some number := width.toNat? | throw (.syntax "AoSoA tile width")
    if valid : 0 < number then return (⟨.aosoa number, valid⟩, rest)
    else throw (.syntax "positive AoSoA tile width")
  | _ => .error (.syntax "collection layout aos, soa, or aosoa")

private def readRows (record : String) (fields : List String) : Nat → Tokens → Except Error (List (List UInt8) × Tokens)
  | _, "]" :: rest => .ok ([], rest)
  | 0, _ => .error (.syntax "collection initializer")
  | fuel + 1, input => do
    let (row, rest) ← parseInitializers ["}", ","] fields (← expect [record, "{"] input)
    let (tail, rest) ← readRows record fields fuel rest
    return (row.map Prod.snd :: tail, rest)

private def readCollectionBlock : Nat → Tokens → Except Error (CollectionBlock × Tokens)
  | 0, _ => .error (.syntax "collection statement")
  | fuel + 1, input => match input with
    | "let" :: rest => do
      let (name, rest) ← readName false rest
      let (value, rest) ← parseOperand readCollectionPlace (← expect ["="] rest)
      let (next, rest) ← readCollectionBlock fuel (← expect [";"] rest)
      return (.letByte name value next, rest)
    | "if" :: rest => do
      let (left, rest) ← readIndex rest
      let (comparison, rest) ← parseComparison rest
      let (right, rest) ← readIndex rest
      let (yes, rest) ← readCollectionBlock fuel (← expect ["{"] rest)
      let (no, rest) ← readCollectionBlock fuel (← expect ["}", "else", "{"] rest)
      let (next, rest) ← readCollectionBlock fuel (← expect ["}", ";"] rest)
      return (.branch left comparison right yes no next, rest)
    | "view" :: rest => do
      let (mode, rest) ← parseMode rest
      let (name, rest) ← readName false rest
      let (place, rest) ← readCollectionPlace (← expect ["="] rest)
      let (body, rest) ← readCollectionBlock fuel (← expect ["{"] rest)
      let (next, rest) ← readCollectionBlock fuel (← expect ["}", ";"] rest)
      return (.view mode name place body next, rest)
    | _ => match readCollectionPlace input with
      | .ok (place, "=" :: rest) => do
        let (value, rest) ← parseOperand readCollectionPlace rest
        let (next, rest) ← readCollectionBlock fuel (← expect [";"] rest)
        return (.assign place value next, rest)
      | _ => return (.done, input)

structure ParsedCollection (input : String) where
  mir : CollectionMIR
  spelled : tokens input = mir.tokens
  layoutValid : mir.layout.Valid

def parseCollection (input : String) : Except Error (ParsedCollection input) := do
  let original := tokens input
  let fuel := original.length
  let (layout, rest) ← readCollectionLayout original
  let (record, rest) ← readName true (← expect ["type"] rest)
  let (fields, rest) ← parseDeclFields fuel (← expect ["{"] rest)
  let (root, rest) ← readName false (← expect (byteMainPrefix ++ ["let", "mut"]) rest)
  let (initial, rest) ← readRows record fields fuel (← expect [":", "Collection", "(", record, ")", "=", "["] rest)
  let (body, rest) ← readCollectionBlock fuel (← expect [";"] rest)
  let (result, rest) ← readCollectionPlace rest
  let [] ← expect ["}"] rest | throw (.syntax "end of file")
  let mir : CollectionMIR := ⟨currentSourceMIRVersion, layout.val, record, root, fields, initial, body, result⟩
  if spelled : original = mir.tokens then return ⟨mir, spelled, layout.property⟩
  else throw (.syntax "canonical collection program")

private def CollectionMIR.collection (mir : CollectionMIR) (valid : mir.layout.Valid) : ByteCollection :=
  ⟨0, mir.layout, mir.initial.length, mir.fields.length, valid⟩

private def CollectionMIR.initialByte (mir : CollectionMIR) (row field : Nat) : UInt8 :=
  (mir.initial[row]?.bind fun values => values[field]?).getD 0

private abbrev CapturedByte (ctx : List Ty) := ByteOperand (Var ctx .byte)

private def CapturedByte.term : CapturedByte ctx → Term ctx .byte
  | .literal value => .byte value
  | .place slot => .var slot

private inductive CollectionBinding (ctx : List Ty) where
  | byte (value : CapturedByte ctx)
  | view (id : ViewId)

private abbrev CollectionScope (ctx : List Ty) := List (String × CollectionBinding ctx)

private def CollectionScope.extendByte (scope : CollectionScope ctx) : CollectionScope (.byte :: ctx) :=
  scope.map fun (name, binding) => (name, match binding with
    | .byte (.literal value) => .byte (.literal value)
    | .byte (.place slot) => .byte (.place (.there slot))
    | .view id => .view id)

private def CollectionScope.retain (scope : CollectionScope ctx) (count : Nat) : CollectionScope ctx :=
  scope.drop (scope.length - count)

private def CollectionScope.index (scope : CollectionScope ctx) : ByteOperand String → Except Error (CapturedByte ctx)
  | .literal value => .ok (.literal value)
  | .place name =>
    match scope.lookup name with
    | some (.byte value) => .ok value
    | _ => .error (.unknownBinding name)

inductive CollectionIndexAt (scope : CollectionScope ctx) (env : Env ctx) : ByteOperand String → UInt8 → Prop where
  | literal : CollectionIndexAt scope env (.literal value) value
  | captured : scope.lookup name = some (.byte value) →
      CollectionIndexAt scope env (.place name) (value.term.eval env)

private theorem CollectionScope.index_sound {scope : CollectionScope ctx} {operand : ByteOperand String}
    {captured : CapturedByte ctx} (found : scope.index operand = .ok captured) (env : Env ctx) :
    CollectionIndexAt scope env operand (captured.term.eval env) := by
  cases operand with
  | literal value =>
    cases found
    exact .literal
  | place name =>
    cases lookedUp : scope.lookup name with
    | none => simp [index, lookedUp] at found
    | some binding =>
      cases binding with
      | view id => simp [index, lookedUp] at found
      | byte value =>
        have same : value = captured := by simpa [index, lookedUp] using found
        exact same ▸ .captured lookedUp

inductive CollectionPlaceAt (mir : CollectionMIR) (valid : mir.layout.Valid)
    (scope : CollectionScope ctx) (env : Env ctx) : CollectionPlace → AccessTarget → Prop where
  | view {id : ViewId} : scope.lookup name = some (.view id) →
      CollectionPlaceAt mir valid scope env (.binding name) (.view id)
  | cell {column : Fin mir.fields.length} {value : UInt8} :
      root = mir.root → mir.fields[column.val] = name → CollectionIndexAt scope env index value →
      value.toNat < mir.initial.length →
      CollectionPlaceAt mir valid scope env (.cell root index name)
        (.handle ((mir.collection valid).cellOffset value.toNat column))

private def CollectionPlace.lower (mir : CollectionMIR) (valid : mir.layout.Valid) (scope : CollectionScope ctx)
    (place : CollectionPlace) (action : AccessTarget → Code ctx) : Except Error (Code ctx) := do
  match place with
  | .binding name =>
    let some (.view id) := scope.lookup name | throw (.unknownView name)
    return action (.view id)
  | .cell root index field =>
    if root ≠ mir.root then throw (.unknownBinding root)
    let value ← scope.index index
    let some column := mir.fields.finIdxOf? field | throw (.unknownField root field)
    return (mir.collection valid).dispatch value.term column fun handle => action (.handle handle)

theorem CollectionPlace.lower_executes {mir : CollectionMIR} {valid : mir.layout.Valid}
    {scope : CollectionScope ctx} {place : CollectionPlace} {action : AccessTarget → Code ctx}
    {code : Code ctx} {env : Env ctx} {state final : State} {steps : Program}
    (lowered : place.lower mir valid scope action = .ok code)
    (ran : Structured.Executes env state code steps final) :
    ∃ target, CollectionPlaceAt mir valid scope env place target ∧
      Structured.Executes env state (action target) steps final := by
  cases place with
  | binding name =>
    cases found : scope.lookup name with
    | none => simp [lower, found] at lowered
    | some binding =>
      cases binding with
      | byte value => simp [lower, found] at lowered
      | view id =>
        have same : action (.view id) = code := by simpa [lower, found, pure, Except.pure] using lowered
        exact ⟨.view id, .view found, same.symm ▸ ran⟩
  | cell root index field =>
    by_cases owns : root = mir.root
    · cases captured : scope.index index with
      | error err => simp [lower, owns, captured, bind, Except.bind] at lowered
      | ok value =>
        cases named : mir.fields.finIdxOf? field with
        | none => simp [lower, owns, captured, named, bind, Except.bind] at lowered
        | some column =>
          have same : (mir.collection valid).dispatch value.term column
              (fun handle => action (.handle handle)) = code := by
            simp only [lower, owns, captured, named, ne_eq, not_true_eq_false, ↓reduceIte, bind, Except.bind,
              pure, Except.pure, Except.ok.injEq] at lowered
            exact lowered
          rw [← same] at ran
          obtain ⟨within, selected⟩ := ((mir.collection valid).dispatch_correct value.term column _).mp ran
          exact ⟨_, .cell owns (List.finIdxOf?_eq_some_iff.mp named).1 (scope.index_sound captured env) within,
            selected⟩
    · simp [lower, owns, bind, Except.bind] at lowered

private abbrev ByteContinuation :=
  (ctx : List Ty) → CollectionScope ctx → CapturedByte ctx → Except Error (Code ctx)

private def lowerCollectionLoad (mir : CollectionMIR) (valid : mir.layout.Valid)
    (scope : CollectionScope ctx) (place : CollectionPlace) (next : ByteContinuation) :
    Except Error (Code ctx) := do
  let tail ← next (.byte :: ctx) scope.extendByte (.place .here)
  place.lower mir valid scope fun target => .read target tail

private def lowerCollectionValue (mir : CollectionMIR) (valid : mir.layout.Valid)
    (scope : CollectionScope ctx) (value : ByteOperand CollectionPlace) (next : ByteContinuation) :
    Except Error (Code ctx) :=
  match value with
  | .literal byte => next ctx scope (.literal byte)
  | .place (.binding name) =>
    match scope.lookup name with
    | some (.byte captured) => next ctx scope captured
    | some (.view _) => lowerCollectionLoad mir valid scope (.binding name) next
    | none => .error (.unknownBinding name)
  | .place place => lowerCollectionLoad mir valid scope place next

inductive CollectionValueReads (mir : CollectionMIR) (valid : mir.layout.Valid) :
    {ctx : List Ty} → CollectionScope ctx → Env ctx → State → ByteOperand CollectionPlace →
      {inner : List Ty} → CollectionScope inner → Env inner → CapturedByte inner → Program → State → Prop where
  | literal :
      CollectionValueReads mir valid scope env state (.literal value) scope env (.literal value) [] state
  | captured : scope.lookup name = some (.byte value) →
      CollectionValueReads mir valid scope env state (.place (.binding name)) scope env value [] state
  | load {target : AccessTarget} {value : UInt8} :
      CollectionPlaceAt mir valid scope env place target →
      Step state target.readInstruction observed → observed = state.observe value →
      CollectionValueReads mir valid scope env state (.place place) scope.extendByte (env.extend value)
        (.place .here) [target.readInstruction] observed

private def CollectionValueContinues (mir : CollectionMIR) (valid : mir.layout.Valid)
    (scope : CollectionScope ctx) (env : Env ctx) (state : State) (value : ByteOperand CollectionPlace)
    (next : ByteContinuation) (steps : Program) (final : State) : Prop :=
  ∃ (inner : List Ty) (locals : CollectionScope inner) (environment : Env inner) (captured : CapturedByte inner)
    (beforeTail : State) (readSteps tailSteps : Program) (tail : Code inner),
    CollectionValueReads mir valid scope env state value locals environment captured readSteps beforeTail ∧
      steps = readSteps ++ tailSteps ∧ next inner locals captured = .ok tail ∧
      Structured.Executes environment beforeTail tail tailSteps final

private theorem lowerCollectionLoad_executes {mir : CollectionMIR} {valid : mir.layout.Valid}
    {scope : CollectionScope ctx} {place : CollectionPlace} {next : ByteContinuation}
    {code : Code ctx} {env : Env ctx} {state final : State} {steps : Program}
    (lowered : lowerCollectionLoad mir valid scope place next = .ok code)
    (ran : Structured.Executes env state code steps final) :
    CollectionValueContinues mir valid scope env state (.place place) next steps final := by
  cases continued : next (.byte :: ctx) scope.extendByte (.place .here) with
  | error err => simp [lowerCollectionLoad, continued, bind, Except.bind] at lowered
  | ok tail =>
    simp only [lowerCollectionLoad, continued, bind, Except.bind] at lowered
    obtain ⟨target, resolved, loaded⟩ := CollectionPlace.lower_executes lowered ran
    cases loaded with
    | read step stored remaining =>
      exact ⟨_, _, _, _, _, _, _, tail, .load resolved step stored, rfl, continued, remaining⟩

theorem lowerCollectionValue_executes {mir : CollectionMIR} {valid : mir.layout.Valid}
    {scope : CollectionScope ctx} {value : ByteOperand CollectionPlace} {next : ByteContinuation}
    {code : Code ctx} {env : Env ctx} {state final : State} {steps : Program}
    (lowered : lowerCollectionValue mir valid scope value next = .ok code)
    (ran : Structured.Executes env state code steps final) :
    CollectionValueContinues mir valid scope env state value next steps final := by
  cases value with
  | literal byte => exact ⟨ctx, scope, env, .literal byte, state, [], steps, code, .literal, rfl, lowered, ran⟩
  | place place =>
    cases place with
    | cell root index field => exact lowerCollectionLoad_executes lowered ran
    | binding name =>
      cases found : scope.lookup name with
      | none => simp [lowerCollectionValue, found] at lowered
      | some binding =>
        cases binding with
        | view id => exact lowerCollectionLoad_executes (by simpa [lowerCollectionValue, found] using lowered) ran
        | byte value =>
          exact ⟨ctx, scope, env, value, state, [], steps, code, .captured found, rfl,
            by simpa [lowerCollectionValue, found] using lowered, ran⟩

private def lowerCollectionBranch (comparison : Comparison) (left right : CapturedByte ctx)
    (yes no : Code ctx) : Code ctx :=
  match left, right with
  | .literal a, .literal b => if comparison.test a b then yes else no
  | a, b =>
    match comparison with
    | .unequal => .branch (.byteEq a.term b.term) no yes
    | _ => .branch (comparison.term a.term b.term) yes no

private theorem comparisonEvaluates (comparison : Comparison) (left right : Term ctx .byte) (env : Env ctx) :
    (comparison.term left right).eval env = comparison.test (left.eval env) (right.eval env) := by
  cases comparison <;> rfl

private theorem lowerCollectionBranch_executes {comparison : Comparison} {left right : CapturedByte ctx}
    {yes no : Code ctx} {env : Env ctx} {state final : State} {steps : Program}
    (ran : Structured.Executes env state (lowerCollectionBranch comparison left right yes no) steps final) :
    Structured.Executes env state
      (if comparison.test (left.term.eval env) (right.term.eval env) then yes else no) steps final := by
  unfold lowerCollectionBranch at ran
  split at ran
  · split at ran <;> simp_all [CapturedByte.term, Term.eval]
  · split at ran
    · have chosen := ran.branch_selected
      rw [← comparisonEvaluates]
      cases observed : (Term.byteEq left.term right.term).eval env <;>
        simpa [Comparison.term, Term.eval, show (left.term.eval env == right.term.eval env) = _ from observed]
          using chosen
    · simpa only [comparisonEvaluates] using ran.branch_selected

private abbrev CollectionContinuation := (ctx : List Ty) → CollectionScope ctx → Except Error (Code ctx)

private def lowerCollectionBlock (mir : CollectionMIR) (valid : mir.layout.Valid) :
    CollectionBlock → (ctx : List Ty) → CollectionScope ctx → Nat → CollectionContinuation →
      Except Error (Code ctx)
  | .done, ctx, scope, _, tail => tail ctx scope
  | .letByte name value next, _, scope, depth, tail =>
    lowerCollectionValue mir valid scope value fun inner bound captured =>
      lowerCollectionBlock mir valid next inner ((name, .byte captured) :: bound) depth tail
  | .assign place value next, _, scope, depth, tail =>
    lowerCollectionValue mir valid scope value fun inner bound captured => do
      let lowered ← lowerCollectionBlock mir valid next inner bound depth tail
      place.lower mir valid bound fun target =>
        .write target captured.term lowered
  | .branch left comparison right yes no next, ctx, scope, depth, tail => do
    let a ← scope.index left
    let b ← scope.index right
    let continuation := fun (inner : List Ty) (locals : CollectionScope inner) =>
      lowerCollectionBlock mir valid next inner (locals.retain scope.length) depth tail
    let onTrue ← lowerCollectionBlock mir valid yes ctx scope depth continuation
    let onFalse ← lowerCollectionBlock mir valid no ctx scope depth continuation
    return lowerCollectionBranch comparison a b onTrue onFalse
  | .view mode name place body next, ctx, scope, depth, tail => do
    let .cell .. := place | throw (.syntax "collection view of an indexed field")
    let inside ← lowerCollectionBlock mir valid body ctx ((name, .view depth) :: scope) (depth + 1)
      fun inner locals => do
        let continuation ← lowerCollectionBlock mir valid next inner
          (locals.retain scope.length) depth tail
        return .instruction (.release depth) continuation
    place.lower mir valid scope fun target =>
      match target with
      | .handle id => .instruction (.reserve depth id mode) inside
      | .view _ => .unreachable
termination_by block _ _ _ _ => sizeOf block
decreasing_by all_goals simp_wf <;> omega

inductive CollectionBlockExecutes (mir : CollectionMIR) (valid : mir.layout.Valid) :
    {ctx : List Ty} → CollectionScope ctx → Env ctx → State → Nat → CollectionBlock →
      {inner : List Ty} → CollectionScope inner → Env inner → Program → State → Prop where
  | done : CollectionBlockExecutes mir valid scope env state depth .done scope env [] state
  | letByte :
      CollectionValueReads mir valid scope env state value locals inner captured readSteps middle →
      CollectionBlockExecutes mir valid ((name, .byte captured) :: locals) inner middle depth next
        afterScope afterEnv nextSteps final →
      CollectionBlockExecutes mir valid scope env state depth (.letByte name value next)
        afterScope afterEnv (readSteps ++ nextSteps) final
  | assign {target : AccessTarget} :
      CollectionValueReads mir valid scope env state value locals inner captured readSteps middle →
      CollectionPlaceAt mir valid locals inner place target →
      Step middle (target.writeInstruction (captured.term.eval inner)) written →
      CollectionBlockExecutes mir valid locals inner written depth next afterScope afterEnv nextSteps final →
      CollectionBlockExecutes mir valid scope env state depth (.assign place value next)
        afterScope afterEnv (readSteps ++ target.writeInstruction (captured.term.eval inner) :: nextSteps) final
  | branch :
      CollectionIndexAt scope env left leftValue → CollectionIndexAt scope env right rightValue →
      CollectionBlockExecutes mir valid scope env state depth
        (if comparison.test leftValue rightValue then yes else no) locals inner branchSteps joined →
      CollectionBlockExecutes mir valid (locals.retain scope.length) inner joined depth next
        afterScope afterEnv nextSteps final →
      CollectionBlockExecutes mir valid scope env state depth (.branch left comparison right yes no next)
        afterScope afterEnv (branchSteps ++ nextSteps) final
  | view {handle : HandleId} :
      CollectionPlaceAt mir valid scope env place (.handle handle) →
      Step state (.reserve depth handle mode) opened →
      CollectionBlockExecutes mir valid ((name, .view depth) :: scope) env opened (depth + 1) body
        locals inner bodySteps leaving →
      Step leaving (.release depth) released →
      CollectionBlockExecutes mir valid (locals.retain scope.length) inner released depth next
        afterScope afterEnv nextSteps final →
      CollectionBlockExecutes mir valid scope env state depth (.view mode name place body next)
        afterScope afterEnv (.reserve depth handle mode :: bodySteps ++ .release depth :: nextSteps) final

private def CollectionBlockContinues (mir : CollectionMIR) (valid : mir.layout.Valid)
    (scope : CollectionScope ctx) (env : Env ctx) (state : State) (depth : Nat) (block : CollectionBlock)
    (continuation : CollectionContinuation) (steps : Program) (final : State) : Prop :=
  ∃ (inner : List Ty) (locals : CollectionScope inner) (environment : Env inner)
    (beforeTail : State) (bodySteps tailSteps : Program) (tail : Code inner),
    CollectionBlockExecutes mir valid scope env state depth block locals environment bodySteps beforeTail ∧
      steps = bodySteps ++ tailSteps ∧ continuation inner locals = .ok tail ∧
      Structured.Executes environment beforeTail tail tailSteps final

theorem lowerCollectionBlock_executes (mir : CollectionMIR) (valid : mir.layout.Valid) (block : CollectionBlock) :
    ∀ {ctx : List Ty} {scope : CollectionScope ctx} {depth : Nat} {continuation : CollectionContinuation}
      {code : Code ctx} {env : Env ctx} {state final : State} {steps : Program},
    lowerCollectionBlock mir valid block ctx scope depth continuation = .ok code →
    Structured.Executes env state code steps final →
    CollectionBlockContinues mir valid scope env state depth block continuation steps final := by
  induction block <;> intro ctx scope depth continuation code env state final steps lowered ran
  case done =>
    rw [lowerCollectionBlock] at lowered
    exact ⟨ctx, scope, env, state, [], steps, code, .done, rfl, lowered, ran⟩
  case letByte name value next ih =>
    rw [lowerCollectionBlock] at lowered
    obtain ⟨_, _, _, _, _, reads, _, _, observed, rfl, compiled, executed⟩ :=
      lowerCollectionValue_executes lowered ran
    obtain ⟨inner, locals, environment, middle, nextSteps, tailSteps, tail, nextRan, rfl, tailCode, tailRan⟩ :=
      ih compiled executed
    exact ⟨inner, locals, environment, middle, reads ++ nextSteps, tailSteps, tail,
      .letByte observed nextRan, (List.append_assoc ..).symm, tailCode, tailRan⟩
  case assign place value next ih =>
    rw [lowerCollectionBlock] at lowered
    obtain ⟨inner, locals, environment, captured, _, reads, _, _, observed, rfl, compiled, executed⟩ :=
      lowerCollectionValue_executes lowered ran
    cases nextCode : lowerCollectionBlock mir valid next inner locals depth continuation with
    | error err => simp [nextCode, bind, Except.bind] at compiled
    | ok body =>
      simp only [nextCode, bind, Except.bind] at compiled
      obtain ⟨target, resolved, accessed⟩ := CollectionPlace.lower_executes compiled executed
      cases accessed with
      | write evaluated stepped rest =>
        rw [← evaluated.agrees] at stepped
        obtain ⟨afterCtx, afterScope, afterEnv, last, nextSteps, tailSteps, tail, nextRan, rfl, tailCode, tailRan⟩ :=
          ih nextCode rest
        exact ⟨afterCtx, afterScope, afterEnv, last, reads ++ _ :: nextSteps, tailSteps, tail,
          .assign observed resolved stepped nextRan, by simp [evaluated.agrees, List.append_assoc], tailCode, tailRan⟩
  case branch left comparison right yes no next ihYes ihNo ihNext =>
    let rest : CollectionContinuation := fun inner locals =>
      lowerCollectionBlock mir valid next inner (locals.retain scope.length) depth continuation
    rw [lowerCollectionBlock] at lowered
    change (do
      let a ← scope.index left
      let b ← scope.index right
      let onTrue ← lowerCollectionBlock mir valid yes ctx scope depth rest
      let onFalse ← lowerCollectionBlock mir valid no ctx scope depth rest
      return lowerCollectionBranch comparison a b onTrue onFalse) = .ok code at lowered
    cases leftCode : scope.index left with
    | error err => simp [leftCode, bind, Except.bind] at lowered
    | ok a =>
      cases rightCode : scope.index right with
      | error err => simp [leftCode, rightCode, bind, Except.bind] at lowered
      | ok b =>
        cases yesCode : lowerCollectionBlock mir valid yes ctx scope depth rest with
        | error err => simp [leftCode, rightCode, yesCode, bind, Except.bind] at lowered
        | ok trueArm =>
          cases noCode : lowerCollectionBlock mir valid no ctx scope depth rest with
          | error err =>
            simp [leftCode, rightCode, yesCode, noCode, bind, Except.bind] at lowered
          | ok falseArm =>
            have same : lowerCollectionBranch comparison a b trueArm falseArm = code := by
              simpa [leftCode, rightCode, yesCode, noCode, bind, Except.bind,
                pure, Except.pure] using lowered
            have chosen := lowerCollectionBranch_executes (same.symm ▸ ran)
            have branchRan : CollectionBlockContinues mir valid scope env state depth
                (if comparison.test (a.term.eval env) (b.term.eval env) then yes else no) rest steps final := by
              cases outcome : comparison.test (a.term.eval env) (b.term.eval env)
              · exact ihNo noCode (by simpa only [outcome, Bool.false_eq_true, ite_false] using chosen)
              · exact ihYes yesCode (by simpa only [outcome, ite_true] using chosen)
            obtain ⟨_, _, _, _, branchSteps, _, _, selected, rfl, nextCode, nextExec⟩ := branchRan
            obtain ⟨inner, locals, environment, middle, nextSteps, tailSteps, tail, nextRan, rfl, tailCode, tailRan⟩ :=
              ihNext nextCode nextExec
            exact ⟨inner, locals, environment, middle, branchSteps ++ nextSteps, tailSteps, tail,
              .branch (scope.index_sound leftCode env) (scope.index_sound rightCode env) selected nextRan,
              (List.append_assoc ..).symm, tailCode, tailRan⟩
  case view mode name place body next ihBody ihNext =>
    cases place with
    | binding bound => simp [lowerCollectionBlock] at lowered
    | cell root index field =>
      let close : CollectionContinuation := fun inner locals => do
        let tail ← lowerCollectionBlock mir valid next inner (locals.retain scope.length) depth continuation
        return .instruction (.release depth) tail
      let place := CollectionPlace.cell root index field
      rw [lowerCollectionBlock] at lowered
      change (do
        let inside ← lowerCollectionBlock mir valid body ctx ((name, .view depth) :: scope) (depth + 1) close
        place.lower mir valid scope fun target =>
          match target with
          | .handle handle => .instruction (.reserve depth handle mode) inside
          | .view _ => .unreachable) = .ok code at lowered
      cases bodyCode : lowerCollectionBlock mir valid body ctx ((name, .view depth) :: scope) (depth + 1) close with
      | error err =>
        simp [bodyCode, bind, Except.bind] at lowered
      | ok inside =>
        simp only [bodyCode, bind, Except.bind] at lowered
        obtain ⟨target, resolved, opened⟩ := CollectionPlace.lower_executes lowered ran
        cases target with
        | view loan => cases opened
        | handle handle =>
          cases opened with
          | instruction entered bodyRun =>
            obtain ⟨inner, locals, environment, _, bodySteps, _, releaseTail, insideRan, rfl, tailCode, tailRun⟩ :=
              ihBody bodyCode bodyRun
            cases afterCode : lowerCollectionBlock mir valid next inner (locals.retain scope.length) depth continuation with
            | error err => simp [close, afterCode, bind, Except.bind] at tailCode
            | ok continuationCode =>
              have same : (.instruction (.release depth) continuationCode : Code inner) = releaseTail := by
                simp only [close, afterCode, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at tailCode
                exact tailCode
              rw [← same] at tailRun
              cases tailRun with
              | instruction released nextExecution =>
                obtain ⟨afterCtx, afterScope, afterEnv, middle, nextSteps, tailSteps, tail, nextRan, rfl, tailCode, tailRan⟩ :=
                  ihNext afterCode nextExecution
                refine ⟨afterCtx, afterScope, afterEnv, middle, .reserve depth handle mode :: bodySteps ++
                  .release depth :: nextSteps, tailSteps, tail, .view resolved entered insideRan released nextRan,
                  ?_, tailCode, tailRan⟩
                simp [List.append_assoc]

private def CollectionMIR.lowerResult (mir : CollectionMIR) (valid : mir.layout.Valid) : CollectionContinuation :=
  fun _ scope => mir.result.lower mir valid scope fun target =>
    .read target (.instruction (.destroy 0) .finish)

private def CollectionMIR.lowerBody (mir : CollectionMIR) (valid : mir.layout.Valid) :
    Except Error (Code []) :=
  lowerCollectionBlock mir valid mir.body [] [] 0 (mir.lowerResult valid)

private def CollectionMIR.lower (mir : CollectionMIR) (valid : mir.layout.Valid) :
    Except Error (Code []) := do
  let body ← mir.lowerBody valid
  let entry := (mir.collection valid).entry mir.initialByte
  return Code.prepend entry body

structure VerifiedCollection (input : String) where
  parsed : ParsedCollection input
  lowered : Code []
  derivesCode : parsed.mir.lower parsed.layoutValid = .ok lowered
  checked : Structured.check {} lowered = true

def verifyCollection (input : String) : Except Error (VerifiedCollection input) := do
  let parsed ← parseCollection input
  if !decide parsed.mir.fields.Nodup then throw (.syntax "duplicate collection field")
  match lowered : parsed.mir.lower parsed.layoutValid with
  | .error error => throw error
  | .ok code =>
    if checked : Structured.check {} code = true then
      return ⟨parsed, code, lowered, checked⟩
    else throw .resourceConflict

def VerifiedCollection.run {input : String} (verified : VerifiedCollection input) : Option UInt8 := do
  let (_, final) ← Structured.runCode Env.empty {} verified.lowered
  final.observations.head?

private theorem VerifiedCollection.executed_body {input : String} (verified : VerifiedCollection input)
    {steps : Program} {final : State} (ran : Structured.Executes Env.empty {} verified.lowered steps final) :
    let mir := verified.parsed.mir
    let valid := verified.parsed.layoutValid
    let entry := (mir.collection valid).entry mir.initialByte
    ∃ state remaining body, steps = entry ++ remaining ∧ Runs {} entry state ∧
      mir.lowerBody valid = .ok body ∧ Structured.Executes Env.empty state body remaining final := by
  have derived := verified.derivesCode
  unfold CollectionMIR.lower at derived
  cases loweredBody : verified.parsed.mir.lowerBody verified.parsed.layoutValid with
  | error error => simp [loweredBody, bind, Except.bind] at derived
  | ok body =>
    simp only [loweredBody, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at derived
    rw [← derived] at ran
    obtain ⟨state, remaining, used, entered, executed⟩ := ran.prepend_split _
    exact ⟨state, remaining, body, used, entered, loweredBody, executed⟩

theorem VerifiedCollection.initial_memory {input : String} (verified : VerifiedCollection input)
    {steps : Program} {final : State} (ran : Structured.Executes Env.empty {} verified.lowered steps final) :
    let mir := verified.parsed.mir
    let collection := mir.collection verified.parsed.layoutValid
    let entry := collection.entry mir.initialByte
    ∃ state remaining, steps = entry ++ remaining ∧ Runs {} entry state ∧
      ByteCollectionRep state collection.owner collection.layout collection.length collection.fields mir.initialByte ∧
      ∀ row, row < collection.length → ∀ field : Fin collection.fields,
        state.handle (collection.cellOffset row field) =
          some ⟨⟨collection.owner, collection.cellOffset row field⟩, .exclusive⟩ := by
  obtain ⟨state, remaining, _, used, entered, _, _⟩ := verified.executed_body ran
  obtain ⟨representation, _, handles⟩ :=
    (verified.parsed.mir.collection verified.parsed.layoutValid).entry_correct (run_complete entered)
  exact ⟨state, remaining, used, entered, representation, handles⟩

/-- The collection's source trace includes its chosen layout, every source
statement, the final selected field read, and ownership teardown. -/
def CollectionExecutes (mir : CollectionMIR) (valid : mir.layout.Valid)
    (steps : Program) (final : State) (result : UInt8) : Prop :=
  let collection := mir.collection valid
  let entry := collection.entry mir.initialByte
  ∃ (entered beforeResult afterRead : State) (ctx : List Ty) (scope : CollectionScope ctx) (env : Env ctx)
      (target : AccessTarget) (bodySteps : Program),
    Runs {} entry entered ∧
      ByteCollectionRep entered collection.owner collection.layout collection.length collection.fields mir.initialByte ∧
      CollectionBlockExecutes mir valid [] Env.empty entered 0 mir.body scope env bodySteps beforeResult ∧
      CollectionPlaceAt mir valid scope env mir.result target ∧
      Step beforeResult target.readInstruction afterRead ∧ afterRead = beforeResult.observe result ∧
      Step afterRead (.destroy collection.owner) final ∧ steps = entry ++ bodySteps ++
        [target.readInstruction, .destroy collection.owner]

theorem VerifiedCollection.source_execution {input : String} (verified : VerifiedCollection input)
    {steps : Program} {final : State} (ran : Structured.Executes Env.empty {} verified.lowered steps final) :
    ∃ result, CollectionExecutes verified.parsed.mir verified.parsed.layoutValid steps final result ∧
      verified.run = some result := by
  let mir := verified.parsed.mir
  let valid := verified.parsed.layoutValid
  let collection := mir.collection valid
  obtain ⟨entered, _, body, used, initial, lowered, executed⟩ := verified.executed_body ran
  have represented := (collection.entry_correct (run_complete initial)).1
  obtain ⟨ctx, scope, env, beforeResult, bodySteps, _, _, bodyRan, finished, tailCode, tailRan⟩ :=
    lowerCollectionBlock_executes mir valid mir.body lowered executed
  obtain ⟨target, resolved, output⟩ := CollectionPlace.lower_executes tailCode tailRan
  cases output with
  | read readStep observed rest =>
    cases rest with
    | instruction destroyed done =>
      cases done
      refine ⟨_, ⟨entered, beforeResult, _, ctx, scope, env, target, bodySteps, initial,
        represented, bodyRan, resolved, readStep, observed, destroyed, ?_⟩, ?_⟩
      · rw [used, finished, List.append_assoc]
        rfl
      · cases destroyed
        simp [VerifiedCollection.run, ran.agrees, bind, State.removeOwner, observed, State.observe]

theorem VerifiedCollection.execute_correct {input : String} (verified : VerifiedCollection input) :
    ∃ steps final value, Structured.Executes Env.empty {} verified.lowered steps final ∧
      CollectionExecutes verified.parsed.mir verified.parsed.layoutValid steps final value ∧
      final.views = [] ∧ verified.run = some value := by
  obtain ⟨steps, final, ran, closed⟩ := Structured.check_executes _ Env.empty {} verified.checked
  obtain ⟨value, program, observed⟩ := verified.source_execution ran
  exact ⟨steps, final, value, ran, program, closed, observed⟩

theorem VerifiedCollection.prefix_safe {input : String} (verified : VerifiedCollection input)
    {first rest : Program} {final : State}
    (ran : Structured.Executes Env.empty {} verified.lowered (first ++ rest) final) :
    ∃ middle, Runs {} first middle ∧ Runs middle rest final ∧ final.views = [] ∧
      middle.OwnersValid ∧ middle.ReferencesLive ∧ middle.ViewsCompatible :=
  Structured.checked_prefix_safe verified.checked ran

structure MatchingCollectionMIR (input text : String) where
  accepted : VerifiedCollection input
  decoded : decodeCanonicalMIR text = .ok accepted.parsed.mir

def verifyCollectionMIR (input text : String) : Except Error (MatchingCollectionMIR input text) := do
  let accepted ← verifyCollection input
  let matched ← matchCanonicalMIR text accepted.parsed.mir
  return ⟨accepted, matched.down⟩

theorem MatchingCollectionMIR.corresponds {input text : String} (matching : MatchingCollectionMIR input text) :
    decodeCanonicalMIR text = .ok matching.accepted.parsed.mir ∧
      tokens input = matching.accepted.parsed.mir.tokens ∧
        ∃ steps final value, CollectionExecutes matching.accepted.parsed.mir
          matching.accepted.parsed.layoutValid steps final value ∧ final.views = [] ∧
          matching.accepted.run = some value := by
  obtain ⟨steps, final, value, _, trace, closed, observed⟩ := matching.accepted.execute_correct
  exact ⟨matching.decoded, matching.accepted.parsed.spelled, steps, final, value, trace, closed, observed⟩

end Aethel.SourceVerification
