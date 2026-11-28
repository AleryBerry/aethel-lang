import Aethel.SourceRust

namespace Aethel.SourceVerification

open Core Lean RustFFI

structure RustSymbol where
  package : String
  symbol : String
  deriving Repr, DecidableEq, ToJson, FromJson

structure RustParameter where
  name : String
  mode : AccessMode
  deriving Repr, DecidableEq, ToJson, FromJson

structure RustImport where
  name : String
  target : RustSymbol
  parameters : List RustParameter
  deriving Repr, DecidableEq, ToJson, FromJson

structure RustCall where
  name : String
  arguments : List FieldPath

private def RustParameter.tokens (parameter : RustParameter) : Tokens :=
  [parameter.name, ":", "["] ++ (if parameter.mode = .exclusive then ["mut"] else []) ++ ["u8", "]"]

private def RustImport.tokens (decl : RustImport) : Tokens :=
  ["@external", "(", "rust", ",", "\"" ++ decl.target.package ++ "\"", ",",
    "\"" ++ decl.target.symbol ++ "\"", ")", "pub", "fn", decl.name, "("] ++
    ((decl.parameters.map RustParameter.tokens).intersperse [","]).flatten ++ [")", "->", "(", ")"]

private def RustCall.tokens (call : RustCall) : Tokens :=
  [call.name, "("] ++ ((call.arguments.map FieldPath.tokens).intersperse [","]).flatten ++ [")", ";"]

private def parseQuotedRustName (input : Tokens) : Except Error (String × Tokens) := do
  let word :: rest := input | throw (.syntax "quoted Rust crate or symbol")
  let '"' :: contents := word.toList | throw (.syntax "quoted Rust crate or symbol")
  let '"' :: reversed := contents.reverse | throw (.syntax "quoted Rust crate or symbol")
  if !reversed.isEmpty && reversed.all (fun c => c.isAlphanum || c == '_' || c == '-') then
    return (String.ofList reversed.reverse, rest)
  else throw (.syntax "quoted Rust crate or symbol")

private def parseRustParameter (input : Tokens) : Except Error (RustParameter × Tokens) := do
  let (name, rest) ← readName false input
  match ← expect [":", "["] rest with
  | "mut" :: rest => return (⟨name, .exclusive⟩, ← expect ["u8", "]"] rest)
  | rest => return (⟨name, .shared⟩, ← expect ["u8", "]"] rest)

private def parseRustArguments {α : Type} (parseItem : Tokens → Except Error (α × Tokens)) :
    Nat → Tokens → Except Error (List α × Tokens)
  | 0, _ => .error (.syntax "nonempty Rust arguments")
  | fuel + 1, input => do
    let (first, rest) ← parseItem input
    match rest with
    | ")" :: rest => return ([first], rest)
    | "," :: tail =>
      let (others, rest) ← parseRustArguments parseItem fuel tail
      return (first :: others, rest)
    | _ => throw (.syntax ", or )")

private def parseRustImports : Nat → Tokens → Except Error (List RustImport × Tokens)
  | fuel + 1, "@external" :: rest => do
    let (package, rest) ← parseQuotedRustName (← expect ["(", "rust", ","] rest)
    let (symbol, rest) ← parseQuotedRustName (← expect [","] rest)
    let (name, rest) ← readName false (← expect [")", "pub", "fn"] rest)
    let (parameters, rest) ← parseRustArguments parseRustParameter fuel (← expect ["("] rest)
    let (imports, rest) ← parseRustImports fuel (← expect ["->", "(", ")"] rest)
    return (⟨name, ⟨package, symbol⟩, parameters⟩ :: imports, rest)
  | _, rest => return ([], rest)

private def parseRustCalls : Nat → Tokens → Except Error (List RustCall × Tokens)
  | fuel + 1, name :: "(" :: rest => do
    let (name, _) ← readName false [name]
    let (arguments, rest) ← parseRustArguments parseField fuel rest
    let (calls, rest) ← parseRustCalls fuel (← expect [";"] rest)
    return (⟨name, arguments⟩ :: calls, rest)
  | _, rest => return ([], rest)

structure ParsedRustSource (input : String) where
  imports : List RustImport
  source : Source
  calls : List RustCall
  spelled : tokens input = imports.flatMap RustImport.tokens ++
    source.tokensWithCallTrailer (calls.flatMap RustCall.tokens)

def parseRustSource (input : String) : Except Error (ParsedRustSource input) := do
  let spelling := tokens input
  let (imports, rest) ← parseRustImports spelling.length spelling
  let (source, calls) ← parseSourceWithCallTrailer (parseRustCalls spelling.length) rest
  if imports.isEmpty || calls.isEmpty then throw (.syntax "Rust import and call")
  else if spelled : spelling = imports.flatMap RustImport.tokens ++
      source.tokensWithCallTrailer (calls.flatMap RustCall.tokens) then
    return ⟨imports, source, calls, spelled⟩
  else throw (.syntax "canonical Rust call fragment")

abbrev RustFieldArgument (checked : CheckedRecord) := Fin checked.mir.fields.length × AccessMode

inductive RustArgumentsAt (checked : CheckedRecord) :
    List FieldPath → List RustParameter → List (RustFieldArgument checked) → Prop where
  | nil : RustArgumentsAt checked [] [] []
  | cons : FieldAt checked.source checked.source.currentRoot (checked.source.fields.map Prod.fst)
      path field.val → RustArgumentsAt checked paths parameters fields →
      RustArgumentsAt checked (path :: paths) (parameter :: parameters) ((field, parameter.mode) :: fields)

private def lowerRustArguments (checked : CheckedRecord) (name : String) :
    (paths : List FieldPath) → (parameters : List RustParameter) →
      Except Error { fields : List (RustFieldArgument checked) // RustArgumentsAt checked paths parameters fields }
  | [], [] => pure ⟨[], .nil⟩
  | path :: paths, parameter :: parameters => do
    let resolved ← resolveField checked.source checked.source.currentRoot (checked.source.fields.map Prod.fst) path
    let bound : resolved.val < checked.mir.fields.length := by
      rw [checked.lowers.initialBytes]
      exact (List.getElem?_eq_some_iff.mp resolved.property.2.2.choose_spec).choose
    let tail ← lowerRustArguments checked name paths parameters
    return ⟨(⟨resolved.val, bound⟩, parameter.mode) :: tail.val, .cons resolved.property tail.property⟩
  | _, _ => throw (.invalidArgument name)

structure CheckedRustCall (checked : CheckedRecord) (imports : List RustImport) (call : RustCall) where
  decl : RustImport
  declared : decl ∈ imports
  named : decl.name = call.name
  fields : List (RustFieldArgument checked)
  resolved : RustArgumentsAt checked call.arguments decl.parameters fields
  compatible : fields.Pairwise RustFieldsCompatible

private instance {n : Nat} (left right : Fin n × AccessMode) : Decidable (RustFieldsCompatible left right) :=
  inferInstanceAs (Decidable (left.1 ≠ right.1 ∨ left.2.Compatible right.2))

private def checkRustCall (checked : CheckedRecord) (imports : List RustImport) (call : RustCall) :
    Except Error (CheckedRustCall checked imports call) := do
  match found : imports.find? (·.name == call.name) with
  | none => throw (.unknownFunction call.name)
  | some decl =>
    let resolved ← lowerRustArguments checked call.name call.arguments decl.parameters
    if apart : resolved.val.Pairwise RustFieldsCompatible then
      return ⟨decl, List.mem_of_find?_eq_some found,
        beq_iff_eq.mp (List.find?_some (p := fun item : RustImport => item.name == call.name) found),
        resolved.val, resolved.property, apart⟩
    else throw .resourceConflict

inductive CheckedRustCalls (checked : CheckedRecord) (imports : List RustImport) : List RustCall → Type where
  | nil : CheckedRustCalls checked imports []
  | cons : CheckedRustCall checked imports call → CheckedRustCalls checked imports rest →
      CheckedRustCalls checked imports (call :: rest)

private def checkRustCalls (record : CheckedRecord) (imports : List RustImport) :
    (calls : List RustCall) → Except Error (CheckedRustCalls record imports calls)
  | [] => pure .nil
  | head :: tail => return .cons (← checkRustCall record imports head) (← checkRustCalls record imports tail)

structure VerifiedRustSource (input : String) where
  parsed : ParsedRustSource input
  uniqueNames : (parsed.imports.map RustImport.name ++ parsed.source.functions.map Helper.name ++ ["main"]).Nodup
  record : CheckedRecord
  same : record.source = parsed.source
  calls : CheckedRustCalls record parsed.imports parsed.calls

def verifyRustSource (input : String) : Except Error (VerifiedRustSource input) := do
  let parsed ← parseRustSource input
  let names := parsed.imports.map RustImport.name ++ parsed.source.functions.map Helper.name ++ ["main"]
  if unique : names.Nodup then
    for decl in parsed.imports do
      if !(decl.parameters.map RustParameter.name).Nodup then throw (.duplicateParameter decl.name)
    let ⟨record, same⟩ ← checkRecord parsed.source
    let calls ← checkRustCalls record parsed.imports parsed.calls
    return ⟨parsed, unique, record, same, calls⟩
  else throw (.syntax "distinct Rust imports and functions")

structure RustCallMIR where
  name : String
  target : RustSymbol
  fields : List (Nat × AccessMode)
  deriving Repr, DecidableEq, ToJson, FromJson

def CheckedRustCalls.mir {checked : CheckedRecord} {imports : List RustImport} {calls : List RustCall} :
    CheckedRustCalls checked imports calls → List RustCallMIR
  | .nil => []
  | .cons head tail =>
    ⟨head.decl.name, head.decl.target, head.fields.map fun (field, mode) => (field.val, mode)⟩ :: tail.mir

structure RustSourceMIR where
  record : SourceMIR
  imports : List RustImport
  calls : List RustCallMIR
  deriving Repr, DecidableEq, ToJson, FromJson

def VerifiedRustSource.mir {input : String} (accepted : VerifiedRustSource input) : RustSourceMIR :=
  ⟨accepted.record.mir, accepted.parsed.imports, accepted.calls.mir⟩

structure MatchingRustMIR (input text : String) where
  accepted : VerifiedRustSource input
  decoded : decodeCanonicalMIR text = .ok accepted.mir

def verifyRustMIR (input text : String) : Except Error (MatchingRustMIR input text) := do
  let accepted ← verifyRustSource input
  let decoded ← matchCanonicalMIR text accepted.mir
  return ⟨accepted, decoded.down⟩

theorem MatchingRustMIR.corresponds {input text : String} (matching : MatchingRustMIR input text) :
    ∃ (parsed : ParsedRustSource input) (record : CheckedRecord)
      (calls : CheckedRustCalls record parsed.imports parsed.calls),
      SourceTrace parsed.source record.mir ∧
        decodeCanonicalMIR text = .ok (⟨record.mir, parsed.imports, calls.mir⟩ : RustSourceMIR) :=
  ⟨matching.accepted.parsed, matching.accepted.record, matching.accepted.calls,
    matching.accepted.same ▸ matching.accepted.record.lowers, matching.decoded⟩

/-- A model supplies the finite accesses of a particular linked Rust symbol.
The runtime behavior of a native adapter is a separate contract. -/
abbrev RustModels := RustSymbol → Option (List RustAdapterAccess)

deriving instance ToJson, FromJson for RustArgumentByte, RustAdapterAccess

structure RustModel where
  target : RustSymbol
  accesses : List RustAdapterAccess
  deriving FromJson

def decodeRustModels (text : String) : Except String RustModels := do
  let models : List RustModel ← fromJson? (← Json.parse text)
  if (models.map RustModel.target).Nodup then
    return fun target => (models.find? (fun model => decide (model.target = target))).map RustModel.accesses
  else throw "duplicate Rust model symbol"

def CheckedRustCall.slices {checked : CheckedRecord} {imports : List RustImport} {call : RustCall}
    (accepted : CheckedRustCall checked imports call) : List RustSliceSpec :=
  checked.mir.rustFieldArguments accepted.fields

def CheckedRustCalls.run {checked : CheckedRecord} {imports : List RustImport} {calls : List RustCall}
    (model : RustModels) : CheckedRustCalls checked imports calls → State → Option State
  | .nil, state => some state
  | .cons head tail, state => do
    let trace ← model head.decl.target
    let next ← runRustAdapterTrace state head.slices trace
    tail.run model next

inductive RustCallsExecute {checked : CheckedRecord} {imports : List RustImport} (model : RustModels) :
    {calls : List RustCall} → CheckedRustCalls checked imports calls → State → State → Prop where
  | nil : RustCallsExecute model .nil state state
  | cons {head : CheckedRustCall checked imports call} {tail : CheckedRustCalls checked imports calls}
      {trace : List RustAdapterAccess} :
      model head.decl.target = some trace →
      RustAdapterTraceLowers head.slices state.freshView trace program →
      RustBorrowedExec state head.slices program next →
      RustCallsExecute model tail next final →
      RustCallsExecute model (.cons head tail) state final

theorem CheckedRustCalls.run_correct {checked : CheckedRecord} {imports : List RustImport} {calls : List RustCall}
    (accepted : CheckedRustCalls checked imports calls) (model : RustModels) (state final : State) :
    accepted.run model state = some final ↔ RustCallsExecute model accepted state final := by
  induction accepted generalizing state final with
  | nil =>
    constructor
    · intro same
      obtain rfl := Option.some.inj same
      exact .nil
    · intro ran
      cases ran
      rfl
  | cons head tail ih =>
    simp only [run, bind, Option.bind_eq_some_iff, runRustAdapterTrace_correct, ih]
    constructor
    · rintro ⟨trace, supplied, next, ⟨program, lowered, ran⟩, rest⟩
      exact .cons supplied lowered ran rest
    · intro ran
      cases ran with
      | cons supplied lowered ran rest =>
        exact ⟨_, supplied, _, ⟨_, lowered, ran⟩, rest⟩

def CheckedRustCalls.ModelCovers {checked : CheckedRecord} {imports : List RustImport} {calls : List RustCall}
    (model : RustModels) : CheckedRustCalls checked imports calls → Prop
  | .nil => True
  | .cons head tail =>
    (∃ trace, model head.decl.target = some trace ∧
      ∀ start, ∃ program, RustAdapterTraceLowers head.slices start trace program) ∧ tail.ModelCovers model

theorem CheckedRustCalls.run_total {checked : CheckedRecord} {imports : List RustImport} {calls : List RustCall}
    (accepted : CheckedRustCalls checked imports calls) (model : RustModels) {entry state : State}
    (entered : Core.run {} checked.mir.entry = some entry) (restored : state.resources = entry.resources)
    (covers : accepted.ModelCovers model) :
    ∃ final, RustCallsExecute model accepted state final ∧ final.resources = entry.resources := by
  induction accepted generalizing state with
  | nil => exact ⟨_, .nil, restored⟩
  | cons head tail ih =>
    obtain ⟨⟨trace, supplied, admitted⟩, coveredTail⟩ := covers
    obtain ⟨program, lowered⟩ := admitted state.freshView
    have safe := (checked.mir.rustBorrowPlan_at_restored_resources head.fields entered restored).mpr head.compatible
    have closed : state.views = [] :=
      (congrArg ResourceState.views restored).trans (checked.mir.entry_views entered)
    have compatible : state.ViewsCompatible := by simp [State.ViewsCompatible, closed]
    obtain ⟨next, ran, returned, _⟩ := runRustBorrowedCall_total safe compatible lowered.authorized
    obtain ⟨final, rest, preserved⟩ := ih (returned.trans restored) coveredTail
    exact ⟨final, .cons supplied lowered ((runRustBorrowedCall_correct ..).mp ran) rest, preserved⟩

def CheckedRustCalls.Writes {checked : CheckedRecord} {imports : List RustImport} {calls : List RustCall} :
    CheckedRustCalls checked imports calls → ByteLocation → Prop
  | .nil, _ => False
  | .cons head tail, location => RustCallWrites head.slices location ∨ tail.Writes location

theorem RustCallsExecute.trace_and_frame {checked : CheckedRecord} {imports : List RustImport}
    {calls : List RustCall} {accepted : CheckedRustCalls checked imports calls} {model : RustModels}
    {state final : State} (execution : RustCallsExecute model accepted state final)
    (compatible : state.ViewsCompatible) :
    (∃ instructions, Runs state instructions final) ∧ final.resources = state.resources ∧
      ∀ location, ¬ accepted.Writes location → final.byte location = state.byte location := by
  induction execution with
  | nil => exact ⟨⟨[], .nil⟩, rfl, fun _ _ => rfl⟩
  | cons _ _ invoked _ ih =>
    obtain ⟨first, entered⟩ := invoked.trace
    obtain ⟨restored, frame⟩ := invoked.restores_scope compatible
    obtain ⟨⟨rest, invokedRest⟩, resources, frameRest⟩ := ih (entered.views_compatible compatible)
    refine ⟨⟨first ++ rest, entered.append invokedRest⟩, resources.trans restored, fun location outside => ?_⟩
    exact (frameRest location (fun write => outside (.inr write))).trans
      (frame location (fun write => outside (.inl write)))

def VerifiedRustSource.run {input : String} (accepted : VerifiedRustSource input)
    (model : RustModels) : Option UInt8 := do
  let entry ← Core.run {} accepted.record.mir.entry
  let body ← accepted.record.mir.body.run 0 entry
  let returned ← accepted.calls.run model body
  let final ← Core.run returned accepted.record.mir.exit
  final.observations.head?

def RustSourceExecutes {input : String} (accepted : VerifiedRustSource input)
    (model : RustModels) (value : UInt8) : Prop :=
  ∃ entry steps body returned final,
    Runs {} accepted.record.mir.entry entry ∧
    Structured.Executes Functional.Env.empty entry
      (accepted.record.mir.body.toCode 0 (fun _ => .finish) []) steps body ∧
    RustCallsExecute model accepted.calls body returned ∧ Runs returned accepted.record.mir.exit final ∧
    final.observations.head? = some value

theorem VerifiedRustSource.run_correct {input : String} (accepted : VerifiedRustSource input)
    (model : RustModels) (value : UInt8) : accepted.run model = some value ↔ RustSourceExecutes accepted model value := by
  simp only [run, bind, Option.bind_eq_some_iff, Core.run_correct, CheckedRustCalls.run_correct, RustSourceExecutes]
  constructor
  · rintro ⟨entry, entered, body, computed, returned, calls, final, finished, observed⟩
    obtain ⟨steps, ran⟩ := Operations.run_executes computed
    exact ⟨entry, steps, body, returned, final, entered, ran, calls, finished, observed⟩
  · rintro ⟨entry, steps, body, returned, final, entered, ran, calls, finished, observed⟩
    exact ⟨entry, entered, body, Operations.executes_run ran, returned, calls, final, finished, observed⟩

theorem VerifiedRustSource.run_total {input : String} (accepted : VerifiedRustSource input) (model : RustModels)
    (covers : accepted.calls.ModelCovers model) :
    ∃ value, accepted.run model = some value ∧ RustSourceExecutes accepted model value := by
  obtain ⟨entry, entered⟩ := SourceMIR.entry_runs accepted.record.checked
  have bodyOK := SourceMIR.body_checked accepted.record.checked entered
  obtain ⟨body, computed, restored⟩ := Operations.run_preserves_resources bodyOK
  obtain ⟨steps, ran⟩ := Operations.run_executes computed
  obtain ⟨returned, calls, preserved⟩ := accepted.calls.run_total model entered restored covers
  obtain ⟨final, finished, _⟩ := SourceMIR.exit_runs accepted.record.checked entered preserved
  obtain ⟨_, value, _, _, observed⟩ := accepted.record.mir.exit_result finished
  have executes : RustSourceExecutes accepted model value :=
    ⟨entry, steps, body, returned, final, run_sound entered, ran, calls, finished, observed⟩
  exact ⟨value, (accepted.run_correct model value).mpr executes, executes⟩

theorem RustSourceExecutes.prefix_safe {input : String} {accepted : VerifiedRustSource input}
    {model : RustModels} {value : UInt8} (execution : RustSourceExecutes accepted model value) :
    ∃ trace final, Runs {} trace final ∧ final.views = [] ∧ final.observations.head? = some value ∧
      ∀ first rest, trace = first ++ rest →
        ∃ middle, Runs {} first middle ∧ Runs middle rest final ∧
          middle.OwnersValid ∧ middle.ReferencesLive ∧ middle.ViewsCompatible := by
  obtain ⟨entry, _, body, returned, final, entered, ran, calls, finished, observed⟩ := execution
  have bodyTrace := entered.append ran.trace
  obtain ⟨⟨_, traced⟩, restored, _⟩ :=
    calls.trace_and_frame (bodyTrace.views_compatible State.empty_views_compatible)
  have resources := accepted.record.body_restored (run_complete entered) (Operations.executes_run ran)
  obtain ⟨exited, exitRun, closed⟩ :=
    SourceMIR.exit_runs accepted.record.checked (run_complete entered) (restored.trans resources)
  have sameExit : exited = final := Option.some.inj ((run_complete exitRun).symm.trans (run_complete finished))
  have combined := (bodyTrace.append traced).append finished
  exact ⟨_, final, combined, sameExit ▸ closed, observed, fun _ _ split => (split ▸ combined).prefix_safe⟩

end Aethel.SourceVerification
