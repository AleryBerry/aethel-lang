import Aethel.SourceMIR

namespace Aethel.SourceVerification

open Core

/-- Reference grammar for sequential programs over a flat byte record. -/
structure FieldPath where
  root : String
  field : String

inductive SourcePlace where
  | field (path : FieldPath)
  | view (name : String)

abbrev SourceStoreTask := List (FieldPath × UInt8)

inductive ByteBranch where
  | conditional (comparison : Comparison) (right : ByteOperand SourcePlace)
  | literalCase (value : UInt8)

def ByteBranch.comparison : ByteBranch → Comparison
  | .conditional comparison _ => comparison
  | .literalCase _ => .equal

def ByteBranch.operand : ByteBranch → ByteOperand SourcePlace
  | .conditional _ right => right
  | .literalCase value => .literal value

inductive Body where
  | done
  | discard (place : SourcePlace) (next : Body)
  | assign (destination : SourcePlace) (value : UInt8) (next : Body)
  | copy (destination source : SourcePlace) (next : Body)
  | subtractFrom (destination source : SourcePlace) (amount : UInt8) (next : Body)
  | assignCall (destination : SourcePlace) (name argument : String) (next : Body)
  | view (mode : AccessMode) (name : String) (target : SourcePlace) (inside next : Body)
  | branch (place : SourcePlace) (form : ByteBranch) (yes no next : Body)
  | range (first stop : ByteOperand SourcePlace) (body next : Body)
  | countdown (counter : FieldPath) (threshold amount : UInt8) (positive : 0 < amount.toNat)
      (afterDecrease next : Body)
  | call (name argument : String) (next : Body)
  | bindView (binding callee argument : String) (inside : Body)
  | forkStores (tasks : List SourceStoreTask) (next : Body)

private def SourcePlace.viewUses : SourcePlace → List String
  | .field _ => []
  | .view name => [name]

private def ByteOperand.viewUses : ByteOperand SourcePlace → List String
  | .literal _ => []
  | .place target => target.viewUses

/-- Candidate reads and writes of a view name on any path in a statement
block, including guards and nested bindings. -/
def Body.viewUses : Body → List String
  | .done => []
  | .discard place next | .assign place _ next | .assignCall place _ _ next =>
    place.viewUses ++ next.viewUses
  | .copy target source next | .subtractFrom target source _ next =>
    target.viewUses ++ source.viewUses ++ next.viewUses
  | .branch place form yes no next =>
    place.viewUses ++ form.operand.viewUses ++ yes.viewUses ++ no.viewUses ++ next.viewUses
  | .range first stop body next =>
    first.viewUses ++ stop.viewUses ++ body.viewUses ++ next.viewUses
  | .view _ _ target body next => target.viewUses ++ body.viewUses ++ next.viewUses
  | .countdown _ _ _ _ body next => body.viewUses ++ next.viewUses
  | .call _ _ next | .bindView _ _ _ next | .forkStores _ next => next.viewUses

inductive HelperResult where
  | unit
  | byte (field : FieldPath)
  | view (mode : AccessMode) (field : FieldPath)

structure Helper where
  name : String
  parameter : String
  paths : List String
  body : Body
  result : HelperResult

structure Source where
  record : String
  root : String
  fields : List (String × UInt8)
  moves : List OwnerMove
  functions : List Helper
  body : Body
  result : FieldPath

def ownerAfter (owner : String) : List OwnerMove → String
  | [] => owner
  | move :: rest => ownerAfter move.toName rest

def Source.currentRoot (source : Source) : String :=
  ownerAfter source.root source.moves

private def emitToken (word : List Char) (rest : List String) : List String :=
  if word.isEmpty then rest else String.ofList word.reverse :: rest

private def tokenize : List Char → List Char → List String
  | [], word => emitToken word []
  | '/' :: '/' :: chars, word => emitToken word (tokenize (chars.dropWhile (· != '\n')) [])
  | '-' :: '>' :: chars, word => emitToken word ("->" :: tokenize chars [])
  | '-' :: '|' :: chars, word => emitToken word ("-|" :: tokenize chars [])
  | '=' :: '=' :: chars, word => emitToken word ("==" :: tokenize chars [])
  | '!' :: '=' :: chars, word => emitToken word ("!=" :: tokenize chars [])
  | '<' :: '=' :: chars, word => emitToken word ("<=" :: tokenize chars [])
  | '>' :: '=' :: chars, word => emitToken word (">=" :: tokenize chars [])
  | '~' :: '>' :: chars, word => emitToken word ("~>" :: tokenize chars [])
  | '.' :: '.' :: chars, word => emitToken word (".." :: tokenize chars [])
  | c :: chars, word =>
    if c.isWhitespace then
      emitToken word (tokenize chars [])
    else if "{}().,:=;<>".contains c then
      emitToken word (String.singleton c :: tokenize chars [])
    else
      tokenize chars (c :: word)
termination_by chars _ => chars.length
decreasing_by
  all_goals simp_wf <;> try omega
  exact Nat.lt_of_le_of_lt (List.dropWhile_sublist _).length_le (by omega)

def tokens (input : String) : List String :=
  tokenize input.toList []

private def FieldPath.tokens (p : FieldPath) : List String :=
  [p.root, ".", p.field]

private def SourcePlace.tokens : SourcePlace → List String
  | .field path => path.tokens
  | .view name => [name]

private def modeToken : AccessMode → String
  | .shared => "shared"
  | .exclusive => "exclusive"

private def modeTypeToken : AccessMode → String
  | .shared => "Shared"
  | .exclusive => "Exclusive"

def byteToken (value : UInt8) : String := toString value ++ "u8"

private def ByteOperand.tokens {α : Type} (encode : α → List String) : ByteOperand α → List String
  | .literal value => [byteToken value]
  | .place target => encode target

private def FieldPath.countdownPrefix (counter : FieldPath) : List String :=
  counter.tokens ++ ["{"] ++ counter.tokens ++ ["="] ++ counter.tokens ++
    ["-|"]

private def comparisonToken : Comparison → String
  | .equal => "=="
  | .unequal => "!="
  | .less => "<"
  | .lessEqual => "<="
  | .greater => ">"
  | .greaterEqual => ">="

private def SourceStoreTask.tokens (task : SourceStoreTask) : List String :=
  task.flatMap fun (field, value) => field.tokens ++ ["=", byteToken value, ";"]

/-- The grammar spells out each operation, scope delimiter, and initializer. -/
private def Body.tokens : Body → List String
  | .done => []
  | .discard place next => ["let", "_", "="] ++ place.tokens ++ [";"] ++ next.tokens
  | .assign path value next => path.tokens ++ ["=", byteToken value, ";"] ++ next.tokens
  | .copy path source next => path.tokens ++ ["="] ++ source.tokens ++ [";"] ++ next.tokens
  | .subtractFrom path source amount next =>
    path.tokens ++ ["="] ++ source.tokens ++ ["-|", byteToken amount, ";"] ++ next.tokens
  | .assignCall path name argument next =>
    path.tokens ++ ["=", name, "(", argument, ")", ";"] ++ next.tokens
  | .view mode name path inside next =>
    ["view", modeToken mode, name, "="] ++ path.tokens ++ ["{"] ++ inside.tokens ++ ["}", ";"] ++ next.tokens
  | .branch place (.conditional comparison right) yes no next =>
    ["if"] ++ place.tokens ++ [comparisonToken comparison] ++ ByteOperand.tokens SourcePlace.tokens right ++ ["{"] ++
      yes.tokens ++ ["}", "else", "{"] ++ no.tokens ++ ["}", ";"] ++ next.tokens
  | .branch place (.literalCase literal) matched fallback next =>
    ["case"] ++ place.tokens ++ ["{", byteToken literal, "->", "{"] ++ matched.tokens ++
      ["}", "_", "->", "{"] ++ fallback.tokens ++ ["}", "}", ";"] ++ next.tokens
  | .range first stop body next =>
    ["for", "_", "in"] ++ ByteOperand.tokens SourcePlace.tokens first ++ [".."] ++
      ByteOperand.tokens SourcePlace.tokens stop ++ ["{"] ++ body.tokens ++ ["}", ";"] ++ next.tokens
  | .countdown counter threshold amount _ afterDecrease next =>
    ["while"] ++ counter.tokens ++ [">", byteToken threshold, "decreases"] ++ counter.countdownPrefix ++
      [byteToken amount, ";"] ++ afterDecrease.tokens ++ ["}", ";"] ++ next.tokens
  | .call name argument next => [name, "(", argument, ")", ";"] ++ next.tokens
  | .bindView binding callee argument inside =>
    ["let", binding, "=", callee, "(", argument, ")", ";"] ++ inside.tokens
  | .forkStores tasks next =>
    ["fork", "{"] ++ tasks.flatMap (fun task => ["{"] ++ task.tokens ++ ["}"]) ++
      ["}", "join", ";"] ++ next.tokens

private structure Body.Head (body : Body) where
  next : Body
  attach : Body → Body
  reconstructs : attach next = body
  spells : ∀ tail, (attach tail).tokens = (attach .done).tokens ++ tail.tokens
  uses : ∀ tail, (attach tail).viewUses = (attach .done).viewUses ++ tail.viewUses
  size : ∀ tail, sizeOf tail ≤ sizeOf next → sizeOf (attach tail) ≤ sizeOf body
  smaller : sizeOf next < sizeOf body

/-- Only the outer statement spine is split. In particular, a returned-view
binding keeps its entire lexical continuation together. -/
private def Body.head (body : Body) : Option (Body.Head body) := by
  cases body
  case done => exact none
  case bindView => exact none
  case' discard place next => refine some ⟨next, .discard place, rfl, ?_, ?_, ?_, ?_⟩
  case' assign path value next => refine some ⟨next, .assign path value, rfl, ?_, ?_, ?_, ?_⟩
  case' copy path source next => refine some ⟨next, .copy path source, rfl, ?_, ?_, ?_, ?_⟩
  case' subtractFrom path source amount next =>
    refine some ⟨next, .subtractFrom path source amount, rfl, ?_, ?_, ?_, ?_⟩
  case' assignCall path name argument next =>
    refine some ⟨next, .assignCall path name argument, rfl, ?_, ?_, ?_, ?_⟩
  case' view mode name target inside next =>
    refine some ⟨next, .view mode name target inside, rfl, ?_, ?_, ?_, ?_⟩
  case' branch place form yes no next =>
    cases form
    case' conditional comparison right =>
      refine some ⟨next, .branch place (.conditional comparison right) yes no, rfl, ?_, ?_, ?_, ?_⟩
    case' literalCase value =>
      refine some ⟨next, .branch place (.literalCase value) yes no, rfl, ?_, ?_, ?_, ?_⟩
  case' range first stop body next =>
    refine some ⟨next, .range first stop body, rfl, ?_, ?_, ?_, ?_⟩
  case' countdown counter threshold amount positive body next =>
    refine some ⟨next, .countdown counter threshold amount positive body, rfl, ?_, ?_, ?_, ?_⟩
  case' call name argument next => refine some ⟨next, .call name argument, rfl, ?_, ?_, ?_, ?_⟩
  case' forkStores tasks next => refine some ⟨next, .forkStores tasks, rfl, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro tail; simp [Body.tokens, Body.viewUses, List.append_assoc]; done)
    | (intros; simp_wf; omega)

private theorem Body.done_min_size (body : Body) : sizeOf Body.done ≤ sizeOf body := by
  cases body <;> simp_wf <;> omega

structure Body.LoanWindow (name : String) (body : Body) where
  before : Body
  after : Body
  beforeSize : sizeOf before ≤ sizeOf body
  afterSize : sizeOf after ≤ sizeOf body
  spells : before.tokens ++ after.tokens = body.tokens
  unused : name ∉ after.viewUses

private inductive Body.ViewUse (name : String) (body : Body) where
  | unused : name ∉ body.viewUses → Body.ViewUse name body
  | atEnd : Body.ViewUse name body
  | cut : Body.LoanWindow name body → Body.ViewUse name body

private def Body.locateViewUse (name : String) (body : Body) : Body.ViewUse name body :=
  match body.head with
  | none => if active : name ∈ body.viewUses then .atEnd else .unused active
  | some head =>
    match head.next.locateViewUse name with
    | .atEnd => .atEnd
    | .cut split => .cut {
        before := head.attach split.before
        after := split.after
        beforeSize := head.size _ split.beforeSize
        afterSize := Nat.le_trans split.afterSize (Nat.le_of_lt head.smaller)
        spells := by rw [head.spells, List.append_assoc, split.spells, ← head.spells, head.reconstructs]
        unused := split.unused
      }
    | .unused unused =>
      if active : name ∈ (head.attach .done).viewUses then
        match head.next with
        | .done => .atEnd
        | _ => .cut {
            before := head.attach .done
            after := head.next
            beforeSize := head.size _ (Body.done_min_size _)
            afterSize := Nat.le_of_lt head.smaller
            spells := by rw [← head.spells, head.reconstructs]
            unused := unused
          }
      else .unused (by
        rw [← head.reconstructs, head.uses, List.mem_append]
        exact not_or.mpr ⟨active, unused⟩)
termination_by sizeOf body
decreasing_by exact head.smaller

/-- End the loan after the last complete statement that may access it. A block
with no mentions or no trailing statements keeps its original reservation. -/
def Body.loanWindow (name : String) (body : Body) : Body.LoanWindow name body :=
  match body.locateViewUse name with
  | .cut split => split
  | _ => ⟨body, .done, Nat.le_refl _, Body.done_min_size _, by simp [Body.tokens], by simp [Body.viewUses]⟩

private def HelperResult.signatureTokens : HelperResult → List String
  | .unit => []
  | .byte _ => ["->", "u8"]
  | .view mode _ => ["->", "View", "(", "u8", ",", modeTypeToken mode, ")"]

private def HelperResult.valueTokens : HelperResult → List String
  | .unit => []
  | .byte field | .view _ field => field.tokens

private def Helper.tokens (record : String) (helper : Helper) : List String :=
  ["fn", helper.name, "(", helper.parameter, ":", record, "~>", ".", "{"] ++
    List.intersperse "," helper.paths ++ ["}", ")"] ++ helper.result.signatureTokens ++ ["{"] ++
    helper.body.tokens ++ helper.result.valueTokens ++ ["}"]

def Source.tokens (source : Source) : List String :=
  ["type", source.record, "{"] ++
    source.fields.flatMap (fun (name, _) => [name, ":", "u8", ","]) ++
    ["}"] ++ source.functions.flatMap (Helper.tokens source.record) ++
    ["fn", "main", "(", ")", "->", "u8", "{", "let", "mut", source.root, "=", source.record, "{"] ++
    source.fields.flatMap (fun (name, value) => [name, ":", byteToken value, ","]) ++
    ["}", ";"] ++
    source.moves.flatMap (fun move => ["let", "mut", move.toName, "=", "move", move.fromName, ";"]) ++
    source.body.tokens ++ source.result.tokens ++ ["}"]

inductive Error where
  | syntax (expected : String)
  | unknownField (root field : String)
  | unknownView (name : String)
  | duplicateView (name : String)
  | immutableView (name : String)
  | unknownFunction (name : String)
  | duplicateFunction (name : String)
  | duplicateParameter (function : String)
  | invalidContract (name : String)
  | invalidArgument (name : String)
  | invalidCallResult (name : String)
  | invalidDecreases
  | invalidReborrow (parent : String)
  | invalidMove (fromName toName : String)
  | sourceMIRMismatch
  | invalidSourceMIR
  | resourceConflict
  | unknownBinding (name : String)
  | coreType
  | coreStuck
  deriving Repr, DecidableEq

abbrev Tokens := List String

private def validName (upper : Bool) (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
    (if upper then first.isUpper else first.isLower) &&
      rest.all (fun c => c.isAlphanum || c == '_') &&
      !["pub", "import", "as", "fn", "let", "mut", "const", "type", "opaque", "case",
        "if", "else", "while", "for", "in", "use", "return", "view", "move", "law",
        "extern", "true", "false", "todo", "panic", "fork", "join", "trait", "instance",
        "using", "with", "default"].contains name

def readName (upper : Bool) : Tokens → Except Error (String × Tokens)
  | word :: rest =>
    if validName upper word then .ok (word, rest) else .error (.syntax "identifier")
  | [] => .error (.syntax "identifier")

def expect (expected : Tokens) (input : Tokens) : Except Error Tokens :=
  if expected.isPrefixOf input then .ok (input.drop expected.length)
  else .error (.syntax (String.intercalate " " expected))

def parseByte : Tokens → Except Error (UInt8 × Tokens)
  | word :: rest => do
    let [digits, ""] := word.splitOn "u8" | throw (.syntax "decimal u8 literal")
    let some n := digits.toNat? | throw (.syntax "decimal u8 literal")
    if n < 256 then return (UInt8.ofNat n, rest)
    else throw (.syntax "u8 literal in 0..255")
  | [] => .error (.syntax "u8 literal")

private def parseField (input : Tokens) : Except Error (FieldPath × Tokens) := do
  let (root, rest) ← readName false input
  let (field, rest) ← readName false (← expect ["."] rest)
  return (⟨root, field⟩, rest)

private def parsePlace (input : Tokens) : Except Error (SourcePlace × Tokens) := do
  let (name, rest) ← readName false input
  match rest with
  | "." :: fields =>
    let (field, rest) ← readName false fields
    return (.field ⟨name, field⟩, rest)
  | _ => return (.view name, rest)

private def parseDeclFields : Nat → Tokens → Except Error (List String × Tokens)
  | _, "}" :: rest => .ok ([], rest)
  | 0, _ => .error (.syntax "record field or }")
  | fuel + 1, input => do
    let (name, rest) ← readName false input
    let (fields, rest) ← parseDeclFields fuel (← expect [":", "u8", ","] rest)
    return (name :: fields, rest)

private def parseInitializers : List String → Tokens → Except Error (List (String × UInt8) × Tokens)
  | [], input => do return ([], ← expect ["}", ";"] input)
  | field :: fields, input => do
    let (value, rest) ← parseByte (← expect [field, ":"] input)
    let (values, rest) ← parseInitializers fields (← expect [","] rest)
    return ((field, value) :: values, rest)

private def parseMode : Tokens → Except Error (AccessMode × Tokens)
  | "shared" :: rest => .ok (.shared, rest)
  | "exclusive" :: rest => .ok (.exclusive, rest)
  | _ => .error (.syntax "shared or exclusive")

private def parseComparison : Tokens → Except Error (Comparison × Tokens)
  | "==" :: rest => .ok (.equal, rest)
  | "!=" :: rest => .ok (.unequal, rest)
  | "<" :: rest => .ok (.less, rest)
  | "<=" :: rest => .ok (.lessEqual, rest)
  | ">" :: rest => .ok (.greater, rest)
  | ">=" :: rest => .ok (.greaterEqual, rest)
  | _ => .error (.syntax "byte comparison")

private def parseOperand (parseTarget : Tokens → Except Error (place × Tokens)) (input : Tokens) :
    Except Error (ByteOperand place × Tokens) := do
  if let .ok (value, rest) := parseByte input then
    return (.literal value, rest)
  let (source, rest) ← parseTarget input
  return (.place source, rest)

private def parseStoreTask : Nat → Tokens → Except Error (SourceStoreTask × Tokens)
  | _, "}" :: rest => .ok ([], rest)
  | 0, _ => .error (.syntax "literal store or }")
  | fuel + 1, input => do
    let (field, rest) ← parseField input
    let (value, rest) ← parseByte (← expect ["="] rest)
    let (tail, rest) ← parseStoreTask fuel (← expect [";"] rest)
    return ((field, value) :: tail, rest)

private def parseStoreTasks : Nat → Tokens → Except Error (List SourceStoreTask × Tokens)
  | _, "}" :: rest => .ok ([], rest)
  | fuel + 1, "{" :: rest => do
    let (task, rest) ← parseStoreTask fuel rest
    let (tail, rest) ← parseStoreTasks fuel rest
    return (task :: tail, rest)
  | _, _ => .error (.syntax "fork task block or }")

private def parseBody : Nat → Tokens → Except Error (Body × Tokens)
  | 0, _ => .error (.syntax "end of block")
  | fuel + 1, input =>
    match input with
    | "let" :: "_" :: "=" :: rest => do
      let (place, rest) ← parsePlace rest
      let (next, rest) ← parseBody fuel (← expect [";"] rest)
      return (.discard place next, rest)
    | "let" :: binding :: "=" :: callee :: "(" :: argument :: ")" :: ";" :: rest => do
      let (binding, _) ← readName false [binding]
      let (callee, _) ← readName false [callee]
      let (argument, _) ← readName false [argument]
      let (inside, rest) ← parseBody fuel rest
      return (.bindView binding callee argument inside, rest)
    | "view" :: rest => do
      let (mode, rest) ← parseMode rest
      let (name, rest) ← readName false rest
      let (path, rest) ← parsePlace (← expect ["="] rest)
      let (inside, rest) ← parseBody fuel (← expect ["{"] rest)
      let (next, rest) ← parseBody fuel (← expect ["}", ";"] rest)
      return (.view mode name path inside next, rest)
    | "if" :: rest => do
      let (place, rest) ← parsePlace rest
      let (comparison, rest) ← parseComparison rest
      let (right, rest) ← parseOperand parsePlace rest
      let (yes, rest) ← parseBody fuel (← expect ["{"] rest)
      let (no, rest) ← parseBody fuel (← expect ["}", "else", "{"] rest)
      let (next, rest) ← parseBody fuel (← expect ["}", ";"] rest)
      return (.branch place (.conditional comparison right) yes no next, rest)
    | "case" :: rest => do
      let (place, rest) ← parsePlace rest
      let (literal, rest) ← parseByte (← expect ["{"] rest)
      let (matched, rest) ← parseBody fuel (← expect ["->", "{"] rest)
      let (fallback, rest) ← parseBody fuel (← expect ["}", "_", "->", "{"] rest)
      let (next, rest) ← parseBody fuel (← expect ["}", "}", ";"] rest)
      return (.branch place (.literalCase literal) matched fallback next, rest)
    | "for" :: rest => do
      let (first, rest) ← parseOperand parsePlace (← expect ["_", "in"] rest)
      let (stop, rest) ← parseOperand parsePlace (← expect [".."] rest)
      let (body, rest) ← parseBody fuel (← expect ["{"] rest)
      let (next, rest) ← parseBody fuel (← expect ["}", ";"] rest)
      return (.range first stop body next, rest)
    | "while" :: rest => do
      let (counter, rest) ← parseField rest
      let (threshold, rest) ← parseByte (← expect [">"] rest)
      let rest ← expect ["decreases"] rest
      let expected := counter.countdownPrefix
      unless expected.isPrefixOf rest do throw .invalidDecreases
      let (amount, rest) ← (parseByte (rest.drop expected.length)).mapError (fun _ => .invalidDecreases)
      if positive : 0 < amount.toNat then
        let (afterDecrease, rest) ← parseBody fuel (← expect [";"] rest)
        let (next, rest) ← parseBody fuel (← expect ["}", ";"] rest)
        return (.countdown counter threshold amount positive afterDecrease next, rest)
      else throw .invalidDecreases
    | "fork" :: rest => do
      let (tasks, rest) ← parseStoreTasks fuel (← expect ["{"] rest)
      let (next, rest) ← parseBody fuel (← expect ["join", ";"] rest)
      return (.forkStores tasks next, rest)
    | name :: "(" :: argument :: ")" :: ";" :: rest => do
      let (name, _) ← readName false [name]
      let (argument, _) ← readName false [argument]
      let (next, rest) ← parseBody fuel rest
      return (.call name argument next, rest)
    | _ => match parsePlace input with
      | .ok (target, "=" :: name :: "(" :: argument :: ")" :: ";" :: rest) => do
        let (name, _) ← readName false [name]
        let (argument, _) ← readName false [argument]
        let (next, rest) ← parseBody fuel rest
        return (.assignCall target name argument next, rest)
      | .ok (target, "=" :: rest) => do
        let (value, rest) ← parseOperand parsePlace rest
        match value, rest with
        | .place source, "-|" :: more =>
          let (amount, rest) ← parseByte more
          let (next, rest) ← parseBody fuel (← expect [";"] rest)
          return (.subtractFrom target source amount next, rest)
        | _, rest =>
          let (next, rest) ← parseBody fuel (← expect [";"] rest)
          match value with
          | .literal literal => return (.assign target literal next, rest)
          | .place source => return (.copy target source next, rest)
      | _ => .ok (.done, input)

private def parsePaths : Nat → Tokens → Except Error (List String × Tokens)
  | 0, _ => .error (.syntax "field contract")
  | fuel + 1, input => do
    let (field, rest) ← readName false input
    match rest with
    | "," :: more =>
      let (fields, rest) ← parsePaths fuel more
      return (field :: fields, rest)
    | "}" :: rest => return ([field], rest)
    | _ => throw (.syntax ", or }")

private def parseHelpers (record : String) (bound : Nat) :
    Nat → Tokens → Except Error (List Helper × Tokens)
  | _, "fn" :: "main" :: rest => .ok ([], "fn" :: "main" :: rest)
  | 0, _ => .error (.syntax "fn main")
  | fuel + 1, input => do
    let (name, rest) ← readName false (← expect ["fn"] input)
    let (parameter, rest) ← readName false (← expect ["("] rest)
    let (paths, rest) ← parsePaths bound (← expect [":", record, "~>", ".", "{"] rest)
    let rest ← expect [")"] rest
    let (resultKind, rest) ← match rest with
      | "->" :: "u8" :: more => pure (some HelperResult.byte, more)
      | "->" :: "View" :: "(" :: "u8" :: "," :: mode :: ")" :: more =>
        match mode with
        | "Shared" => pure (some (HelperResult.view .shared), more)
        | "Exclusive" => pure (some (HelperResult.view .exclusive), more)
        | _ => throw (.syntax "Shared or Exclusive")
      | more => pure (none, more)
    let (body, rest) ← parseBody bound (← expect ["{"] rest)
    let (result, rest) ← if let some makeResult := resultKind then do
      let (field, tail) ← parseField rest
      pure (makeResult field, tail)
    else pure (HelperResult.unit, rest)
    let (functions, rest) ← parseHelpers record bound fuel (← expect ["}"] rest)
    return (⟨name, parameter, paths, body, result⟩ :: functions, rest)

private def parseMoves : Nat → Tokens → Except Error (List OwnerMove × Tokens)
  | fuel + 1, "let" :: "mut" :: toName :: "=" :: "move" :: fromName :: ";" :: tail => do
    let (target, _) ← readName false [toName]
    let (owner, _) ← readName false [fromName]
    let (rest, tail) ← parseMoves fuel tail
    return (⟨owner, target⟩ :: rest, tail)
  | _, rest => .ok ([], rest)

def parseSource (input : List String) : Except Error Source := do
  let (record, rest) ← readName true (← expect ["type"] input)
  let (fields, rest) ← parseDeclFields input.length (← expect ["{"] rest)
  let (functions, rest) ← parseHelpers record input.length input.length rest
  let (root, rest) ← readName false
    (← expect ["fn", "main", "(", ")", "->", "u8", "{", "let", "mut"] rest)
  let (initial, rest) ← parseInitializers fields (← expect ["=", record, "{"] rest)
  let (moves, rest) ← parseMoves input.length rest
  let (body, rest) ← parseBody input.length rest
  let (result, rest) ← parseField rest
  let [] ← expect ["}"] rest | throw (.syntax "end of file")
  return ⟨record, root, initial, moves, functions, body, result⟩

structure LawGuard where
  place : FieldPath
  comparison : Comparison
  bound : UInt8

private def LawGuard.tokens (guard : LawGuard) : Tokens :=
  ["when"] ++ guard.place.tokens ++ [comparisonToken guard.comparison, byteToken guard.bound]

structure ReturnLaw where
  name : String
  record : String
  parameter : String
  guard : Option LawGuard
  helper : String
  comparison : Comparison
  bound : ByteOperand FieldPath
  expected : Bool

def ReturnLaw.tokens (law : ReturnLaw) : List String :=
  ["law", law.name, "(", law.parameter, ":", law.record, ")", "{"] ++
  (law.guard.map LawGuard.tokens).getD [] ++ [
    if law.expected then "always" else "never", law.helper, "(", law.parameter, ")",
    comparisonToken law.comparison] ++ ByteOperand.tokens FieldPath.tokens law.bound ++ ["}"]

private def parseReturnLaw (input : Tokens) : Except Error (ReturnLaw × Tokens) := do
  let (name, tail) ← readName false (← expect ["law"] input)
  let (parameter, tail) ← readName false (← expect ["("] tail)
  let (record, tail) ← readName true (← expect [":"] tail)
  let (guard, tail) ← match ← expect [")", "{"] tail with
    | "when" :: rest => do
      let (place, rest) ← parseField rest
      let (comparison, rest) ← parseComparison rest
      let (bound, rest) ← parseByte rest
      pure (some (⟨place, comparison, bound⟩ : LawGuard), rest)
    | rest => pure (none, rest)
  let (expected, tail) ← match tail with
    | "always" :: rest => pure (true, rest)
    | "never" :: rest => pure (false, rest)
    | _ => throw (.syntax "always or never")
  let (helper, tail) ← readName false tail
  let (comparison, tail) ← parseComparison (← expect ["(", parameter, ")"] tail)
  let (bound, tail) ← parseOperand parseField tail
  let tail ← expect ["}"] tail
  return (⟨name, record, parameter, guard, helper, comparison, bound, expected⟩, tail)

private def parseLawDeclarations : Nat → Tokens → Except Error (List ReturnLaw)
  | _, [] => pure []
  | 0, _ => throw (.syntax "end of law file")
  | fuel + 1, input => do
    let (law, rest) ← parseReturnLaw input
    return law :: (← parseLawDeclarations fuel rest)

structure ParsedReturnLaws (input : String) where
  declarations : List ReturnLaw
  spelled : tokens input = declarations.flatMap ReturnLaw.tokens

def parseReturnLaws (input : String) : Except Error (ParsedReturnLaws input) := do
  let inputTokens := tokens input
  let declarations ← parseLawDeclarations inputTokens.length inputTokens
  if declarations.isEmpty then throw (.syntax "law")
  else if spelled : inputTokens = declarations.flatMap ReturnLaw.tokens then
    return ⟨declarations, spelled⟩
  else throw (.syntax "canonical return law")

end Aethel.SourceVerification
