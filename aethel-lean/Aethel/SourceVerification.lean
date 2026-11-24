import Aethel.SourceMIR
import Lean.Data.Json.Parser

namespace Aethel.SourceVerification

open Core Functional Structured Lean

/-- Reference grammar for sequential programs over a flat byte record. -/
structure FieldPath where
  root : String
  field : String

inductive ReadPlace where
  | field (path : FieldPath)
  | view (name : String)

inductive Body where
  | done
  | discard (place : ReadPlace) (next : Body)
  | assign (path : FieldPath) (value : UInt8) (next : Body)
  | view (mode : AccessMode) (name : String) (path : FieldPath) (inside next : Body)
  | branch (place : ReadPlace) (comparison : Comparison) (value : UInt8) (yes no next : Body)
  | call (name argument : String) (next : Body)

structure Helper where
  name : String
  parameter : String
  paths : List String
  body : Body

structure Source where
  record : String
  root : String
  fields : List (String × UInt8)
  functions : List Helper
  body : Body
  result : FieldPath

private def emitToken (word : List Char) (rest : List String) : List String :=
  if word.isEmpty then rest else String.ofList word.reverse :: rest

private def tokenize : List Char → List Char → List String
  | [], word => emitToken word []
  | '/' :: '/' :: chars, word => emitToken word (tokenize (chars.dropWhile (· != '\n')) [])
  | '-' :: '>' :: chars, word => emitToken word ("->" :: tokenize chars [])
  | '=' :: '=' :: chars, word => emitToken word ("==" :: tokenize chars [])
  | '!' :: '=' :: chars, word => emitToken word ("!=" :: tokenize chars [])
  | '<' :: '=' :: chars, word => emitToken word ("<=" :: tokenize chars [])
  | '~' :: '>' :: chars, word => emitToken word ("~>" :: tokenize chars [])
  | c :: chars, word =>
    if c.isWhitespace then
      emitToken word (tokenize chars [])
    else if "{}().,:=;<".contains c then
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

private def ReadPlace.tokens : ReadPlace → List String
  | .field path => path.tokens
  | .view name => [name]

private def modeToken : AccessMode → String
  | .shared => "shared"
  | .exclusive => "exclusive"

private def byteToken (value : UInt8) : String := toString value ++ "u8"

private def comparisonToken : Comparison → String
  | .equal => "=="
  | .unequal => "!="
  | .less => "<"
  | .lessEqual => "<="

/-- The grammar spells out each operation, scope delimiter, and initializer. -/
private def Body.tokens : Body → List String
  | .done => []
  | .discard place next => ["let", "_", "="] ++ place.tokens ++ [";"] ++ next.tokens
  | .assign path value next => path.tokens ++ ["=", byteToken value, ";"] ++ next.tokens
  | .view mode name path inside next =>
    ["view", modeToken mode, name, "="] ++ path.tokens ++ ["{"] ++ inside.tokens ++ ["}", ";"] ++ next.tokens
  | .branch place comparison value yes no next =>
    ["if"] ++ place.tokens ++ [comparisonToken comparison, byteToken value, "{"] ++
      yes.tokens ++ ["}", "else", "{"] ++ no.tokens ++ ["}", ";"] ++ next.tokens
  | .call name argument next => [name, "(", argument, ")", ";"] ++ next.tokens

private def Helper.tokens (record : String) (helper : Helper) : List String :=
  ["fn", helper.name, "(", helper.parameter, ":", record, "~>", ".", "{"] ++
    List.intersperse "," helper.paths ++ ["}", ")", "{"] ++ helper.body.tokens ++ ["}"]

def Source.tokens (source : Source) : List String :=
  ["type", source.record, "{"] ++
    source.fields.flatMap (fun (name, _) => [name, ":", "u8", ","]) ++
    ["}"] ++ source.functions.flatMap (Helper.tokens source.record) ++
    ["fn", "main", "(", ")", "->", "u8", "{", "let", "mut", source.root, "=", source.record, "{"] ++
    source.fields.flatMap (fun (name, value) => [name, ":", byteToken value, ","]) ++
    ["}", ";"] ++ source.body.tokens ++ source.result.tokens ++ ["}"]

inductive Error where
  | syntax (expected : String)
  | unknownField (root field : String)
  | unknownView (name : String)
  | duplicateView (name : String)
  | unknownFunction (name : String)
  | invalidContract (name : String)
  | invalidArgument (name : String)
  | sourceMIRMismatch
  | invalidSourceMIR
  | resourceConflict
  deriving Repr, DecidableEq

private abbrev Tokens := List String

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

private def readName (upper : Bool) : Tokens → Except Error (String × Tokens)
  | word :: rest =>
    if validName upper word then .ok (word, rest) else .error (.syntax "identifier")
  | [] => .error (.syntax "identifier")

private def expect (expected : Tokens) (input : Tokens) : Except Error Tokens :=
  if expected.isPrefixOf input then .ok (input.drop expected.length)
  else .error (.syntax (String.intercalate " " expected))

private def parseByte : Tokens → Except Error (UInt8 × Tokens)
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

private def parseRead (input : Tokens) : Except Error (ReadPlace × Tokens) := do
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
  | _ => .error (.syntax "byte comparison")

private def parseBody : Nat → Tokens → Except Error (Body × Tokens)
  | 0, _ => .error (.syntax "end of block")
  | fuel + 1, input =>
    match input with
    | "let" :: rest => do
      let (place, rest) ← parseRead (← expect ["_", "="] rest)
      let (next, rest) ← parseBody fuel (← expect [";"] rest)
      return (.discard place next, rest)
    | "view" :: rest => do
      let (mode, rest) ← parseMode rest
      let (name, rest) ← readName false rest
      let (path, rest) ← parseField (← expect ["="] rest)
      let (inside, rest) ← parseBody fuel (← expect ["{"] rest)
      let (next, rest) ← parseBody fuel (← expect ["}", ";"] rest)
      return (.view mode name path inside next, rest)
    | "if" :: rest => do
      let (place, rest) ← parseRead rest
      let (comparison, rest) ← parseComparison rest
      let (value, rest) ← parseByte rest
      let (yes, rest) ← parseBody fuel (← expect ["{"] rest)
      let (no, rest) ← parseBody fuel (← expect ["}", "else", "{"] rest)
      let (next, rest) ← parseBody fuel (← expect ["}", ";"] rest)
      return (.branch place comparison value yes no next, rest)
    | name :: "(" :: argument :: ")" :: ";" :: rest => do
      let (name, _) ← readName false [name]
      let (argument, _) ← readName false [argument]
      let (next, rest) ← parseBody fuel rest
      return (.call name argument next, rest)
    | root :: "." :: field :: "=" :: rest => do
      let (path, _) ← parseField [root, ".", field]
      let (value, rest) ← parseByte rest
      let (next, rest) ← parseBody fuel (← expect [";"] rest)
      return (.assign path value next, rest)
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
    let (body, rest) ← parseBody bound (← expect [")", "{"] rest)
    let (functions, rest) ← parseHelpers record bound fuel (← expect ["}"] rest)
    return (⟨name, parameter, paths, body⟩ :: functions, rest)

private def parse (input : Tokens) : Except Error Source := do
  let (record, rest) ← readName true (← expect ["type"] input)
  let (fields, rest) ← parseDeclFields input.length (← expect ["{"] rest)
  let (functions, rest) ← parseHelpers record input.length input.length rest
  let (root, rest) ← readName false
    (← expect ["fn", "main", "(", ")", "->", "u8", "{", "let", "mut"] rest)
  let (initial, rest) ← parseInitializers fields (← expect ["=", record, "{"] rest)
  let (body, rest) ← parseBody input.length rest
  let (result, rest) ← parseField rest
  let [] ← expect ["}"] rest | throw (.syntax "end of file")
  return ⟨record, root, initial, functions, body, result⟩

