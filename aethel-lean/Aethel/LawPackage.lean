import Aethel.SourceSyntax

namespace Aethel.LawPackage

open System
open SourceVerification (tokens)

structure Declaration where
  name : String
  text : String
  equality : Option (String × String × String)
  deriving Inhabited, BEq

structure Loaded where
  source : String
  record : String
  equalities : List (String × String × String)
  propositions : List Declaration

private def fail {α : Type} (message : String) : IO α := throw (IO.userError message)

private def identifier (s : String) : Bool :=
  (s.toList.head?.any fun c => c.isAlpha || c == '_') &&
  s.toList.all fun c => c.isAlphanum || c == '_'

private def qualified (s : String) : Bool := (s.splitOn ".").all identifier

private def sourceLines (s : String) : List String :=
  (s.splitOn "\n").map fun line => ((line.splitOn "//").head!).trimAscii.toString

private def header (lines : List String) : IO (List String × List String × String) := do
  let mut imports := []
  let mut uses := []
  let mut body := []
  for line in lines do
    if line.isEmpty then continue
    match tokens line with
    | "import" :: [name] =>
      unless body.isEmpty do fail "imports must precede declarations"
      unless identifier name do fail s!"invalid module name {name}"
      imports := imports ++ [name]
    | "use" :: "law" :: path =>
      unless body.isEmpty do fail "use law must precede declarations"
      let name := String.join path
      unless qualified name && tokens name == path do fail s!"invalid law name {name}"
      uses := uses ++ [name]
    | _ => body := body ++ [line]
  return (imports, uses, String.intercalate "\n" body)

private def parseDeclarations (ns : String) : Nat → List String → IO (List Declaration)
  | _, [] => pure []
  | 0, _ => fail "invalid law declarations"
  | fuel + 1, kind :: name :: tail => do
    unless identifier name do fail s!"invalid law name {name}"
    let full := ns ++ "." ++ name
    let clause := tail.takeWhile (· != "}")
    let "}" :: rest := tail.dropWhile (· != "}") | fail s!"unterminated {full}"
    let equality ← match kind, clause with
      | "law", ["(", param, ":", recName, ")", "{", "always", l, ".", x, "==", r, ".", y] => do
        unless [param, recName, x, y].all identifier && l == param && r == param do
          fail s!"invalid invariant path in {full}"
        pure (some (recName, x, y))
      | "law", _ => pure none
      | _, _ => fail s!"unsupported declaration {full}"
    let remaining ← parseDeclarations ns fuel rest
    if remaining.any (·.name == full) then fail s!"duplicate declaration {full}"
    return ⟨full, String.intercalate " " ([kind, name] ++ clause ++ ["}"]), equality⟩ :: remaining
  | _, _ => fail "incomplete law declaration"

private def stripTypeLaws (source : String) : IO (String × String × List Declaration) := do
  let "type" :: record :: "{" :: rest := tokens source | return (source, "", [])
  let fields := rest.takeWhile fun token => token != "law" && token != "}"
  let tail := rest.drop fields.length
  let rec collect (fuel : Nat) (input : List String) : IO (List String × List String) := do
    match fuel, input with
    | _, "}" :: body => return ([], body)
    | n + 1, "law" :: rest =>
      let clause := rest.takeWhile (· != "}")
      let "}" :: remaining := rest.drop clause.length | fail "unterminated type law"
      let (laws, body) ← collect n remaining
      return (["law"] ++ clause ++ ["}"] ++ laws, body)
    | _, _ => fail "expected a type law or closing brace"
  let (lawTokens, body) ← collect tail.length tail
  if lawTokens.isEmpty then return (source, record, [])
  let laws ← parseDeclarations record lawTokens.length lawTokens
  return (String.intercalate " " (["type", record, "{"] ++ fields ++ ["}"] ++ body), record, laws)

private def resolve (dir : FilePath) (name : String) : IO (List Declaration) := do
  let segments := name.splitOn "."
  let mut candidates := []
  for scope in [segments, segments.dropLast] do
    if scope.isEmpty then continue
    let ns := String.intercalate "." scope
    let path := dir / (String.intercalate "/" scope ++ ".aethel")
    if ← path.pathExists then
      let lines := (sourceLines (← IO.FS.readFile path)).filter (!·.isEmpty)
      let first :: rest := lines | fail s!"empty law module {path}"
      unless tokens first == "namespace" :: tokens ns do fail s!"expected namespace {ns} in {path}"
      let ts := tokens (String.intercalate "\n" rest)
      let ds ← parseDeclarations ns ts.length ts
      if ns == name then candidates := candidates ++ [ds]
      else if let some d := ds.find? (·.name == name) then candidates := candidates ++ [[d]]
  match candidates with
  | [ds] => return ds
  | [] => fail s!"unknown law or namespace {name}"
  | _ => fail s!"ambiguous law or namespace {name}"

def load (path : FilePath) : IO Loaded := do
  let dir := path.parent.getD "."
  let (imports, uses, entry) ← header (sourceLines (← IO.FS.readFile path))
  let (ownerUses, owner, clientUses, client) ← match imports with
    | [] => pure (uses, entry, [], "")
    | [mod] => do
      let (nested, adopted, owner) ← header (sourceLines (← IO.FS.readFile (dir / (mod ++ ".aethel"))))
      unless nested.isEmpty do fail "nested program imports exceed the reference fragment"
      pure (adopted, owner, uses, entry)
    | _ => fail "the byte-record reference fragment supports one owner module"
  let (owner, recName, inlineLaws) ← stripTypeLaws owner
  let mut equalities := []
  for decl in inlineLaws do
    let some (target, x, y) := decl.equality | fail s!"unsupported type law {decl.name}"
    unless target == recName do fail s!"type law {decl.name} must bind {recName}"
    equalities := equalities ++ [(decl.name, x, y)]
  let mut props := []
  for (owned, selections) in [(true, ownerUses), (false, clientUses)] do
    for selection in selections do
      for decl in ← resolve dir selection do
        match decl.equality with
        | some (target, x, y) =>
          let eq := (decl.name, x, y)
          if target != recName || !owned then
            unless equalities.contains eq || props.contains decl do props := props ++ [decl]
            continue
          unless equalities.contains eq do
            equalities := equalities ++ [eq]
        | none => unless props.contains decl do props := props ++ [decl]
  return ⟨owner ++ "\n" ++ client, recName, equalities, props⟩

end Aethel.LawPackage
