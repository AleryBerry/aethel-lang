import Aethel.Tests
import Aethel.CoreTests
import Aethel.FunctionalTests
import Aethel.StructuredTests
import Aethel.AutomaticLayoutTests
import Aethel.PackedMIRTests
import Aethel.RecordRuntimeTests
import Aethel.FunctionSummariesTests
import Aethel.BorrowGraphTests
import Aethel.IterationTests
import Aethel.CoreASTTests
import Aethel.RepresentationTests
import Aethel.CoreSoundnessTests
import Aethel.Phase1Tests
import Aethel.Phase2Tests
import Aethel.Phase3Tests
import Aethel.Phase4Tests
import Aethel.Phase5And6Tests
import Aethel.Phase7Tests
import Aethel.Phase8Tests
import Aethel.IntInferenceTests
import Aethel.LitmusCorpus
import Aethel.SourceVerification
import Aethel.SourcePacked
import Aethel.RecordInvariant
import Aethel.LawPackage
import Aethel.SourceLaws
import Aethel.SourcePureLaws
import Aethel.SourceCollection
import Aethel.SourceRustCall

open Aethel
open Aethel.LitmusCorpus

private def usage :=
  "Usage: aethel-check [--self-test | --help | <file.mir> | --source <file.aethel> [--model <file.json>]
" ++
  "  | --emit-source-mir <file.aethel> | --source-mir <file.aethel> <file.mir> [--model <file.json>]\n" ++
  "  | --law-package <entry.aethel> | --source-law <file.aethel> <laws.aethel> | --packed-mir <file.json>\n" ++
  "  | --packed-source <file.aethel> | --emit-packed-mir <file.aethel>\n" ++
  "  | --packed-source-mir <file.aethel> <file.json>]"

private inductive ReferenceSource (input : String) where
  | record (verified : SourceVerification.Verified input)
  | pure (verified : SourceVerification.VerifiedPure input)
  | collection (verified : SourceVerification.VerifiedCollection input)
  | rust (verified : SourceVerification.VerifiedRustSource input)

private def checkReferenceSource (input : String) (candidate : Option String) :
    Except SourceVerification.Error (ReferenceSource input) := do
  match (SourceVerification.tokens input).head? with
  | some "@external" =>
    match candidate with
    | none => return .rust (← SourceVerification.verifyRustSource input)
    | some text => return .rust (← SourceVerification.verifyRustMIR input text).accepted
  | some "@layout" =>
    match candidate with
    | none => return .collection (← SourceVerification.verifyCollection input)
    | some text => return .collection (← SourceVerification.verifyCollectionMIR input text).accepted
  | some "fn" =>
    match candidate with
    | none => return .pure (← SourceVerification.verifyPure input)
    | some text => return .pure (← SourceVerification.verifyPureMIR input text).accepted
  | _ =>
    match candidate with
    | none => return .record (← SourceVerification.verify input)
    | some text => return .record (← SourceVerification.verifyMIR input text).accepted

private def ReferenceSource.emitMIR {input : String} : ReferenceSource input → String
  | .record verified => SourceVerification.encodeMIR verified.mir
  | .pure verified => SourceVerification.encodeCanonicalMIR verified.mir
  | .collection verified => SourceVerification.encodeCanonicalMIR verified.parsed.mir
  | .rust verified => SourceVerification.encodeCanonicalMIR verified.mir

private def observedByte (value : Option UInt8) : Except SourceVerification.Error String :=
  match value with
  | some byte => .ok (toString byte)
  | none => .error .coreStuck

private def ReferenceSource.observe {input : String} (modelText : Option String) :
    ReferenceSource input → Except SourceVerification.Error String
  | .record verified => observedByte (SourceVerification.execute verified)
  | .pure verified => return toString (← verified.run).value
  | .collection verified => observedByte verified.run
  | .rust verified => do
    let some text := modelText | throw .rustModelRequired
    let model ← (SourceVerification.decodeRustModels text).mapError .invalidRustModel
    let some byte := verified.run model | throw .rustTraceRejected
    return toString byte

private def checkSourceFile (path : String) (emit : Bool) (mirPath modelPath : Option String := none) : IO UInt32 := do
  let operation := if mirPath.isSome then "Source MIR verification" else "Source verification"
  try
    let input ← IO.FS.readFile path
    let candidate ← mirPath.mapM IO.FS.readFile
    match checkReferenceSource input candidate with
    | .error err =>
      IO.eprintln s!"{operation} failed: {repr err}"
      return 1
    | .ok verified =>
      if emit then
        IO.println verified.emitMIR
        return 0
      let models ← modelPath.mapM IO.FS.readFile
      match verified.observe models with
      | .error err =>
        IO.eprintln s!"{operation} failed: {repr err}"
        return 1
      | .ok value =>
        IO.println s!"Source verified (u8 result: {value})"
        return 0
  catch err =>
    IO.eprintln s!"{operation} failed: {err}"
    return 1

private def sourceLawBudget : Nat := 65536

private def checkRecordLaws {input : String} (accepted : SourceVerification.Verified input)
    (laws : String) : IO UInt32 := do
  match SourceVerification.checkReturnLaws accepted laws sourceLawBudget with
  | .error err =>
    IO.eprintln s!"Source law verification failed: {repr err}"
    return 1
  | .ok checked =>
    let mut exitCode := 0
    for report in checked.reports do
      let name := report.law.name
      match report.checked with
      | .error err =>
        IO.eprintln s!"Law {name} verification failed: {repr err}"
        exitCode := 1
      | .ok result =>
        match result.verdict with
        | .proved _ =>
          if result.emptyPremise then
            IO.println s!"Law {name} proved vacuously (no initialized input satisfies the guard)"
          else IO.println s!"Law {name} proved for all {256 ^ accepted.mir.fields.length} initialized inputs"
        | .falsified initial value _ _ _ _ =>
          let values := String.intercalate ", " (initial.map (toString ·.toNat))
          IO.eprintln s!"Law {name} is false on [{values}] with result {value}"
          exitCode := 1
    return exitCode

private def displayLawInput : CoreAST.CoreExpr → String
  | .unit => "()"
  | .bool value => toString value
  | .int false 8 value => s!"{value}u8"
  | .pair left right => s!"({displayLawInput left}, {displayLawInput right})"
  | .inject side _ payload =>
    let constructor := if side then "Ok" else "Err"
    s!"{constructor}({displayLawInput payload})"
  | expression => reprStr expression

private def checkPureLaws {input : String} (accepted : SourceVerification.VerifiedPure input)
    (laws : String) : IO UInt32 := do
  match SourceVerification.parsePureInputLaws laws with
  | .error err =>
    IO.eprintln s!"Source law verification failed: {repr err}"
    return 1
  | .ok parsed =>
    let mut exitCode := 0
    for law in parsed.declarations do
      match SourceVerification.bindPureLaw accepted law sourceLawBudget with
      | .error err =>
        IO.eprintln s!"Law {law.name} verification failed: {repr err}"
        exitCode := 1
      | .ok bound =>
        match bound.verdict with
        | .proved =>
          IO.println s!"Law {law.name} proved for all {bound.count} typed inputs"
        | .falsified code =>
          let witness := displayLawInput (bound.shape.decode code)
          IO.eprintln s!"Law {law.name} is false on {witness} with result {(bound.evaluate code).value}"
          exitCode := 1
    return exitCode

private def checkSourceLawFile (path lawPath : String) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let laws ← IO.FS.readFile lawPath
    match checkReferenceSource input none with
    | .error err =>
      IO.eprintln s!"Source verification failed: {repr err}"
      return 1
    | .ok (.record accepted) => checkRecordLaws accepted laws
    | .ok (.pure accepted) => checkPureLaws accepted laws
    | .ok (.collection _) | .ok (.rust _) =>
      IO.eprintln "Source law verification requires a pure module or a byte-record program"
      return 1
  catch err =>
    IO.eprintln s!"Source law verification failed: {err}"
    return 1

private def checkLawPackage (path : String) : IO UInt32 := do
  try
    let pkg ← LawPackage.load path
    let mut code := 0
    unless pkg.equalities.isEmpty do
      match RecordInvariant.checkProgram pkg.source pkg.record pkg.equalities with
      | .error err => IO.eprintln err; code := 1
      | .ok () =>
        for (name, _, _) in pkg.equalities do IO.println s!"Invariant {name} proved for every observed state"
    if pkg.propositions.isEmpty && pkg.equalities.isEmpty then
      IO.println "No laws checked"
    unless pkg.propositions.isEmpty do
      match checkReferenceSource pkg.source none with
      | .error err => IO.eprintln s!"Source verification failed: {repr err}"; return 1
      | .ok verified =>
        for decl in pkg.propositions do
          IO.println s!"Checking {decl.name}"
          let status ← match verified with
            | .record accepted => checkRecordLaws accepted decl.text
            | .pure accepted => checkPureLaws accepted decl.text
            | _ => IO.eprintln "Unsupported law target"; pure 1
          if status != 0 then code := 1
    return code
  catch err =>
    IO.eprintln s!"Law package verification failed: {err}"
    return 1

private def checkPackedMIRFile (path : String) : IO UInt32 := do
  try
    let contents ← IO.FS.readFile path
    match PackedMIR.parse contents with
    | .error err =>
      IO.eprintln s!"Invalid packed MIR: {err}"
      return 1
    | .ok mir =>
      match PackedMIR.validate mir with
      | .ok accepted =>
        IO.println s!"Packed MIR verified (v{mir.version}, bytes={mir.layout.byteCount}, observations={accepted.final.observations.reverse})"
        return 0
      | .error err =>
        IO.eprintln s!"Packed MIR verification failed: {err}"
        return 1
  catch err =>
    IO.eprintln s!"Failed to read '{path}': {err}"
    return 1

private def checkPackedSourceFile (path : String) (emit : Bool)
    (certificate : Option String := none) : IO UInt32 := do
  try
    let input ← IO.FS.readFile path
    let result ← match certificate with
      | none => pure (SourcePacked.verify input)
      | some candidate => do
        let text ← IO.FS.readFile candidate
        pure ((SourcePacked.verifyMIR input text).map SourcePacked.Matched.accepted)
    match result with
    | .error err =>
      IO.eprintln s!"Packed source verification failed: {repr err}"
      return 1
    | .ok proof =>
      if emit then
        IO.println (Lean.toJson proof.mir).compress
      else
        let some value := proof.result
          | IO.eprintln "Packed source returned no value"; return 1
        IO.println s!"Packed source verified ({proof.source.resultKind.spelling} result: {value}, bytes: {proof.mir.layout.byteCount})"
      return 0
  catch err =>
    IO.eprintln s!"Packed source verification failed: {err}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--self-test"] =>
    Tests.run
    Core.Tests.runTests
    Functional.Tests.run
    Functional.Tests.runSearch
    Structured.Tests.run
    Structured.Tests.runWideAndFacts
    AutomaticLayout.Tests.run
    AutomaticLayout.Tests.runCrossBoundary
    AutomaticLayout.Tests.runPackedNested
    AutomaticLayout.Tests.runPackedCodecs
    AutomaticLayout.Tests.runPackedRecordMachine
    PackedMIR.Tests.run
    AutomaticLayout.Tests.runAccess
    AutomaticLayout.Tests.runRecordRuntime
    AutomaticLayout.Tests.runCrossBoundaryPermissions
    AutomaticLayout.Tests.runSourceRecords
    AutomaticLayout.Tests.runInferredScopes
    AutomaticLayout.Tests.runScopeCoalescing
    FunctionSummaries.Tests.runFunctionSummaries
    BorrowGraph.Tests.runBorrowGraphTests
    Iteration.Tests.runIterationTests
    CoreAST.Tests.runCoreASTTests
    Representation.Tests.runRepresentationTests
    CoreSoundness.Tests.run
    Phase1.Tests.run
    Phase2.Tests.run
    Phase3.Tests.run
    Phase4.Tests.run
    Phase5And6.Tests.run
    Phase7.Tests.run
    Phase8.Tests.run
    IntInference.Tests.run
    runLitmusCorpus
    IO.println "Lean component checks passed. Full program checker and safety gate remain open."
    return 0
  | ["--help"] =>
    IO.println usage
    IO.println "Runs Lean foundation, layout, borrow, law, MIR validator, fork/join, Rust FFI, and 250 Lean litmus fixtures, or validates a versioned .mir file."
    IO.println "Use --source to check a reference byte record, indexed collection, or pure function program."
    IO.println "Supply a JSON adapter trace with --model when the reference program calls Rust."
    IO.println "Use --emit-source-mir to emit its operations, or --source-mir to compare it with supplied reference MIR."
    IO.println "Use --source-law to check byte-record return laws or finite pure predicates."
    IO.println "Use --packed-mir to validate a typed packed record and its byte-access trace."
    return 0
  | ["--source"] | ["--emit-source-mir"] | ["--source-mir"] | ["--source-mir", _] |
    ["--source-law"] | ["--source-law", _] | ["--packed-mir"] | ["--packed-source"] |
    ["--emit-packed-mir"] | ["--packed-source-mir"] | ["--packed-source-mir", _] =>
    IO.eprintln usage
    return 2
  | ["--source", path] => checkSourceFile path false
  | ["--source", path, "--model", model] => checkSourceFile path false none (some model)
  | ["--emit-source-mir", path] => checkSourceFile path true
  | ["--source-mir", path, mirPath] => checkSourceFile path false (some mirPath)
  | ["--source-mir", path, mirPath, "--model", model] => checkSourceFile path false (some mirPath) (some model)
  | ["--law-package", path] => checkLawPackage path
  | ["--source-law", path, lawPath] => checkSourceLawFile path lawPath
  | ["--packed-mir", path] => checkPackedMIRFile path
  | ["--packed-source", path] => checkPackedSourceFile path false
  | ["--emit-packed-mir", path] => checkPackedSourceFile path true
  | ["--packed-source-mir", path, certificate] => checkPackedSourceFile path false (some certificate)
  | [mirPath] =>
    try
      let contents ← IO.FS.readFile mirPath
      match Aethel.MIRValidator.validateMIRText contents with
      | .ok cert =>
        IO.println s!"MIR verified (v{cert.version}, records={cert.recordSizes.length}, functions={cert.functionCount}, laws={cert.lawCount})"
        return 0
      | .error err =>
        IO.eprintln s!"MIR verification failed: {err}"
        return 1
    catch err =>
      IO.eprintln s!"Failed to read '{mirPath}': {err}"
      return 1
  | _ =>
    IO.eprintln usage
    return 2
