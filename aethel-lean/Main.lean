import Aethel.Tests
import Aethel.CoreTests
import Aethel.FunctionalTests
import Aethel.StructuredTests
import Aethel.AutomaticLayoutTests
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
import Aethel.SourceLaws
import Aethel.SourcePure

open Aethel
open Aethel.LitmusCorpus

private def usage :=
  "Usage: aethel-check [--self-test | --help | <file.mir> | --source <file.aethel>
" ++
  "  | --emit-source-mir <file.aethel> | --source-mir <file.aethel> <file.mir>\n" ++
  "  | --source-law <file.aethel> <laws.aethel>]"

private inductive ReferenceSource (input : String) where
  | record (verified : SourceVerification.Verified input)
  | pure (verified : SourceVerification.VerifiedPure input)

private def checkReferenceSource (input : String) (candidate : Option String) :
    Except SourceVerification.Error (ReferenceSource input) := do
  if (SourceVerification.tokens input).head? = some "fn" then
    match candidate with
    | none => return .pure (← SourceVerification.verifyPure input)
    | some text => return .pure (← SourceVerification.verifyPureMIR input text).accepted
  else
    match candidate with
    | none => return .record (← SourceVerification.verify input)
    | some text => return .record (← SourceVerification.verifyMIR input text).accepted

private def ReferenceSource.emitMIR {input : String} : ReferenceSource input → String
  | .record verified => SourceVerification.encodeMIR verified.mir
  | .pure verified => SourceVerification.encodeCanonicalMIR verified.mir

private def ReferenceSource.observe {input : String} :
    ReferenceSource input → Except SourceVerification.Error String
  | .record verified =>
    match SourceVerification.execute verified with
    | some value => .ok (toString value)
    | none => .error .coreStuck
  | .pure verified => return toString (← verified.run).value

private def checkSourceFile (path : String) (emit : Bool) (mirPath : Option String := none) : IO UInt32 := do
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
      match verified.observe with
      | .error err =>
        IO.eprintln s!"{operation} failed: {repr err}"
        return 1
      | .ok value =>
        IO.println s!"Source verified (u8 result: {value})"
        return 0
  catch err =>
    IO.eprintln s!"{operation} failed: {err}"
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
    AutomaticLayout.Tests.runAccess
    AutomaticLayout.Tests.runRecordRuntime
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
    IO.println "Use --source to check a reference byte-record or pure function program."
    IO.println "Use --emit-source-mir to emit its operations, or --source-mir to compare it with supplied reference MIR."
    IO.println "Use --source-law to check return laws over initialized byte-record inputs."
    return 0
  | ["--source"] | ["--emit-source-mir"] | ["--source-mir"] | ["--source-mir", _] |
    ["--source-law"] | ["--source-law", _] =>
    IO.eprintln usage
    return 2
  | ["--source", path] => checkSourceFile path false
  | ["--emit-source-mir", path] => checkSourceFile path true
  | ["--source-mir", path, mirPath] => checkSourceFile path false (some mirPath)
  | ["--source-law", path, lawPath] =>
    try
      let input ← IO.FS.readFile path
      let laws ← IO.FS.readFile lawPath
      match SourceVerification.verify input with
      | .error err =>
        IO.eprintln s!"Source verification failed: {repr err}"
        return 1
      | .ok accepted =>
        match SourceVerification.checkReturnLaws accepted laws 65536 with
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
                IO.println s!"Law {name} proved for all {256 ^ accepted.mir.fields.length} initialized inputs"
              | .falsified initial value _ _ _ _ =>
                let values := String.intercalate ", " (initial.map (toString ·.toNat))
                IO.eprintln s!"Law {name} is false on [{values}] with result {value}"
                exitCode := 1
          return exitCode
    catch err =>
      IO.eprintln s!"Source law verification failed: {err}"
      return 1
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
