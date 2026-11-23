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
import Aethel.IntInferenceTests
import Aethel.LitmusCorpus

open Aethel
open Aethel.LitmusCorpus

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
    IntInference.Tests.run
    runLitmusCorpus
    IO.println "Lean component checks passed. Full program checker and safety gate remain open."
    return 0
  | ["--help"] =>
    IO.println "Usage: aethel-check [--self-test | --help | <file.mir>]"
    IO.println "Runs Lean foundation, layout, borrow, law, MIR validator, fork/join, Rust FFI, and 250 litmus regressions, or validates a versioned .mir file."
    return 0
  | [mirPath] =>
    try
      let contents ← IO.FS.readFile mirPath
      match Aethel.MIRValidator.validateMIRText contents with
      | .ok cert =>
        IO.println s!"MIR verified (v{cert.version}, records={cert.recordSizes.length}, functions={cert.functionCount})"
        return 0
      | .error err =>
        IO.eprintln s!"MIR verification failed: {err}"
        return 1
    catch err =>
      IO.eprintln s!"Failed to read '{mirPath}': {err}"
      return 1
  | _ =>
    IO.eprintln "Usage: aethel-check [--self-test | --help | <file.mir>]"
    return 2
