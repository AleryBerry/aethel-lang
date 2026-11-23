import Aethel
import Aethel.CoreAST
import Aethel.CoreSemantics
import Aethel.Representation
import Aethel.CoreSoundnessFull

namespace Aethel.Litmus

open Functional Core Structured CoreAST CoreSemantics CoreSoundness

inductive Domain where
  | aliasingScopes
  | invalidationFacts
  | branchJoins
  | ownershipTransfer
  | returnedOrigins
  | closuresCaptures
  | layoutPacking
  | adtMatching
  | iterationTermination
  deriving Repr, DecidableEq

inductive Verdict where
  | accept
  | rejectTypeMismatch
  | rejectBorrowConflict
  | rejectStaleFact
  | rejectEscapedView
  | rejectEscapedClosure
  | rejectLayoutMismatch
  | rejectIncompletePattern
  | rejectNonterminating
  deriving Repr, DecidableEq

structure Fixture where
  name : String
  domain : Domain
  isPositive : Bool
  expected : Verdict
  check : Bool
  description : String

def Fixture.passed (f : Fixture) : Bool := f.check

end Aethel.Litmus
