import Aethel.SourcePure
import Aethel.Representation
import Aethel.LawFalsifier

namespace Aethel.SourceVerification

open CoreAST CoreSemantics LawFalsifier Representation

structure PureInputLaw where
  name : String
  parameter : String
  domain : CoreType
  predicate : String
  expected : Bool

def PureInputLaw.tokens (law : PureInputLaw) : Tokens :=
  ["law", law.name, "(", law.parameter, ":"] ++ typeTokens law.domain ++
    [")", "{", lawExpectationToken law.expected, law.predicate, "(", law.parameter, ")", "}"]

private def parsePureInputLaw (input : Tokens) : Except Error (PureInputLaw × Tokens) := do
  let (name, rest) ← readName false (← expect ["law"] input)
  let (parameter, rest) ← readName false (← expect ["("] rest)
  let (domain, rest) ← parsePureType rest.length (← expect [":"] rest)
  let (expected, rest) ← parseLawExpectation (← expect [")", "{"] rest)
  let (predicate, rest) ← readName false rest
  let rest ← expect ["(", parameter, ")", "}"] rest
  return (⟨name, parameter, domain, predicate, expected⟩, rest)

def parsePureInputLaws := parseLaws parsePureInputLaw PureInputLaw.tokens

inductive PureLawError where
  | source (error : Error)
  | unsupportedDomain (domain : CoreType)
  | budgetExceeded (inputs : Nat)
  deriving Repr

structure BoundPureLaw {input : String} (verified : VerifiedPure input) (law : PureInputLaw) where
  selected : VerifiedPureDefinition verified law.predicate (.arrow law.domain .bool .empty)
  count : Nat
  shape : DenseData law.domain count
  closure : CoreExpr
  prepared : Reduces {} selected.expression closure
  callable : Computable (.arrow law.domain .bool .empty) closure

def bindPureLaw {input : String} (verified : VerifiedPure input) (law : PureInputLaw) (budget : Nat) :
    Except PureLawError (BoundPureLaw verified law) := do
  let some ⟨count, shape⟩ := DenseData.ofType law.domain | throw (.unsupportedDomain law.domain)
  if count > budget then throw (.budgetExceeded count)
  let selected ← (verified.definition law.predicate (.arrow law.domain .bool .empty)).mapError .source
  let terminates := selected.terminates
  return ⟨selected, count, shape, terminates.normalForm,
    terminates.normalForm_correct.1, terminates.normalForm_correct.2⟩

/-- The declared predicate reduces to the required Boolean for every closed source value of the domain. -/
def BoundPureLaw.Holds {verified : VerifiedPure input} {law : PureInputLaw}
    (bound : BoundPureLaw verified law) : Prop :=
  ∀ value, Value value → WellTyped [] value law.domain .empty →
    Reduces {} (.app bound.selected.expression value) (.bool law.expected)

def BoundPureLaw.evaluate {verified : VerifiedPure input} {law : PureInputLaw}
    (bound : BoundPureLaw verified law) (code : Fin bound.count) :
    BooleanEvaluation (.app bound.selected.expression (bound.shape.decode code)) :=
  let computed := (bound.callable.applies (bound.shape.decoded_computable code)).evalBool
  let prepared := bound.prepared.under (.app · (bound.shape.decode code)) Step.app_fn
  ⟨computed.value, prepared.append computed.ran⟩

private def BoundPureLaw.test {verified : VerifiedPure input} {law : PureInputLaw}
    (bound : BoundPureLaw verified law) (code : Fin bound.count) : Bool :=
  (bound.evaluate code).value == law.expected

def BoundPureLaw.verdict {verified : VerifiedPure input} {law : PureInputLaw}
    (bound : BoundPureLaw verified law) : LawVerdict (Fin bound.count) :=
  verifyExhaustive (finDomain bound.count) bound.test

theorem BoundPureLaw.proved_iff {verified : VerifiedPure input} {law : PureInputLaw}
    (bound : BoundPureLaw verified law) : bound.verdict = .proved ↔ bound.Holds := by
  rw [verdict, verifyExhaustive_proved_iff]
  constructor
  · intro all value ready typed
    obtain ⟨code, encoded⟩ := bound.shape.encode_total ready typed
    have same := (bound.shape.encode_correct).mp encoded
    have expected : (bound.evaluate code).value = law.expected := beq_iff_eq.mp (all code)
    exact same ▸ expected ▸ (bound.evaluate code).ran
  · intro holds code
    have values := bound.shape.decoded_value code
    have required := holds _ values.1 values.2
    have same := (bound.evaluate code).ran.final_unique required (.bool _) (.bool _)
    exact beq_iff_eq.mpr (CoreExpr.bool.inj same)

theorem BoundPureLaw.falsified_sound {verified : VerifiedPure input} {law : PureInputLaw}
    (bound : BoundPureLaw verified law) {code : Fin bound.count} (found : bound.verdict = .falsified code) :
    Value (bound.shape.decode code) ∧ WellTyped [] (bound.shape.decode code) law.domain .empty ∧
      Reduces {} (.app bound.selected.expression (bound.shape.decode code))
        (.bool (bound.evaluate code).value) ∧
      (bound.evaluate code).value ≠ law.expected ∧ ¬ bound.Holds := by
  have failure := (verifyExhaustive_falsified_sound found).1
  have different : (bound.evaluate code).value ≠ law.expected := by
    intro same
    have passed : bound.test code = true := beq_iff_eq.mpr same
    rw [passed] at failure
    cases failure
  have values := bound.shape.decoded_value code
  exact ⟨values.1, values.2, (bound.evaluate code).ran, different, fun holds => by
    rw [(bound.proved_iff.mpr holds)] at found
    cases found⟩

end Aethel.SourceVerification
