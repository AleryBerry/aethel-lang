import Aethel.SourceVerification
import Aethel.LawFalsifier

namespace Aethel.SourceVerification

open Core Functional Structured

private inductive FitsDomains : List (List UInt8) → List UInt8 → Prop where
  | empty : FitsDomains [] []
  | cons : byte ∈ domain → FitsDomains domains bytes → FitsDomains (domain :: domains) (byte :: bytes)

private theorem FitsDomains.length {domains : List (List UInt8)} {bytes : List UInt8}
    (fits : FitsDomains domains bytes) : bytes.length = domains.length := by
  induction fits with
  | empty => rfl
  | cons _ _ same => exact congrArg Nat.succ same

private theorem FitsDomains.lookup {domains : List (List UInt8)} {bytes : List UInt8}
    (fits : FitsDomains domains bytes) {index : Nat} {domain : List UInt8} (slot : domains[index]? = some domain) :
    ∃ byte, bytes[index]? = some byte ∧ byte ∈ domain := by
  induction fits generalizing index with
  | empty => simp at slot
  | cons member _ ih =>
    cases index with
    | zero =>
      obtain rfl := Option.some.inj slot
      exact ⟨_, rfl, member⟩
    | succ index => exact ih slot

private theorem FitsDomains.from_lookup {domains : List (List UInt8)} {bytes : List UInt8}
    (size : bytes.length = domains.length)
    (access : ∀ (index : Nat) (domain : List UInt8), domains[index]? = some domain →
      ∃ byte, bytes[index]? = some byte ∧ byte ∈ domain) : FitsDomains domains bytes := by
  induction domains generalizing bytes with
  | nil => simp [List.length_eq_zero_iff] at size; subst bytes; exact .empty
  | cons domain rest ih =>
    cases bytes with
    | nil => simp at size
    | cons byte tail =>
      obtain ⟨found, equal, member⟩ := access 0 domain rfl
      obtain rfl := Option.some.inj equal
      exact .cons member (ih (Nat.succ.inj size) (fun index allowed slot =>
        access (index + 1) allowed slot))

/-- Enumerate initialized inputs one field at a time, with early exit on a
counterexample and without retaining the Cartesian product. -/
private def findRecordCounterexample (domains : List (List UInt8)) (test : List UInt8 → Bool) :
    Option (List UInt8) :=
  match domains with
  | [] => if test [] then none else some []
  | domain :: rest =>
    domain.findSome? fun byte =>
      (findRecordCounterexample rest fun tail => test (byte :: tail)).map (byte :: ·)

private theorem findRecordCounterexample_proved (domains : List (List UInt8)) (test : List UInt8 → Bool) :
    findRecordCounterexample domains test = none ↔
      ∀ bytes, FitsDomains domains bytes → test bytes = true := by
  induction domains generalizing test with
  | nil =>
    constructor
    · intro accepted _ fits
      cases fits
      cases verdict : test [] <;> simp [findRecordCounterexample, verdict] at accepted ⊢
    · intro all
      simp [findRecordCounterexample, all [] .empty]
  | cons domain rest ih =>
    simp only [findRecordCounterexample, List.findSome?_eq_none_iff, Option.map_eq_none_iff, ih]
    constructor
    · intro accepted bytes fits
      cases fits with
      | cons member tail => exact accepted _ member _ tail
    · intro accepted byte member rest fits
      exact accepted (byte :: rest) (.cons member fits)

private theorem findRecordCounterexample_falsified {domains : List (List UInt8)} {test : List UInt8 → Bool}
    {bytes : List UInt8} (found : findRecordCounterexample domains test = some bytes) :
    FitsDomains domains bytes ∧ test bytes = false := by
  induction domains generalizing test bytes with
  | nil =>
    cases result : test [] <;> simp [findRecordCounterexample, result] at found
    subst bytes
    exact ⟨.empty, result⟩
  | cons domain rest ih =>
    simp only [findRecordCounterexample] at found
    obtain ⟨byte, member, foundTail⟩ := List.exists_of_findSome?_eq_some found
    obtain ⟨tail, foundRest, rfl⟩ := Option.map_eq_some_iff.mp foundTail
    obtain ⟨fits, failed⟩ := ih foundRest
    exact ⟨.cons member fits, failed⟩

private def firstRecord (domains : List (List UInt8)) : Option (List UInt8) :=
  domains.mapM List.head?

private theorem firstRecord_sound {domains : List (List UInt8)} {bytes : List UInt8}
    (found : firstRecord domains = some bytes) : FitsDomains domains bytes := by
  induction domains generalizing bytes with
  | nil => cases found; exact .empty
  | cons domain rest ih =>
    cases domain with
    | nil => simp [firstRecord, bind] at found
    | cons first tail =>
      simp only [firstRecord, List.mapM_cons, List.head?_cons, bind, pure, Option.bind_eq_some_iff,
        Option.some.injEq] at found
      obtain ⟨_, rfl, suffix, foundRest, rfl⟩ := found
      exact .cons List.mem_cons_self (ih foundRest)

private theorem FitsDomains.firstRecord_exists {domains : List (List UInt8)} {bytes : List UInt8}
    (fits : FitsDomains domains bytes) : ∃ witness, firstRecord domains = some witness := by
  induction fits with
  | empty => exact ⟨[], rfl⟩
  | @cons domain byte domains bytes member _ ih =>
    obtain ⟨suffix, found⟩ := ih
    cases domain with
    | nil => cases member
    | cons first tail =>
      have tailChosen : domains.mapM List.head? = some suffix := found
      exact ⟨first :: suffix, by simp [firstRecord, tailChosen]⟩

structure BoundLawField (mir : SourceMIR) (parameter : String) (path : FieldPath) where
  index : Nat
  root : path.root = parameter
  declared : ∃ value, mir.fields[index]? = some (path.field, value)

private theorem BoundLawField.bounded {mir : SourceMIR} {parameter : String} {path : FieldPath}
    (resolved : BoundLawField mir parameter path) : resolved.index < mir.fields.length := by
  obtain ⟨_, found⟩ := resolved.declared
  exact (List.getElem?_eq_some_iff.mp found).choose

inductive BoundLawGuard (mir : SourceMIR) (parameter : String) : Option LawGuard → Type where
  | unguarded : BoundLawGuard mir parameter none
  | field {guard : LawGuard} (resolved : BoundLawField mir parameter guard.place) :
      BoundLawGuard mir parameter (some guard)

def BoundLawGuard.Premise {mir : SourceMIR} {parameter : String} {guard : Option LawGuard}
    (resolved : BoundLawGuard mir parameter guard) (initial : List UInt8) : Prop :=
  match resolved with
  | .unguarded => True
  | .field (guard := condition) resolved =>
    ∃ byte, initial[resolved.index]? = some byte ∧ condition.comparison.test byte condition.bound = true

private def BoundLawGuard.domainAt {mir : SourceMIR} {parameter : String} {guard : Option LawGuard}
    (resolved : BoundLawGuard mir parameter guard) (index : Nat) : List UInt8 :=
  match resolved with
  | .unguarded => LawFalsifier.u8Domain.elems
  | .field (guard := condition) guarded =>
    if index = guarded.index then
      LawFalsifier.u8Domain.elems.filter fun byte => condition.comparison.test byte condition.bound
    else LawFalsifier.u8Domain.elems

private def BoundLawGuard.domains {mir : SourceMIR} {parameter : String} {guard : Option LawGuard}
    (resolved : BoundLawGuard mir parameter guard) : List (List UInt8) :=
  (List.range mir.fields.length).map resolved.domainAt

private theorem BoundLawGuard.domain_at {mir : SourceMIR} {parameter : String} {guard : Option LawGuard}
    (resolved : BoundLawGuard mir parameter guard) {index : Nat} (bounded : index < mir.fields.length) :
    resolved.domains[index]? = some (resolved.domainAt index) := by
  simp [BoundLawGuard.domains, bounded]

private theorem BoundLawGuard.fits_domains {mir : SourceMIR} {parameter : String} {guard : Option LawGuard}
    (resolved : BoundLawGuard mir parameter guard) (initial : List UInt8) :
    FitsDomains resolved.domains initial ↔
      initial.length = mir.fields.length ∧ resolved.Premise initial := by
  constructor
  · intro fits
    refine ⟨by simpa [BoundLawGuard.domains] using fits.length, ?_⟩
    cases resolved with
    | unguarded => trivial
    | field resolved =>
      obtain ⟨byte, atIndex, admitted⟩ := fits.lookup ((BoundLawGuard.field resolved).domain_at resolved.bounded)
      exact ⟨byte, atIndex, by
        simpa [BoundLawGuard.domainAt, List.mem_filter, LawFalsifier.u8Domain.complete] using admitted⟩
  · rintro ⟨size, premise⟩
    apply FitsDomains.from_lookup (by simpa [BoundLawGuard.domains] using size)
    intro index domain found
    have bounded : index < mir.fields.length := by
      simpa [BoundLawGuard.domains] using (List.getElem?_eq_some_iff.mp found).choose
    have inInput : index < initial.length := size.symm ▸ bounded
    have same := Option.some.inj ((resolved.domain_at bounded).symm.trans found)
    subst domain
    refine ⟨initial[index], List.getElem?_eq_getElem inInput, ?_⟩
    cases resolved with
    | unguarded => exact LawFalsifier.u8Domain.complete _
    | field guarded =>
      by_cases guardedIndex : index = guarded.index
      · subst index
        obtain ⟨byte, atIndex, allowed⟩ := premise
        have equal := Option.some.inj ((List.getElem?_eq_getElem inInput).symm.trans atIndex)
        simp [BoundLawGuard.domainAt, List.mem_filter, LawFalsifier.u8Domain.complete, equal, allowed]
      · simpa [BoundLawGuard.domainAt, guardedIndex] using LawFalsifier.u8Domain.complete initial[index]

inductive BoundLawOperand (mir : SourceMIR) (parameter : String) : ByteOperand FieldPath → Type where
  | literal (value : UInt8) : BoundLawOperand mir parameter (.literal value)
  | field : BoundLawField mir parameter path → BoundLawOperand mir parameter (.place path)

def BoundLawOperand.Reads {mir : SourceMIR} {parameter : String} {operand : ByteOperand FieldPath}
    (resolved : BoundLawOperand mir parameter operand) (initial : List UInt8) (value : UInt8) : Prop :=
  match resolved with
  | .literal expected => value = expected
  | .field bound => initial[bound.index]? = some value

theorem BoundLawOperand.reads_initialized {mir : SourceMIR} {parameter : String}
    {operand : ByteOperand FieldPath} (resolved : BoundLawOperand mir parameter operand)
    (inputs : List UInt8) (size : inputs.length = mir.fields.length) :
    ∃ value, resolved.Reads inputs value := by
  cases resolved with
  | literal value => exact ⟨value, rfl⟩
  | field bound =>
    have inRange : bound.index < inputs.length := size.symm ▸ bound.bounded
    exact ⟨inputs[bound.index], List.getElem?_eq_getElem inRange⟩

private def BoundLawOperand.read {mir : SourceMIR} {parameter : String} {operand : ByteOperand FieldPath}
    (resolved : BoundLawOperand mir parameter operand) (initial : List UInt8) : Option UInt8 :=
  match resolved with
  | .literal value => some value
  | .field bound => initial[bound.index]?

private theorem BoundLawOperand.read_correct {mir : SourceMIR} {parameter : String} {operand : ByteOperand FieldPath}
    (resolved : BoundLawOperand mir parameter operand) (initial : List UInt8) (value : UInt8) :
    resolved.read initial = some value ↔ resolved.Reads initial value := by
  cases resolved <;> simp [BoundLawOperand.read, BoundLawOperand.Reads, eq_comm]

private theorem BoundLawOperand.constant_correct {mir : SourceMIR} {parameter : String} {operand : ByteOperand FieldPath}
    (resolved : BoundLawOperand mir parameter operand) {comparison : Comparison} {known : Bool}
    (constant : comparison.knownResult operand = some known) (expected : Bool)
    (initial : List UInt8) (value : UInt8) :
    (resolved.read initial).any (fun right => comparison.test value right == expected) = (known == expected) := by
  cases resolved with
  | literal bound => exact congrArg (· == expected) (Comparison.constantResult_sound constant value)
  | field bound => cases constant

structure BoundReturnLaw (mir : SourceMIR) where
  law : ReturnLaw
  callee : FunctionMIR
  offset : Nat
  recordMatches : law.record = mir.record
  calleeMatches : callee.name = law.helper
  declared : callee ∈ mir.functions
  returned : callee.result = .byte offset
  guard : BoundLawGuard mir law.parameter law.guard
  right : BoundLawOperand mir law.parameter law.bound

def BoundReturnLaw.Observes (bound : BoundReturnLaw mir) (initial : List UInt8) (value : UInt8) : Prop :=
  ∃ steps final, Structured.Executes Env.empty {} (bound.callee.code initial) steps final ∧
    final.views = [] ∧ final.observations.head? = some value

def BoundReturnLaw.Satisfies (bound : BoundReturnLaw mir) (initial : List UInt8) (result : UInt8) : Prop :=
  ∃ right, bound.right.Reads initial right ∧ bound.law.comparison.test result right = bound.law.expected

theorem BoundReturnLaw.violated_comparison (bound : BoundReturnLaw mir) (initial : List UInt8)
    (result : UInt8) (size : initial.length = mir.fields.length) (failed : ¬ bound.Satisfies initial result) :
    ∃ right, bound.right.Reads initial right ∧ bound.law.comparison.test result right ≠ bound.law.expected := by
  obtain ⟨right, read⟩ := bound.right.reads_initialized initial size
  exact ⟨right, read, fun passed => failed ⟨right, read, passed⟩⟩

def BoundReturnLaw.Holds (bound : BoundReturnLaw mir) : Prop :=
  ∀ initial, initial.length = mir.fields.length → bound.guard.Premise initial →
    ∃ value, bound.Observes initial value ∧ bound.Satisfies initial value

private def BoundReturnLaw.evaluate (bound : BoundReturnLaw mir) (initial : List UInt8) : Option UInt8 :=
  (bound.callee.run initial).bind fun state => state.observations.head?

private def BoundReturnLaw.checkOutput (bound : BoundReturnLaw mir) (initial : List UInt8) (result : UInt8) : Bool :=
  (bound.right.read initial).any fun right => bound.law.comparison.test result right == bound.law.expected

private theorem BoundReturnLaw.checkOutput_correct (bound : BoundReturnLaw mir) (initial : List UInt8)
    (result : UInt8) : bound.checkOutput initial result = true ↔ bound.Satisfies initial result := by
  simp only [BoundReturnLaw.checkOutput, BoundReturnLaw.Satisfies, Option.any_eq_true,
    BoundLawOperand.read_correct, beq_iff_eq]

private def BoundReturnLaw.test (bound : BoundReturnLaw mir) (initial : List UInt8) : Bool :=
  (bound.evaluate initial).any (bound.checkOutput initial)

private theorem BoundReturnLaw.Observes.evaluates {bound : BoundReturnLaw mir} {initial value}
    (observed : bound.Observes initial value) : bound.evaluate initial = some value := by
  obtain ⟨steps, final, executed, _, result⟩ := observed
  simp [BoundReturnLaw.evaluate, ← bound.callee.run_agrees, executed.agrees, result]

private theorem BoundReturnLaw.returns (bound : BoundReturnLaw mir) (checked : mir.check = true)
    (initial : List UInt8) (size : initial.length = mir.fields.length) :
    ∃ value, bound.Observes initial value := by
  obtain ⟨steps, final, executed, closed⟩ := SourceMIR.helpers_execute checked bound.callee bound.declared initial size
  obtain ⟨_, _, value, _, _, observed⟩ := bound.callee.result_observed bound.returned executed
  exact ⟨value, steps, final, executed, closed, observed⟩

inductive ReturnLawVerdict (bound : BoundReturnLaw mir) where
  | proved (holds : bound.Holds)
  | falsified (initial : List UInt8) (result : UInt8) (size : initial.length = mir.fields.length)
      (premise : bound.guard.Premise initial)
      (observed : bound.Observes initial result)
      (violated : ¬ bound.Satisfies initial result)

theorem ReturnLawVerdict.refutes {bound : BoundReturnLaw mir} {initial : List UInt8} {result : UInt8}
    (size : initial.length = mir.fields.length) (premise : bound.guard.Premise initial)
    (ran : bound.Observes initial result)
    (failed : ¬ bound.Satisfies initial result) :
    ¬ bound.Holds := by
  intro holds
  obtain ⟨value, observed, passed⟩ := holds initial size premise
  have same := Option.some.inj (ran.evaluates.symm.trans observed.evaluates)
  exact failed (same ▸ passed)

private def BoundReturnLaw.falsifiedAt (bound : BoundReturnLaw mir) (checked : mir.check = true)
    (initial : List UInt8) (fits : FitsDomains bound.guard.domains initial) (failed : bound.test initial = false) :
    ReturnLawVerdict bound :=
  let ⟨size, premise⟩ := (bound.guard.fits_domains initial).mp fits
  match evaluated : bound.evaluate initial with
  | none => False.elim (by
    obtain ⟨_, observed⟩ := bound.returns checked initial size
    have available := observed.evaluates
    simp [evaluated] at available)
  | some value => .falsified initial value size premise (by
    obtain ⟨observedValue, observed⟩ := bound.returns checked initial size
    have same := Option.some.inj (observed.evaluates.symm.trans evaluated)
    exact same ▸ observed) (by
    intro satisfied
    have passed := (bound.checkOutput_correct initial value).mpr satisfied
    simp [BoundReturnLaw.test, evaluated, passed] at failed)

private def BoundReturnLaw.constantVerdict (bound : BoundReturnLaw mir) (checked : mir.check = true)
    (initial : List UInt8) (fits : FitsDomains bound.guard.domains initial)
    {known : Bool} (proved : bound.law.comparison.knownResult bound.law.bound = some known) :
    ReturnLawVerdict bound :=
  if expected : known = bound.law.expected then .proved (by
    intro initial size _
    obtain ⟨value, observed⟩ := bound.returns checked initial size
    refine ⟨value, observed, (bound.checkOutput_correct initial value).mp ?_⟩
    rw [BoundReturnLaw.checkOutput, bound.right.constant_correct proved]
    exact beq_iff_eq.mpr expected)
  else
    bound.falsifiedAt checked initial fits (by
      cases evaluated : bound.evaluate initial with
      | none => simp [BoundReturnLaw.test, evaluated]
      | some value =>
        simp [BoundReturnLaw.test, evaluated, BoundReturnLaw.checkOutput,
          bound.right.constant_correct proved, expected])

private def verifyReturnLaw (bound : BoundReturnLaw mir) (checked : mir.check = true) :
    ReturnLawVerdict bound :=
  match found : findRecordCounterexample bound.guard.domains bound.test with
  | none => .proved (by
    have passed := (findRecordCounterexample_proved _ _).mp found
    intro initial size premise
    obtain ⟨value, observed⟩ := bound.returns checked initial size
    have accepted := passed initial ((bound.guard.fits_domains initial).mpr ⟨size, premise⟩)
    exact ⟨value, observed, (bound.checkOutput_correct initial value).mp (by
      simpa [BoundReturnLaw.test, observed.evaluates] using accepted)⟩)
  | some initial =>
    let failed := findRecordCounterexample_falsified found
    bound.falsifiedAt checked initial failed.1 failed.2

inductive ReturnLawError where
  | sourceLaw (error : Error)
  | wrongRecord (record : String)
  | unknownHelper (name : String)
  | expectedByteHelper (name : String)
  | budgetExceeded (inputs : Nat)
  deriving Repr

private def bindLawField {input : String} (accepted : Verified input) (parameter : String)
    (path : FieldPath) : Except ReturnLawError (BoundLawField accepted.mir parameter path) := do
  let bound ← (resolveField accepted.source parameter (accepted.source.fields.map Prod.fst) path).mapError .sourceLaw
  return ⟨bound.val, bound.property.1, by
    rw [accepted.lowers.initialBytes]
    exact bound.property.2.2⟩

private def bindLawGuard {input : String} (accepted : Verified input) (law : ReturnLaw) :
    Except ReturnLawError (BoundLawGuard accepted.mir law.parameter law.guard) :=
  match law.guard with
  | none => .ok .unguarded
  | some condition => return .field (← bindLawField accepted law.parameter condition.place)

private def bindLawOperand {input : String} (accepted : Verified input) (parameter : String) :
    (operand : ByteOperand FieldPath) → Except ReturnLawError (BoundLawOperand accepted.mir parameter operand)
  | .literal value => .ok (.literal value)
  | .place path => return .field (← bindLawField accepted parameter path)

private def bindReturnLaw {input : String} (accepted : Verified input) (law : ReturnLaw) :
    Except ReturnLawError {bound : BoundReturnLaw accepted.mir // bound.law = law} := do
  let mir := accepted.mir
  if record : law.record = mir.record then
    let named (candidate : FunctionMIR) := candidate.name == law.helper
    match found : mir.functions.find? named with
    | none => throw (.unknownHelper law.helper)
    | some callee =>
      match returned : callee.result with
      | .byte offset =>
        let guard ← bindLawGuard accepted law
        let right ← bindLawOperand accepted law.parameter law.bound
        have nameCheck : (callee.name == law.helper) = true :=
          List.find?_some (p := named) found
        return ⟨⟨law, callee, offset, record, beq_iff_eq.mp nameCheck,
          List.mem_of_find?_eq_some found, returned, guard, right⟩, rfl⟩
      | _ => throw (.expectedByteHelper law.helper)
  else throw (.wrongRecord law.record)

structure CheckedReturnLaw (mir : SourceMIR) (law : ReturnLaw) where
  bound : BoundReturnLaw mir
  declaration : bound.law = law
  verdict : ReturnLawVerdict bound

def CheckedReturnLaw.emptyPremise (result : CheckedReturnLaw mir law) : Bool :=
  result.bound.guard.domains.any List.isEmpty

private def checkReturnLaw {input : String} (accepted : Verified input) (budget : Nat) (law : ReturnLaw) :
    Except ReturnLawError (CheckedReturnLaw accepted.mir law) := do
  let bound ← bindReturnLaw accepted law
  let verdict ← match sampled : firstRecord bound.val.guard.domains with
    | none => pure (.proved (by
      intro initial size premise
      have fits := (bound.val.guard.fits_domains initial).mpr ⟨size, premise⟩
      obtain ⟨_, available⟩ := fits.firstRecord_exists
      simp [sampled] at available))
    | some initial =>
      match constant : bound.val.law.comparison.knownResult bound.val.law.bound with
      | some _ => pure (bound.val.constantVerdict accepted.checked initial (firstRecord_sound sampled) constant)
      | none =>
        let inputs := bound.val.guard.domains.foldl (fun count domain => count * domain.length) 1
        if inputs > budget then throw (.budgetExceeded inputs)
        else pure (verifyReturnLaw bound.val accepted.checked)
  return ⟨bound.val, bound.property, verdict⟩

structure ReturnLawReport (mir : SourceMIR) where
  law : ReturnLaw
  checked : Except ReturnLawError (CheckedReturnLaw mir law)

structure CheckedReturnLaws (mir : SourceMIR) (text : String) where
  reports : List (ReturnLawReport mir)
  spelled : tokens text = reports.flatMap (fun report => report.law.tokens)

def checkReturnLaws {input : String} (accepted : Verified input) (text : String) (budget : Nat) :
    Except ReturnLawError (CheckedReturnLaws accepted.mir text) := do
  let parsed ← (parseReturnLaws text).mapError .sourceLaw
  let reports := parsed.declarations.map fun law => ⟨law, checkReturnLaw accepted budget law⟩
  return ⟨reports, by simpa [reports, List.flatMap_map] using parsed.spelled⟩

end Aethel.SourceVerification
