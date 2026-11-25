import Aethel.BranchFacts
import Aethel.ResourceLiveness

namespace Aethel.Structured

open Functional Core

inductive AccessTarget where
  | handle (id : HandleId)
  | view (id : ViewId)
  deriving Repr, DecidableEq

def AccessTarget.writeInstruction : AccessTarget → UInt8 → Instruction
  | .handle id, value => .write id value
  | .view id, value => .writeView id value

def AccessTarget.readInstruction : AccessTarget → Instruction
  | .handle id => .read id
  | .view id => .readView id

/-- A read contributes one observation to the byte machine and returns that
same byte to the structured evaluator. -/
def AccessTarget.readValue (target : AccessTarget) (state : State) : Option (UInt8 × State) := do
  let next ← execute state target.readInstruction
  let value ← next.observations.head?
  return (value, next)

theorem AccessTarget.read_observes {target : AccessTarget} {state next : State}
    (step : Step state target.readInstruction next) :
    ∃ value, next = state.observe value := by
  cases target <;> cases step <;> exact ⟨_, rfl⟩

theorem AccessTarget.read_correct (target : AccessTarget) (state : State)
    (value : UInt8) (next : State) :
    target.readValue state = some (value, next) ↔
      Step state target.readInstruction next ∧ next = state.observe value := by
  simp only [AccessTarget.readValue, bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ran, _, first, rfl, rfl⟩
    have step := execute_sound ran
    obtain ⟨observed, same⟩ := target.read_observes step
    exact ⟨step, same.trans (congrArg state.observe (by simpa [same, State.observe] using first))⟩
  · rintro ⟨step, rfl⟩
    exact ⟨_, execute_complete step, value, rfl, rfl, rfl⟩

def AccessTarget.location (target : AccessTarget) (state : State) : Option ByteLocation :=
  match target with
  | .handle id => (state.handle id).map Handle.location
  | .view id => (state.view id).map View.location

theorem AccessTarget.location_resources (target : AccessTarget) (state : State) :
    target.location state.resources.authorityState = target.location state := by
  cases target <;> rfl

/-- Permission and liveness checks precede observation. A successful read
returns the byte at the target in the state immediately before the read. -/
theorem AccessTarget.read_current_byte {target : AccessTarget} {state next : State} {value : UInt8}
    (read : target.readValue state = some (value, next)) :
    (target.location state).bind state.byte = some value := by
  obtain ⟨step, observed⟩ := (target.read_correct state value next).mp read
  cases target <;> cases step <;> simp_all [AccessTarget.location, State.observe]

theorem read_pair_current_bytes {low high : AccessTarget} {state middle next : State}
    {lo hi : UInt8} (first : low.readValue state = some (lo, middle))
    (second : high.readValue middle = some (hi, next)) :
    (low.location state).bind state.byte = some lo ∧
      (high.location state).bind state.byte = some hi := by
  have observed := ((low.read_correct state lo middle).mp first).2
  refine ⟨AccessTarget.read_current_byte first, ?_⟩
  rw [observed] at second
  have loaded := AccessTarget.read_current_byte second
  exact loaded

def Adjacent (state : State) (low high : AccessTarget) : Prop :=
  match low.location state, high.location state with
  | some first, some second =>
    first.allocation = second.allocation ∧ first.offset + 1 = second.offset
  | _, _ => False

def checkAdjacent (state : ResourceState) (low high : AccessTarget) : Bool :=
  match low.location state.authorityState, high.location state.authorityState with
  | some first, some second =>
    decide (first.allocation = second.allocation ∧ first.offset + 1 = second.offset)
  | _, _ => false

theorem checkAdjacent_correct (state : State) (low high : AccessTarget) :
    checkAdjacent state.resources low high = true ↔ Adjacent state low high := by
  simp only [checkAdjacent, Adjacent, AccessTarget.location_resources]
  cases low.location state <;> cases high.location state <;> simp

theorem AccessTarget.check_value (target : AccessTarget) (state : ResourceState) (a b : UInt8) :
    checkInstruction state (target.writeInstruction a) = checkInstruction state (target.writeInstruction b) := by
  cases target <;> rfl

/-- Conditionals carry the remainder of the program in each branch. Each arm
can reach a different final heap, but all terminal paths must close views. -/
inductive Code : List Ty → Type where
  | finish : Code ctx
  | instruction : Instruction → Code ctx → Code ctx
  | read : AccessTarget → Code (.byte :: ctx) → Code ctx
  | readUInt16LE : AccessTarget → AccessTarget → Code (.uint16 :: ctx) → Code ctx
  | write : AccessTarget → Term ctx .byte → Code ctx → Code ctx
  | writeUInt16LE : AccessTarget → AccessTarget → Term ctx .uint16 → Code ctx → Code ctx
  | requireLocation : AccessTarget → ByteLocation → Code ctx → Code ctx
  | letValue : Term ctx ty → Code (ty :: ctx) → Code ctx
  | branch : Term ctx .bool → Code ctx → Code ctx → Code ctx
  | selectByte : Term ctx .byte → (Fin 256 → Code ctx) → Code ctx

inductive RawCode where
  | finish
  | instruction (instruction : Instruction) (next : RawCode)
  | read (target : AccessTarget) (body : RawCode)
  | readUInt16LE (low high : AccessTarget) (body : RawCode)
  | write (target : AccessTarget) (value : Raw) (next : RawCode)
  | writeUInt16LE (low high : AccessTarget) (value : Raw) (next : RawCode)
  | letValue (value : Raw) (body : RawCode)
  | branch (condition : Raw) (yes no : RawCode)
  deriving Repr

def elaborateAs (ctx : List Ty) (expected : Ty) (source : Raw) :
    Except TypeError (Term ctx expected) := do
  let inferred ← Functional.elaborate ctx source
  if same : inferred.ty = expected then
    return same ▸ inferred.term
  else .error (.expected expected inferred.ty)

def elaborate (ctx : List Ty) : RawCode → Except TypeError (Code ctx)
  | .finish => .ok .finish
  | .instruction instruction next => return .instruction instruction (← elaborate ctx next)
  | .read target body => return .read target (← elaborate (.byte :: ctx) body)
  | .readUInt16LE low high body =>
    return .readUInt16LE low high (← elaborate (.uint16 :: ctx) body)
  | .write target value next =>
    return .write target (← elaborateAs ctx .byte value) (← elaborate ctx next)
  | .writeUInt16LE low high value next =>
    return .writeUInt16LE low high (← elaborateAs ctx .uint16 value) (← elaborate ctx next)
  | .letValue value body => do
    let inferred ← Functional.elaborate ctx value
    return .letValue inferred.term (← elaborate (inferred.ty :: ctx) body)
  | .branch condition yes no =>
    return .branch (← elaborateAs ctx .bool condition) (← elaborate ctx yes) (← elaborate ctx no)

/-- Check both arms of an unknown guard. A proved fact can discard its
infeasible arm. Heap contents are never available to this checker. -/
def checkWithFacts (state : ResourceState) (facts : BranchFacts ctx) : Code ctx → Bool
  | .finish => state.views.isEmpty
  | .instruction instruction next =>
    (checkInstruction state instruction).any fun s => checkWithFacts s facts next
  | .read target body =>
    (checkInstruction state target.readInstruction).any fun s =>
      checkWithFacts s (facts.underBinder .byte) body
  | .readUInt16LE low high body =>
    checkAdjacent state low high && ((checkInstruction state low.readInstruction).any fun middle =>
      (checkInstruction middle high.readInstruction).any fun next =>
        checkWithFacts next (facts.underBinder .uint16) body)
  | .write target _ next =>
    (checkInstruction state (target.writeInstruction 0)).any fun s => checkWithFacts s facts next
  | .writeUInt16LE low high _ next =>
    checkAdjacent state low high &&
      ((checkInstruction state (low.writeInstruction 0)).any fun middle =>
        (checkInstruction middle (high.writeInstruction 0)).any fun s =>
          checkWithFacts s facts next)
  | .requireLocation target location next =>
    decide (target.location state.authorityState = some location) && checkWithFacts state facts next
  | .letValue (ty := ty) _ body => checkWithFacts state (facts.underBinder ty) body
  | .branch condition yes no =>
    facts.checkArms condition (fun known => checkWithFacts state known yes)
      (fun known => checkWithFacts state known no)
  | .selectByte _ arms =>
    (List.finRange 256).all fun i => checkWithFacts state facts (arms i)

def check (state : ResourceState) (code : Code ctx) : Bool :=
  checkWithFacts state [] code

/-- Execute heap instructions in order. The trace records the resource
operations selected by values computed during execution. -/
def runCode (env : Env ctx) (state : State) : Code ctx → Option (Program × State)
  | .finish => some ([], state)
  | .instruction instruction next => do
    let middle ← execute state instruction
    let (steps, final) ← runCode env middle next
    return (instruction :: steps, final)
  | .read target body => do
    let (value, middle) ← target.readValue state
    let (steps, final) ← runCode (env.extend (ty := .byte) value) middle body
    return (target.readInstruction :: steps, final)
  | .readUInt16LE low high body => do
    if !checkAdjacent state.resources low high then none else do
      let (lowByte, middle) ← low.readValue state
      let (highByte, next) ← high.readValue middle
      let (steps, final) ← runCode (env.extend (ty := .uint16) (decodeUInt16LE lowByte highByte)) next body
      return (low.readInstruction :: high.readInstruction :: steps, final)
  | .write target value next => do
    let instruction := target.writeInstruction (value.eval env)
    let middle ← execute state instruction
    let (steps, final) ← runCode env middle next
    return (instruction :: steps, final)
  | .writeUInt16LE low high value next => do
    if !checkAdjacent state.resources low high then none else do
      let word := value.eval env
      let lowInstruction := low.writeInstruction (splitLow word)
      let middle ← execute state lowInstruction
      let highInstruction := high.writeInstruction (splitHigh word)
      let stepHigh ← execute middle highInstruction
      let (steps, final) ← runCode env stepHigh next
      return (lowInstruction :: highInstruction :: steps, final)
  | .requireLocation target location next =>
    if target.location state = some location then runCode env state next else none
  | .letValue value body => runCode (env.extend (value.eval env)) state body
  | .branch condition yes no =>
    if (show Bool from condition.eval env) then runCode env state yes else runCode env state no
  | .selectByte value arms => runCode env state (arms (value.eval env : UInt8).toFin)

/-- Declarative execution. The read rule uses the byte machine's observed
value to extend the local environment. -/
inductive Executes : Env ctx → State → Code ctx → Program → State → Prop where
  | finish : Executes env state .finish [] state
  | instruction : Step state instruction middle → Executes env middle next steps final →
      Executes env state (.instruction instruction next) (instruction :: steps) final
  | read : Step state target.readInstruction middle → middle = state.observe value →
      Executes (env.extend (ty := .byte) value) middle body steps final →
      Executes env state (.read target body) (target.readInstruction :: steps) final
  | readUInt16LE : Adjacent state low high →
      Step state low.readInstruction middle → middle = state.observe lo →
      Step middle high.readInstruction next → next = middle.observe hi →
      Executes (env.extend (ty := .uint16) (decodeUInt16LE lo hi)) next body steps final →
      Executes env state (.readUInt16LE low high body)
        (low.readInstruction :: high.readInstruction :: steps) final
  | write : Evaluates env term value → Step state (target.writeInstruction value) middle →
      Executes env middle next steps final →
      Executes env state (.write target term next) (target.writeInstruction value :: steps) final
  | writeUInt16LE : Adjacent state low high →
      Evaluates env term word →
      Step state (low.writeInstruction (splitLow word)) middle →
      Step middle (high.writeInstruction (splitHigh word)) next →
      Executes env next rest steps final →
      Executes env state (.writeUInt16LE low high term rest)
        (low.writeInstruction (splitLow word) :: high.writeInstruction (splitHigh word) :: steps) final
  | requireLocation : target.location state = some location → Executes env state next steps final →
      Executes env state (.requireLocation target location next) steps final
  | letValue : Evaluates env term value → Executes (env.extend value) state body steps final →
      Executes env state (.letValue term body) steps final
  | branchTrue : Evaluates env condition true → Executes env state yes steps final →
      Executes env state (.branch condition yes no) steps final
  | branchFalse : Evaluates env condition false → Executes env state no steps final →
      Executes env state (.branch condition yes no) steps final
  | selectByte : Evaluates env term value → Executes env state (arms value.toFin) steps final →
      Executes env state (.selectByte term arms) steps final

inductive CheckError where
  | illTyped (error : TypeError)
  | invalidResources
  deriving Repr, DecidableEq

def verify (source : RawCode) : Except CheckError (Code []) := do
  let code ← (elaborate [] source).mapError .illTyped
  if check {} code then .ok code else .error .invalidResources

def executeClosed (source : RawCode) : Except CheckError (Option State) := do
  let code ← verify source
  return (runCode Env.empty {} code).map Prod.snd

theorem verify_checked {source : RawCode} {code : Code []}
    (accepted : verify source = .ok code) : check {} code = true := by
  cases h : elaborate [] source <;> simp [verify, h, Except.mapError, bind, Except.bind] at accepted
  split at accepted <;> simp_all

theorem Executes.trace {env : Env ctx} {state final : State} {code : Code ctx} {steps : Program}
    (execution : Executes env state code steps final) : Runs state steps final := by
  induction execution with
  | finish => exact .nil
  | instruction first _ ih => exact .cons first ih
  | read first _ _ ih => exact .cons first ih
  | readUInt16LE _ first _ second _ _ ih => exact .cons first (.cons second ih)
  | write _ first _ ih => exact .cons first ih
  | writeUInt16LE _ _ first second _ ih => exact .cons first (.cons second ih)
  | requireLocation _ _ ih | letValue _ _ ih | branchTrue _ _ ih | branchFalse _ _ ih | selectByte _ _ ih =>
    exact ih

theorem Executes.agrees {env : Env ctx} {state final : State} {code : Code ctx} {steps : Program}
    (execution : Executes env state code steps final) :
    runCode env state code = some (steps, final) := by
  induction execution with
  | finish => rfl
  | instruction first _ ih => simp [runCode, execute_complete first, ih, bind, pure]
  | read first observed remaining ih =>
    rename_i target
    simp [runCode, (target.read_correct _ _ _).mpr ⟨first, observed⟩, ih, bind, pure]
  | readUInt16LE adjacent first lowObserved second highObserved rest ih =>
    rename_i low high middle lo next hi body steps final env
    simp [runCode, (checkAdjacent_correct _ _ _).mpr adjacent,
      (low.read_correct _ _ _).mpr ⟨first, lowObserved⟩,
      (high.read_correct _ _ _).mpr ⟨second, highObserved⟩, ih, bind, pure]
  | write evaluated first _ ih =>
    simp [runCode, evaluated.agrees, execute_complete first, ih, bind, pure]
  | writeUInt16LE adjacent evaluated first second _ ih =>
    simp [runCode, (checkAdjacent_correct _ _ _).mpr adjacent, evaluated.agrees,
      execute_complete first, execute_complete second, ih, bind, pure]
  | requireLocation located _ ih => simp [runCode, located, ih]
  | letValue evaluated _ ih => simp [runCode, evaluated.agrees, ih]
  | branchTrue evaluated _ ih | branchFalse evaluated _ ih | selectByte evaluated _ ih =>
    simp [runCode, evaluated.agrees, ih]

theorem runCode_sound {env : Env ctx} {state final : State} {code : Code ctx} {steps : Program}
    (ran : runCode env state code = some (steps, final)) :
    Executes env state code steps final := by
  induction code generalizing state steps final with
  | finish =>
    cases ran
    exact .finish
  | instruction instruction next ih =>
    simp only [runCode, bind, pure, Option.bind_eq_some_iff, Prod.exists, Option.some.injEq,
      Prod.mk.injEq] at ran
    obtain ⟨middle, first, rest, _, remaining, rfl, rfl⟩ := ran
    exact .instruction (execute_sound first) (ih remaining)
  | read target body ih =>
    simp only [runCode, bind, pure, Option.bind_eq_some_iff, Prod.exists, Option.some.injEq,
      Prod.mk.injEq] at ran
    obtain ⟨value, middle, first, rest, _, remaining, rfl, rfl⟩ := ran
    obtain ⟨step, observed⟩ := (target.read_correct state value middle).mp first
    exact .read step observed (ih remaining)
  | readUInt16LE low high body ih =>
    by_cases adjacent : checkAdjacent state.resources low high = true
    · simp only [runCode, adjacent, Bool.not_true, Bool.false_eq_true, ite_false, bind, pure,
        Option.bind_eq_some_iff, Prod.exists, Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨lo, middle, first, hi, next, second, rest, _, remaining, rfl, rfl⟩ := ran
      obtain ⟨first, lowObserved⟩ := (low.read_correct state lo middle).mp first
      obtain ⟨second, highObserved⟩ := (high.read_correct middle hi next).mp second
      exact .readUInt16LE ((checkAdjacent_correct _ _ _).mp adjacent) first lowObserved
        second highObserved (ih remaining)
    · simp [runCode, adjacent] at ran
  | write target value next ih =>
    simp only [runCode, bind, pure, Option.bind_eq_some_iff, Prod.exists, Option.some.injEq,
      Prod.mk.injEq] at ran
    obtain ⟨middle, first, rest, _, remaining, rfl, rfl⟩ := ran
    exact .write (value.evaluates env) (execute_sound first) (ih remaining)
  | writeUInt16LE low high value next ih =>
    by_cases adjacent : checkAdjacent state.resources low high = true
    · simp only [runCode, adjacent, Bool.not_true, Bool.false_eq_true, ite_false, bind, pure,
        Option.bind_eq_some_iff, Prod.exists, Option.some.injEq, Prod.mk.injEq] at ran
      obtain ⟨middle, first, stepHigh, second, rest, _, remaining, rfl, rfl⟩ := ran
      exact .writeUInt16LE ((checkAdjacent_correct _ _ _).mp adjacent) (value.evaluates env)
        (execute_sound first) (execute_sound second) (ih remaining)
    · simp [runCode, adjacent] at ran
  | requireLocation target location next ih =>
    by_cases located : target.location state = some location
    · exact .requireLocation located (ih (by simpa [runCode, located] using ran))
    · simp [runCode, located] at ran
  | letValue value body ih =>
    exact .letValue (value.evaluates env) (ih ran)
  | branch condition _ _ yes no =>
    cases h : condition.eval env <;> simp only [runCode, h, Bool.false_eq_true, ite_false,
      ite_true] at ran
    · exact .branchFalse (h ▸ condition.evaluates env) (no ran)
    · exact .branchTrue (h ▸ condition.evaluates env) (yes ran)
  | selectByte term _ ih =>
    exact .selectByte (term.evaluates env) (ih _ ran)

theorem runCode_correct (env : Env ctx) (state : State) (code : Code ctx)
    (steps : Program) (final : State) :
    runCode env state code = some (steps, final) ↔ Executes env state code steps final :=
  ⟨runCode_sound, Executes.agrees⟩

private theorem checked_step {state : State} {instruction : Instruction} {next : ResourceState → Bool}
    (checked : (checkInstruction state.resources instruction).any next = true) :
    ∃ middle, Step state instruction middle ∧ next middle.resources = true := by
  simp only [checkInstruction_correct, Option.any_eq_true, Option.map_eq_some_iff,
    execute_correct] at checked
  exact match checked with
    | ⟨_, ⟨middle, step, rfl⟩, rest⟩ => ⟨middle, step, rest⟩

theorem checkWithFacts_executes (code : Code ctx) (env : Env ctx) (state : State)
    (facts : BranchFacts ctx) (validFacts : facts.Valid env)
    (checked : checkWithFacts state.resources facts code = true) :
    ∃ steps final, Executes env state code steps final ∧ final.views = [] := by
  induction code generalizing state with
  | finish => exact ⟨[], state, .finish, List.isEmpty_iff.mp checked⟩
  | instruction _ _ ih =>
    obtain ⟨middle, first, rest⟩ := checked_step checked
    obtain ⟨steps, final, remaining, closed⟩ := ih env middle facts validFacts rest
    exact ⟨_, final, .instruction first remaining, closed⟩
  | read target _ ih =>
    obtain ⟨middle, first, rest⟩ := checked_step checked
    obtain ⟨value, observed⟩ := target.read_observes first
    obtain ⟨steps, final, remaining, closed⟩ :=
      ih (env.extend value) middle _ (validFacts.underBinder (ty := .byte) value) rest
    exact ⟨_, final, .read first observed remaining, closed⟩
  | readUInt16LE low high _ ih =>
    have valid := Bool.and_eq_true_iff.mp checked
    obtain ⟨middle, first, rest⟩ := checked_step valid.2
    obtain ⟨next, second, rest⟩ := checked_step rest
    obtain ⟨lo, lowObserved⟩ := low.read_observes first
    obtain ⟨hi, highObserved⟩ := high.read_observes second
    let value := decodeUInt16LE lo hi
    obtain ⟨steps, final, remaining, closed⟩ :=
      ih (env.extend value) next _ (validFacts.underBinder (ty := .uint16) value) rest
    exact ⟨_, final, .readUInt16LE ((checkAdjacent_correct _ _ _).mp valid.1)
      first lowObserved second highObserved remaining, closed⟩
  | write target value next ih =>
    have valid : (checkInstruction state.resources (target.writeInstruction (value.eval env))).any
        (fun s => checkWithFacts s facts next) = true := by
      rw [target.check_value _ _ 0]
      exact checked
    obtain ⟨middle, first, rest⟩ := checked_step valid
    obtain ⟨steps, final, remaining, closed⟩ := ih env middle facts validFacts rest
    exact ⟨_, final, .write (value.evaluates env) first remaining, closed⟩
  | writeUInt16LE low high value next ih =>
    have valid := Bool.and_eq_true_iff.mp checked
    have validLow : (checkInstruction state.resources (low.writeInstruction (splitLow (value.eval env)))).any
        (fun middle => (checkInstruction middle (high.writeInstruction (splitHigh (value.eval env)))).any
          (fun s => checkWithFacts s facts next)) = true := by
      rw [low.check_value state.resources (splitLow (value.eval env)) 0]
      have h := valid.2
      have h2 : (fun middle => (checkInstruction middle (high.writeInstruction 0)).any (fun s => checkWithFacts s facts next)) =
          (fun middle => (checkInstruction middle (high.writeInstruction (splitHigh (value.eval env)))).any (fun s => checkWithFacts s facts next)) := by
        funext m
        rw [high.check_value m 0 (splitHigh (value.eval env))]
      rw [← h2]
      exact h
    obtain ⟨middle, first, rest⟩ := checked_step validLow
    obtain ⟨stepHigh, second, rest⟩ := checked_step rest
    obtain ⟨steps, final, remaining, closed⟩ := ih env stepHigh facts validFacts rest
    exact ⟨_, final, .writeUInt16LE ((checkAdjacent_correct _ _ _).mp valid.1)
      (value.evaluates env) first second remaining, closed⟩
  | requireLocation target location _ ih =>
    obtain ⟨located, next⟩ := Bool.and_eq_true_iff.mp checked
    rw [AccessTarget.location_resources] at located
    obtain ⟨steps, final, remaining, closed⟩ := ih env state facts validFacts next
    exact ⟨steps, final, .requireLocation (of_decide_eq_true located) remaining, closed⟩
  | letValue value _ ih =>
    obtain ⟨steps, final, remaining, closed⟩ :=
      ih (env.extend (value.eval env)) state _ (validFacts.underBinder _) checked
    exact ⟨steps, final, .letValue (value.evaluates env) remaining, closed⟩
  | branch condition yesCode noCode yes no =>
    have arms : facts.checkArms condition (fun f => checkWithFacts state.resources f yesCode)
        (fun f => checkWithFacts state.resources f noCode) = true := checked
    cases h : condition.eval env
    · obtain ⟨steps, final, remaining, closed⟩ := no env state _ (validFacts.learn h)
        (BranchFacts.checkArms_sound validFacts h arms)
      exact ⟨steps, final, .branchFalse (h ▸ condition.evaluates env) remaining, closed⟩
    · obtain ⟨steps, final, remaining, closed⟩ := yes env state _ (validFacts.learn h)
        (BranchFacts.checkArms_sound validFacts h arms)
      exact ⟨steps, final, .branchTrue (h ▸ condition.evaluates env) remaining, closed⟩
  | selectByte term arms ih =>
    let value : UInt8 := term.eval env
    have valid : (List.finRange 256).all (fun i => checkWithFacts state.resources facts (arms i)) = true :=
      checked
    obtain ⟨steps, final, remaining, closed⟩ := ih value.toFin env state facts validFacts
      (List.all_eq_true.mp valid _ (List.mem_finRange _))
    exact ⟨steps, final, .selectByte (term.evaluates env) remaining, closed⟩

theorem check_executes (code : Code ctx) (env : Env ctx) (state : State)
    (checked : check state.resources code = true) :
    ∃ steps final, Executes env state code steps final ∧ final.views = [] :=
  checkWithFacts_executes code env state [] (by intro fact member; cases member) checked

theorem verified_prefix_safe {source : RawCode} {code : Code []} {first rest : Program}
    {final : State} (accepted : verify source = .ok code)
    (execution : Executes Env.empty {} code (first ++ rest) final) :
    ∃ middle, Runs {} first middle ∧ Runs middle rest final ∧ final.views = [] ∧
      middle.OwnersValid ∧ middle.ReferencesLive ∧ middle.ViewsCompatible := by
  obtain ⟨steps, verifiedFinal, verified, closed⟩ :=
    check_executes code Env.empty {} (verify_checked accepted)
  have same := Option.some.inj (verified.agrees.symm.trans execution.agrees)
  have sameFinal : verifiedFinal = final := congrArg Prod.snd same
  have finalClosed : final.views = [] := sameFinal ▸ closed
  have traceVerified := (verifyResources_correct _).mpr ⟨final, execution.trace, finalClosed⟩
  obtain ⟨middle, _, initial, _, _, owners, live, views⟩ := Core.verified_prefix_safe traceVerified
  have executed := run_complete execution.trace
  rw [run_append, run_complete initial] at executed
  exact ⟨middle, initial, run_sound executed, finalClosed, owners, live, views⟩

theorem executeClosed_total {source : RawCode} {code : Code []}
    (accepted : verify source = .ok code) :
    ∃ steps final, executeClosed source = .ok (some final) ∧
      Executes Env.empty {} code steps final ∧ final.views = [] := by
  obtain ⟨steps, final, executed, closed⟩ := check_executes code Env.empty {} (verify_checked accepted)
  exact ⟨steps, final, by simp [executeClosed, accepted, executed.agrees, bind, Except.bind, pure,
    Except.pure], executed, closed⟩

end Aethel.Structured
