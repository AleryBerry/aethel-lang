import Aethel.Structured
import Aethel.ResourceFrame
import Aethel.ByteLoans
import Aethel.SourceForkJoin
import Lean.Elab.Deriving.FromToJson

namespace Aethel.SourceVerification

open Core Functional Structured Lean

scoped instance : ToJson UInt8 where
  toJson value := toJson value.toNat

scoped instance : FromJson UInt8 where
  fromJson? value := do
    let n : Nat ← fromJson? value
    if n < 256 then return UInt8.ofNat n
    else throw "byte outside 0..255"

scoped instance : ToJson AccessMode where
  toJson
    | .shared => toJson "shared"
    | .exclusive => toJson "exclusive"

scoped instance : FromJson AccessMode where
  fromJson? value := do
    match ← value.getStr? with
    | "shared" => return .shared
    | "exclusive" => return .exclusive
    | _ => throw "expected shared or exclusive"

deriving instance ToJson, FromJson for TaskAccess

inductive Place where
  | field (offset : Nat)
  | view (index offset : Nat)
  deriving Repr, DecidableEq, ToJson, FromJson

def Place.offset : Place → Nat
  | .field offset | .view _ offset => offset

def Place.target (depth : Nat) : Place → AccessTarget
  | .field offset => .handle offset
  | .view index _ => .view (depth - (index + 1))

private def Place.Located (target : Place) (depth : Nat) (state : State) : Prop :=
  match target with
  | .field _ => True
  | .view _ offset => (target.target depth).location state = some ⟨0, offset⟩

private instance (target : Place) (depth : Nat) (state : State) :
    Decidable (target.Located depth state) := by
  cases target <;> unfold Place.Located <;> infer_instance

private theorem Place.located_resources (target : Place) (depth : Nat) (state : State) :
    target.Located depth state.resources.authorityState ↔ target.Located depth state := by
  cases target <;> simp [Place.Located, AccessTarget.location_resources]

private def Place.guardCode (target : Place) (depth : Nat) (code : Code ctx) : Code ctx :=
  match target with
  | .field _ => code
  | .view _ offset => .requireLocation (target.target depth) ⟨0, offset⟩ code

private def Place.bindCode (target : Place) (depth : Nat) (body : Code (.byte :: ctx)) : Code ctx :=
  target.guardCode depth (.read (target.target depth) body)

private def Place.writeCode (target : Place) (depth : Nat) (value : Term ctx .byte)
    (next : Code ctx) : Code ctx :=
  target.guardCode depth (.write (target.target depth) value next)

private def Place.withLocation {α : Type} (target : Place) (depth : Nat) (state : State)
    (action : Unit → Option α) : Option α :=
  if target.Located depth state then action () else none

private theorem Place.withLocation_bind {α β : Type} (target : Place) (depth : Nat) (state : State)
    (action : Unit → Option α) (next : α → Option β) :
    (target.withLocation depth state action).bind next =
      target.withLocation depth state (fun _ => (action ()).bind next) := by
  unfold Place.withLocation
  split <;> rfl

def Place.runRead (target : Place) (depth : Nat) (state : State) : Option (UInt8 × State) :=
  target.withLocation depth state fun _ => (target.target depth).readValue state

@[simp] theorem Place.runRead_field (offset depth : Nat) (state : State) :
    (Place.field offset).runRead depth state = (AccessTarget.handle offset).readValue state := rfl

private theorem Place.runRead_correct {target : Place} {depth : Nat} {state final : State} {value : UInt8} :
    target.runRead depth state = some (value, final) ↔
      target.Located depth state ∧ Step state (target.target depth).readInstruction final ∧
        final = state.observe value := by
  simp [Place.runRead, Place.withLocation, Option.ite_none_right_eq_some, AccessTarget.read_correct]

theorem Place.view_read_origin {index offset depth : Nat} {state final : State} {value : UInt8}
    (ran : (Place.view index offset).runRead depth state = some (value, final)) :
    (AccessTarget.view (depth - (index + 1))).location state = some ⟨0, offset⟩ ∧
      state.byte ⟨0, offset⟩ = some value ∧ final = state.observe value := by
  obtain ⟨located, step, observed⟩ := Place.runRead_correct.mp ran
  let target := AccessTarget.view (depth - (index + 1))
  have location : target.location state = some ⟨0, offset⟩ := located
  have loaded := AccessTarget.read_current_byte ((target.read_correct state value final).mpr ⟨step, observed⟩)
  rw [location] at loaded
  exact ⟨location, loaded, observed⟩

private theorem Place.reads_same_value {place : Place} {depth : Nat} {state middle after : State}
    {left right : UInt8} (first : place.runRead depth state = some (left, middle))
    (second : place.runRead depth middle = some (right, after)) : left = right := by
  obtain ⟨_, readLeft, observedLeft⟩ := Place.runRead_correct.mp first
  obtain ⟨_, readRight, observedRight⟩ := Place.runRead_correct.mp second
  let access := place.target depth
  have original := AccessTarget.read_current_byte ((access.read_correct _ _ _).mpr ⟨readLeft, observedLeft⟩)
  have again := AccessTarget.read_current_byte ((access.read_correct _ _ _).mpr ⟨readRight, observedRight⟩)
  rw [observedLeft] at again
  exact Option.some.inj (original.symm.trans again)

def Place.runWrite (target : Place) (depth : Nat) (state : State)
    (value : UInt8) : Option State :=
  target.withLocation depth state fun _ => Core.execute state ((target.target depth).writeInstruction value)

@[simp] theorem Place.runWrite_field (offset depth : Nat) (state : State) (value : UInt8) :
    (Place.field offset).runWrite depth state value = Core.execute state (.write offset value) := rfl

private theorem Place.runWrite_correct {target : Place} {depth : Nat} {state final : State}
    {value : UInt8} :
    target.runWrite depth state value = some final ↔
      target.Located depth state ∧ Step state ((target.target depth).writeInstruction value) final := by
  simp [Place.runWrite, Place.withLocation, Option.ite_none_right_eq_some, execute_correct]

theorem Place.view_write_origin {index offset depth : Nat} {state final : State} {value : UInt8}
    (ran : (Place.view index offset).runWrite depth state value = some final) :
    ∃ view, state.view (depth - (index + 1)) = some view ∧ view.location = ⟨0, offset⟩ ∧
      view.mode = .exclusive ∧ final = state.store ⟨0, offset⟩ value := by
  obtain ⟨located, stepped⟩ := Place.runWrite_correct.mp ran
  change Step state (.writeView (depth - (index + 1)) value) final at stepped
  cases stepped with
  | writeView found _ authority _ =>
    simp only [Place.Located, Place.target, Place.target, AccessTarget.location,
      found, Option.map_some, Option.some.injEq] at located
    exact ⟨_, found, located, by simpa [AccessMode.Allows] using authority, by rw [located]⟩

inductive ByteOperand (place : Type) where
  | literal (value : UInt8)
  | place (target : place)
  deriving Repr, DecidableEq, ToJson, FromJson

private def ByteOperand.bindCode (operand : ByteOperand Place) (depth : Nat)
    (body : Code (.byte :: ctx)) : Code ctx :=
  match operand with
  | .literal value => .letValue (.byte value) body
  | .place target => target.bindCode depth body

def ByteOperand.read (operand : ByteOperand Place) (depth : Nat) (state : State) :
    Option (UInt8 × State) :=
  match operand with
  | .literal value => some (value, state)
  | .place target => target.runRead depth state

inductive ByteOperand.Observes (depth : Nat) :
    ByteOperand Place → State → UInt8 → Program → State → Prop where
  | literal : ByteOperand.Observes depth (.literal value) state value [] state
  | place {target : Place} : target.Located depth state → Step state (target.target depth).readInstruction final →
      final = state.observe value →
      ByteOperand.Observes depth (.place target) state value [(target.target depth).readInstruction] final

theorem ByteOperand.Observes.trace {depth : Nat} {operand : ByteOperand Place} {state final : State}
    {value : UInt8} {steps : Program} (read : ByteOperand.Observes depth operand state value steps final) :
    Runs state steps final := by
  cases read with
  | literal => exact .nil
  | place _ step _ => exact .cons step .nil

theorem ByteOperand.read_correct {operand : ByteOperand Place} {depth : Nat} {state final : State}
    {value : UInt8} : operand.read depth state = some (value, final) ↔
      ∃ steps, ByteOperand.Observes depth operand state value steps final := by
  constructor
  · intro ran
    cases operand with
    | literal expected => cases ran; exact ⟨[], .literal⟩
    | place target =>
      obtain ⟨located, step, observed⟩ := Place.runRead_correct.mp ran
      exact ⟨_, .place located step observed⟩
  · rintro ⟨_, certified⟩
    cases certified with
    | literal => rfl
    | place located step observed => exact Place.runRead_correct.mpr ⟨located, step, observed⟩

private def ByteOperand.fixedRangeLength : ByteOperand Place → ByteOperand Place → Option Nat
  | .literal first, .literal stop => some (stop.toNat - first.toNat)
  | .literal first, .place _ => if first = 255 then some 0 else none
  | .place _, .literal stop => if stop = 0 then some 0 else none
  | .place first, .place stop => if first = stop then some 0 else none

private theorem ByteOperand.fixedRangeLength_sound {first stop : ByteOperand Place} {depth count : Nat}
    {state middle after : State} {a b : UInt8} (fixed : first.fixedRangeLength stop = some count)
    (readFirst : first.read depth state = some (a, middle)) (readStop : stop.read depth middle = some (b, after)) :
    b.toNat - a.toNat = count := by
  cases first <;> cases stop
  case literal.literal =>
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj readFirst)
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj readStop)
    exact Option.some.inj fixed
  case literal.place =>
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj readFirst)
    obtain ⟨rfl, length⟩ := Option.ite_none_right_eq_some.mp fixed
    rw [← Option.some.inj length]
    change b.toNat - 255 = 0
    have := b.toNat_lt
    omega
  case place.literal =>
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj readStop)
    obtain ⟨rfl, length⟩ := Option.ite_none_right_eq_some.mp fixed
    rw [← Option.some.inj length]
    exact Nat.zero_sub _
  case place.place =>
    obtain ⟨rfl, length⟩ := Option.ite_none_right_eq_some.mp fixed
    rw [← Option.some.inj length]
    obtain rfl := Place.reads_same_value readFirst readStop
    exact Nat.sub_self _

inductive Comparison where
  | equal
  | unequal
  | less
  | lessEqual
  | greater
  | greaterEqual
  deriving Repr, DecidableEq, ToJson, FromJson

def Comparison.term (comparison : Comparison) (left right : Term ctx .byte) : Term ctx .bool :=
  match comparison with
  | .equal => .byteEq left right
  | .unequal => .branch (.byteEq left right) (.bool false) (.bool true)
  | .less => .byteLt left right
  | .lessEqual => .byteLe left right
  | .greater => .byteLt right left
  | .greaterEqual => .byteLe right left

def Comparison.test (comparison : Comparison) (left right : UInt8) : Bool :=
  (comparison.term (ctx := []) (.byte left) (.byte right)).eval Env.empty

private def Comparison.guard (comparison : Comparison) : Term (.byte :: .byte :: ctx) .bool :=
  comparison.term (.var (.there .here)) (.var .here)

/-- Comparisons that follow from the byte type alone. -/
def Comparison.constantResult : Comparison → UInt8 → Option Bool
  | .less, literal => if literal = 0 then some false else none
  | .lessEqual, literal => if literal = 255 then some true else none
  | .greater, literal => if literal = 255 then some false else none
  | .greaterEqual, literal => if literal = 0 then some true else none
  | .equal, _ | .unequal, _ => none

theorem Comparison.constantResult_sound {comparison : Comparison} {literal : UInt8} {known : Bool}
    (proved : comparison.constantResult literal = some known) (value : UInt8) :
    comparison.test value literal = known := by
  cases comparison <;> simp only [Comparison.constantResult, Option.ite_none_right_eq_some,
    Option.some.injEq, reduceCtorEq] at proved
  case less =>
    obtain ⟨rfl, rfl⟩ := proved
    change decide (value.toNat < 0) = false
    simp
  case lessEqual =>
    obtain ⟨rfl, rfl⟩ := proved
    change decide (value.toNat ≤ 255) = true
    exact decide_eq_true (by have := value.toNat_lt; omega)
  case greater =>
    obtain ⟨rfl, rfl⟩ := proved
    change decide (255 < value.toNat) = false
    exact decide_eq_false (by have := value.toNat_lt; omega)
  case greaterEqual =>
    obtain ⟨rfl, rfl⟩ := proved
    change decide (0 ≤ value.toNat) = true
    simp

def Comparison.knownResult (comparison : Comparison) {α : Type} : ByteOperand α → Option Bool
  | .literal value => comparison.constantResult value
  | .place _ => none

private def Comparison.selfResult : Comparison → Bool
  | .equal | .lessEqual | .greaterEqual => true
  | .unequal | .less | .greater => false

private theorem Comparison.test_self (comparison : Comparison) (value : UInt8) :
    comparison.test value value = comparison.selfResult := by
  cases comparison <;> simp [Comparison.test, Comparison.term, Comparison.selfResult, Term.eval]

private def Comparison.guardResult (comparison : Comparison) (left : Place)
    (operand : ByteOperand Place) : Option Bool :=
  match operand with
  | .literal _ => comparison.knownResult operand
  | .place right => if left = right then some comparison.selfResult else none

private theorem Comparison.guardResult_sound {comparison : Comparison} {place : Place}
    {operand : ByteOperand Place} {depth : Nat} {state middle after : State} {left right : UInt8} {known : Bool}
    (result : comparison.guardResult place operand = some known)
    (first : place.runRead depth state = some (left, middle))
    (second : operand.read depth middle = some (right, after)) : comparison.test left right = known := by
  cases operand with
  | literal value =>
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj second)
    exact Comparison.constantResult_sound result left
  | place target =>
    by_cases same : place = target
    · subst target
      obtain rfl := Place.reads_same_value first second
      have fixed : comparison.selfResult = known := by simpa [Comparison.guardResult] using result
      exact (comparison.test_self left).trans fixed
    · simp [Comparison.guardResult, same] at result

inductive IterationCount where
  | countdown (threshold amount : UInt8)
  deriving Repr, DecidableEq, ToJson, FromJson

def IterationCount.ofByte : IterationCount → Nat → Nat
  | .countdown threshold amount, value =>
    let distance := value - threshold.toNat
    if distance = 0 then 0 else (distance - 1) / amount.toNat + 1

def IterationCount.valid : IterationCount → Bool
  | .countdown _ amount => decide (0 < amount.toNat)

/-- Byte operations with explicit control flow. A scope or branch carries its
continuation once. A call carries the resolved callee in its own lexical scope. -/
inductive Operations where
  | done
  | discard (place : Place) (next : Operations)
  | assign (target : Place) (value : UInt8) (next : Operations)
  | copy (target : Place) (source : Place) (next : Operations)
  | subtractFrom (target : Place) (source : Place) (amount : UInt8) (next : Operations)
  | withView (mode : AccessMode) (offset : Nat) (body next : Operations)
  | branch (place : Place) (comparison : Comparison) (right : ByteOperand Place)
      (yes no next : Operations)
  | range (first stop : ByteOperand Place) (body next : Operations)
  | repeatFrom (bound : Place) (iterations : IterationCount) (body next : Operations)
  | call (name : String) (body next : Operations)
  | sequence (body next : Operations)
  | reborrow (parent : Nat) (mode : AccessMode) (body next : Operations)
  | fork (tasks : List ByteTask) (next : Operations)
  deriving Repr, DecidableEq, ToJson, FromJson

/-- The guard read follows the write so it precedes the next body or
terminates the loop. The first guard read supplies the initial count. -/
def Operations.countdownIteration (offset : Nat) (amount : UInt8) (afterDecrease : Operations) : Operations :=
  .sequence (.subtractFrom (.field offset) (.field offset) amount afterDecrease) (.discard (.field offset) .done)

def Operations.countdown (offset : Nat) (threshold amount : UInt8) (afterDecrease next : Operations) : Operations :=
  .repeatFrom (.field offset) (.countdown threshold amount) (countdownIteration offset amount afterDecrease) next

abbrev Continuation := (ctx : List Ty) → Code ctx

private def repeatCode (body : Continuation → Continuation) :
    Nat → Continuation → Continuation
  | 0, rest => rest
  | count + 1, rest => body (repeatCode body count rest)

private def rangeExtent : Term (.byte :: .byte :: ctx) .byte :=
  .byteSubSat (.var .here) (.var (.there .here))

private theorem rangeExtent_value (env : Env ctx) (first stop : UInt8) :
    (rangeExtent.eval ((env.extend (ty := .byte) first).extend (ty := .byte) stop)).toFin.val =
      stop.toNat - first.toNat :=
  subtractByteSat_toNat stop first

private def selectRange (first stop : ByteOperand Place)
    (bodyAtCount : Nat → Code (.byte :: .byte :: ctx)) : Code (.byte :: .byte :: ctx) :=
  match first.fixedRangeLength stop with
  | some count => bodyAtCount count
  | none => .selectByte rangeExtent fun count => bodyAtCount count.val

def Operations.toCode : Operations → Nat → Continuation → Continuation
  | .done, _, rest => rest
  | .discard place next, depth, rest => fun ctx =>
    place.bindCode depth (next.toCode depth rest (.byte :: ctx))
  | .assign target value next, depth, rest => fun ctx =>
    target.writeCode depth (.byte value) (next.toCode depth rest ctx)
  | .copy target source next, depth, rest => fun ctx =>
    source.bindCode depth (target.writeCode depth (.var .here) (next.toCode depth rest (.byte :: ctx)))
  | .subtractFrom target source amount next, depth, rest => fun ctx =>
    source.bindCode depth (target.writeCode depth (.byteSubSat (.var .here) (.byte amount))
      (next.toCode depth rest (.byte :: ctx)))
  | .withView mode offset body next, depth, rest => fun ctx =>
    .instruction (.reserve depth offset mode)
      (body.toCode (depth + 1) (fun inner => .instruction (.release depth) (next.toCode depth rest inner)) ctx)
  | .branch place comparison right yes no next, depth, rest => fun ctx =>
    let join := next.toCode depth rest
    place.bindCode depth (right.bindCode depth
      (match comparison.guardResult place right with
        | some true => yes.toCode depth join (.byte :: .byte :: ctx)
        | some false => no.toCode depth join (.byte :: .byte :: ctx)
        | none => .branch comparison.guard (yes.toCode depth join (.byte :: .byte :: ctx))
            (no.toCode depth join (.byte :: .byte :: ctx))))
  | .range first stop body next, depth, rest => fun ctx =>
    first.bindCode depth (stop.bindCode depth (selectRange first stop fun count =>
      repeatCode (body.toCode depth) count (next.toCode depth rest) (.byte :: .byte :: ctx)))
  | .repeatFrom bound iterations body next, depth, rest => fun ctx =>
    bound.bindCode depth (.selectByte (.var .here) fun count =>
      repeatCode (body.toCode depth) (iterations.ofByte count.val) (next.toCode depth rest) (.byte :: ctx))
  | .call _ body next, depth, rest | .sequence body next, depth, rest |
    .reborrow _ _ body next, depth, rest =>
    body.toCode depth (next.toCode depth rest)
  | .fork tasks next, depth, rest => fun ctx =>
    Code.prepend (ByteTask.code tasks.flatten) (next.toCode depth rest ctx)

private def checkStable (resources : ResourceState) (instruction : Instruction) : Bool :=
  decide (checkInstruction resources instruction = some resources)

private def Place.checkAccess (target : Place) (depth : Nat) (resources : ResourceState)
    (instruction : AccessTarget → Instruction) : Bool :=
  decide (target.Located depth resources.authorityState) &&
    checkStable resources (instruction (target.target depth))

private def Place.checkRead (target : Place) (depth : Nat) (resources : ResourceState) : Bool :=
  target.checkAccess depth resources AccessTarget.readInstruction

private def ByteOperand.checkRead (operand : ByteOperand Place) (depth : Nat) (resources : ResourceState) : Bool :=
  match operand with
  | .literal _ => true
  | .place target => target.checkRead depth resources

private def Place.checkWrite (target : Place) (depth : Nat) (resources : ResourceState) : Bool :=
  target.checkAccess depth resources (·.writeInstruction 0)

private def checkScope (resources : ResourceState) (depth offset : Nat) (mode : AccessMode)
    (inside : ResourceState → Bool) : Bool :=
  (checkInstruction resources (.reserve depth offset mode)).any fun opened =>
    inside opened && decide (checkInstruction opened (.release depth) = some resources)

private def checkReborrow (resources : ResourceState) (depth parent : Nat) (mode : AccessMode) : Bool :=
  decide (parent < depth) &&
    (resources.authorityState.view (depth - (parent + 1))).any fun active =>
      resources.live active.location && decide (active.mode.Allows mode)

/-- A block preserves its resource metadata. Check both branch arms against
the same entry and validate the continuation once. The loop body needs only
one check because each iteration preserves that entry metadata. -/
def Operations.check : Operations → Nat → ResourceState → Bool
  | .done, _, _ => true
  | .discard place next, depth, resources =>
    place.checkRead depth resources && next.check depth resources
  | .assign target _ next, depth, resources =>
    target.checkWrite depth resources && next.check depth resources
  | .copy target source next, depth, resources | .subtractFrom target source _ next, depth, resources =>
    source.checkRead depth resources && target.checkWrite depth resources && next.check depth resources
  | .withView mode offset body next, depth, resources =>
    checkScope resources depth offset mode (body.check (depth + 1)) && next.check depth resources
  | .branch place comparison right yes no next, depth, resources =>
    let arms := match comparison.guardResult place right with
      | some true => yes.check depth resources
      | some false => no.check depth resources
      | none => yes.check depth resources && no.check depth resources
    place.checkRead depth resources && right.checkRead depth resources && arms && next.check depth resources
  | .range first stop body next, depth, resources =>
    first.checkRead depth resources && stop.checkRead depth resources &&
      (decide (first.fixedRangeLength stop = some 0) || body.check depth resources) &&
      next.check depth resources
  | .repeatFrom bound iterations body next, depth, resources =>
    iterations.valid && (bound.checkRead depth resources && body.check depth resources && next.check depth resources)
  | .call _ body next, depth, resources | .sequence body next, depth, resources =>
    body.check depth resources && next.check depth resources
  | .reborrow parent mode body next, depth, resources =>
    checkReborrow resources depth parent mode && (body.check depth resources && next.check depth resources)
  | .fork tasks next, depth, resources =>
    checkTasks tasks resources && next.check depth resources

theorem Operations.countdown_checked {offset depth : Nat} {threshold amount : UInt8} {afterDecrease next : Operations}
    {resources : ResourceState}
    (checked : (Operations.countdown offset threshold amount afterDecrease next).check depth resources = true) :
    0 < amount.toNat ∧ checkInstruction resources (.read offset) = some resources ∧
      (Operations.subtractFrom (.field offset) (.field offset) amount afterDecrease).check depth resources = true ∧
      next.check depth resources = true := by
  simp only [Operations.countdown, Operations.countdownIteration] at checked
  have ⟨positive, bodyNext⟩ := Bool.and_eq_true_iff.mp checked
  have ⟨⟨read, body⟩, next⟩ := Bool.and_eq_true_iff.mp bodyNext |>.imp
    Bool.and_eq_true_iff.mp id
  exact ⟨of_decide_eq_true positive, of_decide_eq_true read, (Bool.and_eq_true_iff.mp body).1, next⟩

theorem Operations.reborrow_checked {parent depth : Nat} {mode : AccessMode} {body next : Operations}
    {resources : ResourceState} (checked : (Operations.reborrow parent mode body next).check depth resources = true) :
    parent < depth ∧ ∃ active, resources.authorityState.view (depth - (parent + 1)) = some active ∧
      resources.live active.location = true ∧ active.mode.Allows mode := by
  simp only [Operations.check, checkReborrow, Bool.and_eq_true, decide_eq_true_eq] at checked
  exact ⟨checked.1.1, by
    simpa only [Option.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] using checked.1.2⟩

private def Checks (state : ResourceState) (rest : Continuation) : Prop :=
  ∀ {ctx} (facts : BranchFacts ctx), checkWithFacts state facts (rest ctx) = true

private theorem prepend_check (entry : Program) (initial final : ResourceState)
    (checked : checkResources initial entry = some final)
    (rest : Continuation) (post : Checks final rest) :
    Checks initial (fun ctx => Code.prepend entry (rest ctx)) := by
  induction entry generalizing initial with
  | nil =>
    cases checked
    exact post
  | cons step entry ih =>
    simp only [checkResources, Option.bind_eq_some_iff] at checked
    obtain ⟨middle, first, remaining⟩ := checked
    intro ctx facts
    simpa only [Code.prepend, List.foldr_cons, Structured.checkWithFacts, first, Option.any_some] using
      ih middle remaining facts

private theorem repeatCode_checked (body : Continuation → Continuation) (count : Nat)
    (state : ResourceState) (preserves : ∀ rest, Checks state rest → Checks state (body rest))
    (rest : Continuation) (post : Checks state rest) :
    Checks state (repeatCode body count rest) := by
  induction count with
  | zero => exact post
  | succ count ih => exact preserves (repeatCode body count rest) ih

private theorem Place.guardCode_checked (target : Place) (depth : Nat) {state : ResourceState}
    {ctx : List Ty} {facts : BranchFacts ctx} {code : Code ctx}
    (located : decide (target.Located depth state.authorityState) = true)
    (post : checkWithFacts state facts code = true) :
    checkWithFacts state facts (target.guardCode depth code) = true := by
  cases target with
  | field => exact post
  | view => exact Bool.and_eq_true_iff.mpr ⟨located, post⟩

private theorem Place.writeCode_checked (target : Place) (depth : Nat) {state : ResourceState}
    {ctx : List Ty} {facts : BranchFacts ctx} (value : Term ctx .byte) {next : Code ctx}
    (checked : target.checkWrite depth state = true) (post : checkWithFacts state facts next = true) :
    checkWithFacts state facts (target.writeCode depth value next) = true := by
  obtain ⟨located, writable⟩ := Bool.and_eq_true_iff.mp checked
  have valid : checkInstruction state ((target.target depth).writeInstruction 0) = some state :=
    of_decide_eq_true writable
  apply target.guardCode_checked depth located
  simpa only [checkWithFacts, valid, Option.any_some] using post

private theorem Place.bindCode_checked (target : Place) (depth : Nat)
    {ctx : List Ty} {facts : BranchFacts ctx} {state : ResourceState} {body : Code (.byte :: ctx)}
    (checked : target.checkRead depth state = true)
    (post : checkWithFacts state (facts.underBinder .byte) body = true) :
    checkWithFacts state facts (target.bindCode depth body) = true := by
  obtain ⟨located, readable⟩ := Bool.and_eq_true_iff.mp checked
  have valid : checkInstruction state (target.target depth).readInstruction = some state :=
    of_decide_eq_true readable
  apply target.guardCode_checked depth located
  simpa only [checkWithFacts, valid, Option.any_some] using post

private theorem ByteOperand.bindCode_checked (operand : ByteOperand Place) (depth : Nat)
    {ctx : List Ty} {facts : BranchFacts ctx} {state : ResourceState} {body : Code (.byte :: ctx)}
    (checked : operand.checkRead depth state = true)
    (post : checkWithFacts state (facts.underBinder .byte) body = true) :
    checkWithFacts state facts (operand.bindCode depth body) = true := by
  cases operand with
  | literal => exact post
  | place target => exact target.bindCode_checked depth checked post

private theorem Operations.check_code (ops : Operations) {depth : Nat} {state : ResourceState}
    (ok : ops.check depth state = true) (rest : Continuation) (post : Checks state rest) :
    Checks state (ops.toCode depth rest) := by
  induction ops generalizing depth state rest with
  | done => exact post
  | discard place next ih =>
    obtain ⟨readOk, nextOk⟩ := Bool.and_eq_true_iff.mp ok
    intro ctx facts
    exact place.bindCode_checked depth readOk (ih nextOk rest post _)
  | assign target value next ih =>
    obtain ⟨writable, nextOk⟩ := Bool.and_eq_true_iff.mp ok
    intro ctx facts
    exact target.writeCode_checked depth (.byte value) writable (ih nextOk rest post facts)
  | copy target source next ih | subtractFrom target source _ next ih =>
    simp only [Operations.check, Bool.and_eq_true] at ok
    obtain ⟨⟨readOk, writeOk⟩, nextOk⟩ := ok
    intro ctx facts
    exact source.bindCode_checked depth readOk
      (target.writeCode_checked depth _ writeOk (ih nextOk rest post _))
  | withView mode offset body next inside after =>
    simp only [Operations.check, checkScope, Bool.and_eq_true, Option.any_eq_true, decide_eq_true_eq] at ok
    obtain ⟨⟨opened, reserved, bodyOk, released⟩, nextOk⟩ := ok
    intro ctx facts
    simp only [Operations.toCode, checkWithFacts, reserved, Option.any_some]
    refine inside bodyOk _ ?_ facts
    intro inner facts
    simp only [checkWithFacts, released, Option.any_some]
    exact after nextOk rest post facts
  | branch place comparison operand yes no next left right joined =>
    simp only [Operations.check, Bool.and_eq_true] at ok
    obtain ⟨⟨⟨readOk, operandOk⟩, arms⟩, nextOk⟩ := ok
    intro ctx facts
    simp only [Operations.toCode]
    apply place.bindCode_checked depth readOk
    apply operand.bindCode_checked depth operandOk
    cases known : comparison.guardResult place operand with
    | none =>
      have combined : (yes.check depth state && no.check depth state) = true := by
        simpa only [known] using arms
      have ⟨yesOk, noOk⟩ := Bool.and_eq_true_iff.mp combined
      simp only [checkWithFacts, BranchFacts.checkArms]
      have yesChecked : Checks state (yes.toCode depth (next.toCode depth rest)) :=
        left yesOk _ (joined nextOk rest post)
      have noChecked : Checks state (no.toCode depth (next.toCode depth rest)) :=
        right noOk _ (joined nextOk rest post)
      split
      · exact yesChecked _
      · exact noChecked _
      · exact Bool.and_eq_true_iff.mpr ⟨yesChecked _, noChecked _⟩
    | some result =>
      cases result
      · exact right (by simpa only [known] using arms) _ (joined nextOk rest post) _
      · exact left (by simpa only [known] using arms) _ (joined nextOk rest post) _
  | range first stop body next inside after =>
    simp only [Operations.check, Bool.and_eq_true] at ok
    obtain ⟨⟨⟨firstOk, stopOk⟩, loopOk⟩, nextOk⟩ := ok
    have nextChecked : Checks state (next.toCode depth rest) := after nextOk rest post
    intro ctx facts
    simp only [Operations.toCode]
    apply first.bindCode_checked depth firstOk
    apply stop.bindCode_checked depth stopOk
    cases fixed : first.fixedRangeLength stop with
    | none =>
      have bodyOk : body.check depth state = true := by simpa [fixed] using loopOk
      simp only [selectRange, fixed, check_selectByte]
      intro count _ facts _
      exact repeatCode_checked _ count.val _ (fun tail tailOk => inside bodyOk tail tailOk) _ nextChecked facts
    | some count =>
      simp only [selectRange, fixed]
      by_cases empty : count = 0
      · subst count
        exact nextChecked _
      · have bodyOk : body.check depth state = true := by simpa [fixed, empty] using loopOk
        exact repeatCode_checked _ count _ (fun tail tailOk => inside bodyOk tail tailOk) _ nextChecked _
  | repeatFrom bound iterations body next inside after =>
    simp only [Operations.check, Bool.and_eq_true] at ok
    obtain ⟨_, ⟨readOk, bodyOk⟩, nextOk⟩ := ok
    intro ctx facts
    simp only [Operations.toCode]
    apply bound.bindCode_checked depth readOk
    apply check_selectByte.mpr
    intro count _ facts _
    exact repeatCode_checked _ (iterations.ofByte count.val) _ (fun tail tailOk => inside bodyOk tail tailOk)
      _ (after nextOk rest post) facts
  | call _ body next inside after | sequence body next inside after | reborrow _ _ body next inside after =>
    have paired : (body.check depth state && next.check depth state) = true := by
      first | exact ok | exact (Bool.and_eq_true_iff.mp ok).2
    have ⟨bodyOk, nextOk⟩ := Bool.and_eq_true_iff.mp paired
    intro ctx facts
    exact inside bodyOk _ (after nextOk rest post) facts
  | fork tasks next after =>
    have ⟨forkOk, nextOk⟩ := Bool.and_eq_true_iff.mp ok
    intro ctx facts
    exact prepend_check _ _ _ ((TaskSchedule.serial tasks).checked forkOk) _
      (after nextOk rest post) facts

def runRepeat (body : State → Option State) : Nat → State → Option State
  | 0, state => some state
  | count + 1, state => body state >>= runRepeat body count

private theorem Comparison.test_correct (comparison : Comparison) (left right : UInt8)
    (env : Env ctx) :
    comparison.guard.eval ((env.extend (ty := .byte) left).extend (ty := .byte) right) =
      comparison.test left right := by
  cases comparison <;> rfl

/-- Execute just the selected arm and reuse the loop body. The specification
uses the structured semantics through the continuation translation above. -/
def Operations.run : Operations → Nat → State → Option State
  | .done, _, state => some state
  | .discard place next, depth, state => do
    let (_, after) ← place.runRead depth state
    next.run depth after
  | .assign target value next, depth, state => do
    let after ← target.runWrite depth state value
    next.run depth after
  | .copy target source next, depth, state => do
    let (value, read) ← source.runRead depth state
    let after ← target.runWrite depth read value
    next.run depth after
  | .subtractFrom target source amount next, depth, state => do
    let (value, read) ← source.runRead depth state
    let after ← target.runWrite depth read (subtractByteSat value amount)
    next.run depth after
  | .withView mode offset body next, depth, state => do
    let entered ← Core.execute state (.reserve depth offset mode)
    let after ← body.run (depth + 1) entered
    let released ← Core.execute after (.release depth)
    next.run depth released
  | .branch place comparison right yes no next, depth, state => do
    let (left, readLeft) ← place.runRead depth state
    let (bound, readRight) ← right.read depth readLeft
    let after ← if comparison.test left bound then yes.run depth readRight else no.run depth readRight
    next.run depth after
  | .range first stop body next, depth, state => do
    let (a, middle) ← first.read depth state
    let (b, entered) ← stop.read depth middle
    let after ← runRepeat (body.run depth) (b.toNat - a.toNat) entered
    next.run depth after
  | .repeatFrom bound iterations body next, depth, state => do
    let (count, read) ← bound.runRead depth state
    let after ← runRepeat (body.run depth) (iterations.ofByte count.toNat) read
    next.run depth after
  | .call _ body next, depth, state | .sequence body next, depth, state |
    .reborrow _ _ body next, depth, state => do
    let after ← body.run depth state
    next.run depth after
  | .fork tasks next, depth, state => do
    let after ← Core.run state (ByteTask.code tasks.flatten)
    next.run depth after

theorem Operations.reborrow_erased (parent : Nat) (mode : AccessMode) (body next : Operations)
    (depth : Nat) (state : State) :
    (Operations.reborrow parent mode body next).run depth state =
      (Operations.sequence body next).run depth state := rfl

private def RunsWithResources (run : State → Option State) (entry exit : ResourceState) : Prop :=
  ∀ state, state.resources = entry → ∃ final, run state = some final ∧ final.resources = exit

private theorem RunsWithResources.thenRun {first second : State → Option State}
    {entry middle exit : ResourceState} (started : RunsWithResources first entry middle)
    (finished : RunsWithResources second middle exit) :
    RunsWithResources (fun state => (first state).bind second) entry exit := by
  intro state resources
  obtain ⟨after, ranFirst, rest⟩ := started state resources
  obtain ⟨final, ranSecond, restored⟩ := finished after rest
  exact ⟨final, by simp [ranFirst, ranSecond], restored⟩

private theorem runsWithResources_step {entry exit : ResourceState} {op : Instruction}
    (checked : checkInstruction entry op = some exit) :
    RunsWithResources (fun state => Core.execute state op) entry exit := by
  intro state resources
  rw [← resources, checkInstruction_correct, Option.map_eq_some_iff] at checked
  exact checked

private theorem runsWithResources_program {entry exit : ResourceState} {program : Program}
    (checked : checkResources entry program = some exit) :
    RunsWithResources (fun state => Core.run state program) entry exit := by
  intro state resources
  rw [← resources, checkResources_correct, Option.map_eq_some_iff] at checked
  exact checked

private theorem Place.checked_location {target : Place} {depth : Nat} {entry : ResourceState}
    {state : State} (checked : decide (target.Located depth entry.authorityState) = true)
    (resources : state.resources = entry) : target.Located depth state := by
  apply (target.located_resources depth state).mp
  rw [resources]
  exact of_decide_eq_true checked

private theorem Place.read_available {entry : ResourceState} {target : Place} {depth : Nat}
    (checked : target.checkRead depth entry = true) (state : State) (resources : state.resources = entry) :
    ∃ value middle, target.runRead depth state = some (value, middle) ∧ middle.resources = entry := by
  obtain ⟨address, permitted⟩ := Bool.and_eq_true_iff.mp checked
  have readable : checkInstruction entry (target.target depth).readInstruction = some entry :=
    of_decide_eq_true permitted
  obtain ⟨middle, executed, unchanged⟩ := runsWithResources_step readable state resources
  have step := execute_sound executed
  obtain ⟨value, observed⟩ := (target.target depth).read_observes step
  have read : target.runRead depth state = some (value, middle) :=
    Place.runRead_correct.mpr ⟨Place.checked_location address resources, step, observed⟩
  exact ⟨value, middle, read, unchanged⟩

private theorem runsWithResources_read {entry exit : ResourceState} {target : Place} {depth : Nat}
    {use : UInt8 → State → Option State}
    (checked : target.checkRead depth entry = true)
    (rest : ∀ value, RunsWithResources (use value) entry exit) :
    RunsWithResources (fun state => (target.runRead depth state).bind (fun (value, next) => use value next))
      entry exit := by
  intro state resources
  obtain ⟨value, middle, read, unchanged⟩ := Place.read_available checked state resources
  obtain ⟨final, ran, exited⟩ := rest value middle unchanged
  exact ⟨final, by simp [read, ran], exited⟩

private theorem ByteOperand.read_available {operand : ByteOperand Place} {depth : Nat}
    {entry : ResourceState} (checked : operand.checkRead depth entry = true)
    (state : State) (resources : state.resources = entry) :
    ∃ value middle, operand.read depth state = some (value, middle) ∧ middle.resources = entry := by
  cases operand with
  | literal value => exact ⟨value, state, rfl, resources⟩
  | place target => exact Place.read_available checked state resources

private theorem Place.runWrite_balanced {target : Place} {depth : Nat} {entry : ResourceState}
    (checked : target.checkWrite depth entry = true) (value : UInt8) :
    RunsWithResources (fun state => target.runWrite depth state value) entry entry := by
  obtain ⟨address, write⟩ := Bool.and_eq_true_iff.mp checked
  have stable : checkInstruction entry ((target.target depth).writeInstruction value) = some entry := by
    rw [(target.target depth).check_value entry value 0]
    exact of_decide_eq_true write
  intro state resources
  have located := Place.checked_location address resources
  obtain ⟨after, stepped, same⟩ := runsWithResources_step stable state resources
  exact ⟨after, by simp [Place.runWrite, Place.withLocation, located, stepped], same⟩

private theorem runsWithResources_update {entry : ResourceState} {source : Place}
    {target : Place} {depth : Nat} {next : State → Option State} (compute : UInt8 → UInt8)
    (read : source.checkRead depth entry = true)
    (write : target.checkWrite depth entry = true)
    (continues : RunsWithResources next entry entry) :
    RunsWithResources (fun state => do
      let (value, afterRead) ← source.runRead depth state
      let afterWrite ← target.runWrite depth afterRead (compute value)
      next afterWrite) entry entry := by
  exact runsWithResources_read read fun value => (Place.runWrite_balanced write (compute value)).thenRun continues

private theorem runRepeat_balanced {run : State → Option State} {entry : ResourceState}
    (body : RunsWithResources run entry entry) (count : Nat) :
    RunsWithResources (runRepeat run count) entry entry := by
  induction count with
  | zero => exact fun state resources => ⟨state, rfl, resources⟩
  | succ count ih => exact body.thenRun ih

private theorem Operations.check_balanced (ops : Operations) {depth : Nat} {entry : ResourceState}
    (checked : ops.check depth entry = true) : RunsWithResources (ops.run depth) entry entry := by
  induction ops generalizing depth entry with
  | done => exact fun state resources => ⟨state, rfl, resources⟩
  | discard place next ih =>
    obtain ⟨readable, nextOk⟩ := Bool.and_eq_true_iff.mp checked
    exact runsWithResources_read (use := fun _ => next.run depth) readable (fun _ => ih nextOk)
  | assign target value next ih =>
    obtain ⟨writable, nextOk⟩ := Bool.and_eq_true_iff.mp checked
    exact (Place.runWrite_balanced writable value).thenRun (ih nextOk)
  | copy offset source next ih =>
    simp only [Operations.check, Bool.and_eq_true] at checked
    obtain ⟨⟨read, write⟩, nextOk⟩ := checked
    exact runsWithResources_update id read write (ih nextOk)
  | subtractFrom offset source amount next ih =>
    simp only [Operations.check, Bool.and_eq_true] at checked
    obtain ⟨⟨read, write⟩, nextOk⟩ := checked
    exact runsWithResources_update (subtractByteSat · amount) read write (ih nextOk)
  | withView mode offset body next inside after =>
    simp only [Operations.check, checkScope, Bool.and_eq_true, Option.any_eq_true,
      decide_eq_true_eq] at checked
    obtain ⟨⟨opened, reserved, bodyOk, released⟩, nextOk⟩ := checked
    exact (runsWithResources_step reserved).thenRun
      ((inside bodyOk).thenRun ((runsWithResources_step released).thenRun (after nextOk)))
  | branch place comparison operand yes no next left right joined =>
    simp only [Operations.check, Bool.and_eq_true] at checked
    obtain ⟨⟨⟨read, operandOk⟩, arms⟩, nextOk⟩ := checked
    intro state resources
    obtain ⟨actual, middle, first, unchanged⟩ := Place.read_available read state resources
    obtain ⟨value, observed, second, restored⟩ := ByteOperand.read_available operandOk middle unchanged
    have chosen :
        (if comparison.test actual value then yes.check depth entry else no.check depth entry) = true := by
      cases known : comparison.guardResult place operand with
      | none =>
        have both := Bool.and_eq_true_iff.mp (by simpa only [known] using arms)
        cases h : comparison.test actual value
        · exact both.2
        · exact both.1
      | some result =>
        rw [Comparison.guardResult_sound known first second]
        cases result <;> simpa [known] using arms
    have selected : RunsWithResources (fun state =>
        if comparison.test actual value then (yes.run depth state).bind (next.run depth)
        else (no.run depth state).bind (next.run depth)) entry entry := by
      by_cases taken : comparison.test actual value = true
      · have yesOk : yes.check depth entry = true := by simpa [taken] using chosen
        simpa [taken] using (left yesOk).thenRun (joined nextOk)
      · have noOk : no.check depth entry = true := by simpa [taken] using chosen
        simpa [taken] using (right noOk).thenRun (joined nextOk)
    obtain ⟨final, ran, closed⟩ := selected observed restored
    exact ⟨final, by simpa only [Operations.run, bind, first, second, Option.bind_some] using ran, closed⟩
  | range first stop body next inside after =>
    simp only [Operations.check, Bool.and_eq_true] at checked
    obtain ⟨⟨⟨firstOk, stopOk⟩, loopOk⟩, nextOk⟩ := checked
    intro state resources
    obtain ⟨a, middle, readFirst, firstRestored⟩ := ByteOperand.read_available firstOk state resources
    obtain ⟨b, entered, readStop, restored⟩ := ByteOperand.read_available stopOk middle firstRestored
    have repeated : RunsWithResources (runRepeat (body.run depth) (b.toNat - a.toNat)) entry entry := by
      by_cases empty : first.fixedRangeLength stop = some 0
      · rw [ByteOperand.fixedRangeLength_sound empty readFirst readStop]
        exact fun state same => ⟨state, rfl, same⟩
      · have bodyOk : body.check depth entry = true := by simpa [empty] using loopOk
        exact runRepeat_balanced (inside bodyOk) _
    obtain ⟨final, ran, same⟩ := repeated.thenRun (after nextOk) entered restored
    exact ⟨final, by simpa only [Operations.run, bind, readFirst, readStop, Option.bind_some] using ran, same⟩
  | repeatFrom bound iterations body next inside after =>
    simp only [Operations.check, Bool.and_eq_true] at checked
    obtain ⟨_, ⟨read, bodyOk⟩, nextOk⟩ := checked
    exact runsWithResources_read read (fun count =>
      (runRepeat_balanced (inside bodyOk) (iterations.ofByte count.toNat)).thenRun (after nextOk))
  | call _ body next inside after | sequence body next inside after | reborrow _ _ body next inside after =>
    have paired : (body.check depth entry && next.check depth entry) = true := by
      first | exact checked | exact (Bool.and_eq_true_iff.mp checked).2
    have ⟨bodyOk, nextOk⟩ := Bool.and_eq_true_iff.mp paired
    exact (inside bodyOk).thenRun (after nextOk)
  | fork tasks next after =>
    have ⟨forkOk, nextOk⟩ := Bool.and_eq_true_iff.mp checked
    exact (runsWithResources_program ((TaskSchedule.serial tasks).checked forkOk)).thenRun
      (after nextOk)

/-- A checked block can run with the caller's reservations live and returns
the same allocation extents, handles, issued owners, and reservations. -/
theorem Operations.run_preserves_resources {ops : Operations} {depth : Nat} {state : State}
    (checked : ops.check depth state.resources = true) :
    ∃ final, ops.run depth state = some final ∧ final.resources = state.resources :=
  ops.check_balanced checked state rfl

private def Interprets (rest : Continuation) (run : State → Option State) : Prop :=
  ∀ {ctx} (env : Env ctx) (state : State), (runCode env state (rest ctx)).map Prod.snd = run state

private theorem repeatCode_agrees (body : Continuation → Continuation) (run : State → Option State)
    (step : ∀ rest tail, Interprets rest tail → Interprets (body rest) (fun s => (run s).bind tail))
    (count : Nat) (rest : Continuation) (tail : State → Option State) (post : Interprets rest tail) :
    Interprets (repeatCode body count rest) (fun state => (runRepeat run count state).bind tail) := by
  induction count with
  | zero => exact post
  | succ count ih =>
    intro ctx env state
    simpa only [repeatCode, runRepeat, bind, Option.bind_assoc] using
      step _ _ ih env state

private theorem runInstruction_snd (env : Env ctx) (state : State) (op : Instruction) (next : Code ctx) :
    (runCode env state (.instruction op next)).map Prod.snd =
      (Core.execute state op).bind (fun mid => (runCode env mid next).map Prod.snd) := by
  cases stepped : Core.execute state op with
  | none => simp [runCode, stepped, bind]
  | some mid =>
    cases ran : runCode env mid next <;> simp [runCode, stepped, ran, bind, pure]

private theorem runRead_snd (env : Env ctx) (state : State) (target : AccessTarget) (next : Code (.byte :: ctx)) :
    (runCode env state (.read target next)).map Prod.snd =
      (target.readValue state).bind (fun (value, mid) =>
        (runCode (env.extend value) mid next).map Prod.snd) := by
  cases read : target.readValue state with
  | none => simp [runCode, read, bind]
  | some pair =>
    rcases pair with ⟨value, mid⟩
    cases ran : runCode (env.extend (ty := .byte) value) mid next <;> simp [runCode, read, ran, bind, pure]

private theorem Place.guarded_snd (target : Place) (depth : Nat) (env : Env ctx) (state : State)
    (code : Code ctx) :
    (runCode env state (target.guardCode depth code)).map Prod.snd =
      target.withLocation depth state (fun _ => (runCode env state code).map Prod.snd) := by
  cases target with
  | field => rfl
  | view =>
    simp only [Place.guardCode, Place.withLocation, Place.Located, runCode]
    split <;> rfl

private theorem Place.readCode_snd (target : Place) (depth : Nat) (env : Env ctx)
    (state : State) (body : Code (.byte :: ctx)) :
    (runCode env state (target.bindCode depth body)).map Prod.snd =
      (target.runRead depth state).bind (fun (value, middle) =>
        (runCode (env.extend value) middle body).map Prod.snd) := by
  rw [Place.bindCode, Place.guarded_snd, Place.runRead, Place.withLocation_bind]
  congr
  funext _
  exact runRead_snd env state (target.target depth) body

private theorem ByteOperand.code_snd (operand : ByteOperand Place) (depth : Nat)
    (env : Env ctx) (state : State) (body : Code (.byte :: ctx)) :
    (runCode env state (operand.bindCode depth body)).map Prod.snd =
      (operand.read depth state).bind (fun (value, mid) =>
        (runCode (env.extend value) mid body).map Prod.snd) := by
  cases operand with
  | literal => rfl
  | place target => exact target.readCode_snd depth env state body

private theorem runWrite_snd (env : Env ctx) (state : State) (target : AccessTarget)
    (value : Term ctx .byte) (next : Code ctx) :
    (runCode env state (.write target value next)).map Prod.snd =
      (Core.execute state (target.writeInstruction (value.eval env))).bind
        (fun mid => (runCode env mid next).map Prod.snd) :=
  runInstruction_snd env state (target.writeInstruction (value.eval env)) next

private theorem Place.writeCode_snd (target : Place) (depth : Nat) (env : Env ctx)
    (state : State) (value : Term ctx .byte) (next : Code ctx) :
    (runCode env state (target.writeCode depth value next)).map Prod.snd =
      (target.runWrite depth state (value.eval env)).bind
        (fun mid => (runCode env mid next).map Prod.snd) := by
  rw [Place.writeCode, Place.guarded_snd, Place.runWrite, Place.withLocation_bind]
  congr
  funext _
  exact runWrite_snd env state (target.target depth) value next

private theorem prepend_snd (entry : Program) {ctx} (env : Env ctx) (state : State) (rest : Code ctx) :
    (runCode env state (Code.prepend entry rest)).map Prod.snd =
      (Core.run state entry).bind (fun mid => (runCode env mid rest).map Prod.snd) := by
  induction entry generalizing state with
  | nil => rfl
  | cons op entry ih =>
    simp only [Code.prepend, List.foldr_cons, runInstruction_snd, Core.run, Option.bind_assoc]
    congr
    funext middle
    exact ih middle

private theorem Operations.run_agrees (ops : Operations) (depth : Nat) (rest : Continuation)
    (tail : State → Option State) (post : Interprets rest tail) :
    Interprets (ops.toCode depth rest) (fun state => (ops.run depth state).bind tail) := by
  induction ops generalizing depth rest tail with
  | done => exact post
  | discard _ _ ih =>
    intro ctx env state
    simp only [Operations.toCode, Operations.run, Place.readCode_snd, bind, Option.bind_assoc]
    congr
    funext result
    obtain ⟨value, mid⟩ := result
    exact ih depth rest tail post (env.extend (ty := .byte) value) mid
  | assign target value next ih =>
    intro ctx env state
    simp only [Operations.toCode, Operations.run, Place.writeCode_snd, bind, Option.bind_assoc]
    congr
    funext mid
    exact ih depth rest tail post env mid
  | copy target source next ih | subtractFrom target source _ next ih =>
    intro ctx env state
    simp only [Operations.toCode, Operations.run, Place.readCode_snd, bind, Option.bind_assoc]
    congr
    funext result
    obtain ⟨value, read⟩ := result
    rw [Place.writeCode_snd]
    congr
    funext written
    exact ih depth rest tail post (env.extend (ty := .byte) value) written
  | withView mode offset body next inside after =>
    have nextAgrees := @after depth rest tail post
    have releaseAgrees : Interprets
        (fun ctx => .instruction (.release depth) (next.toCode depth rest ctx))
        (fun state => (Core.execute state (.release depth)).bind
          (fun released => (next.run depth released).bind tail)) := by
      intro ctx env state
      rw [runInstruction_snd]
      congr
      funext released
      exact nextAgrees env released
    intro ctx env state
    simp only [Operations.toCode, Operations.run, runInstruction_snd, bind, Option.bind_assoc]
    congr
    funext entered
    exact inside (depth + 1) _ _ releaseAgrees env entered
  | branch place comparison operand yes no next left right joined =>
    have joinAgrees : Interprets (next.toCode depth rest) (fun state => (next.run depth state).bind tail) :=
      joined depth rest tail post
    intro ctx env state
    simp only [Operations.toCode, Operations.run, Place.readCode_snd, bind, Option.bind_assoc]
    cases tested : place.runRead depth state with
    | none => rfl
    | some observedLeft =>
      obtain ⟨actual, middle⟩ := observedLeft
      simp only [Option.bind_some, ByteOperand.code_snd]
      cases loaded : operand.read depth middle with
      | none => rfl
      | some observedRight =>
        obtain ⟨value, observed⟩ := observedRight
        let bindings := (env.extend (ty := .byte) actual).extend (ty := .byte) value
        have yesAgrees := left depth _ _ joinAgrees bindings observed
        have noAgrees := right depth _ _ joinAgrees bindings observed
        cases known : comparison.guardResult place operand with
        | none =>
          simp only [Option.bind_some, runCode, Comparison.test_correct]
          split
          · simpa only [Option.bind_assoc] using yesAgrees
          · simpa only [Option.bind_assoc] using noAgrees
        | some result =>
          have valueAgrees := Comparison.guardResult_sound known tested loaded
          cases result
          · simpa only [Option.bind_some, valueAgrees, Bool.false_eq_true, ite_false,
              Option.bind_assoc] using noAgrees
          · simpa only [Option.bind_some, valueAgrees, ite_true, Option.bind_assoc] using yesAgrees
  | range first stop body next inside after =>
    intro ctx env state
    simp only [Operations.toCode, Operations.run, ByteOperand.code_snd, bind, Option.bind_assoc]
    cases readFirst : first.read depth state with
    | none => rfl
    | some firstValue =>
      obtain ⟨a, middle⟩ := firstValue
      simp only [Option.bind_some]
      cases readStop : stop.read depth middle with
      | none => rfl
      | some stopValue =>
        obtain ⟨b, entered⟩ := stopValue
        let bindings := (env.extend (ty := .byte) a).extend (ty := .byte) b
        have repeated := repeatCode_agrees _ _ (inside depth) (b.toNat - a.toNat) _ _
          (after depth rest tail post) bindings entered
        cases fixed : first.fixedRangeLength stop with
        | none =>
          simpa only [Option.bind_some, selectRange, fixed, runCode, rangeExtent_value, Option.bind_assoc] using
            repeated
        | some count =>
          have actual := ByteOperand.fixedRangeLength_sound fixed readFirst readStop
          simpa only [Option.bind_some, selectRange, fixed, actual, Option.bind_assoc] using repeated
  | repeatFrom bound iterations body next inside after =>
    intro ctx env state
    simp only [Operations.toCode, Operations.run, Place.readCode_snd, bind, Option.bind_assoc]
    congr
    funext read
    obtain ⟨count, middle⟩ := read
    simp only [runCode]
    change ((runCode (env.extend (ty := .byte) count) middle
      (repeatCode (body.toCode depth) (iterations.ofByte count.toNat)
        (next.toCode depth rest) (.byte :: ctx))).map Prod.snd) = _
    simpa only [Option.bind_assoc] using repeatCode_agrees _ _ (inside depth) (iterations.ofByte count.toNat) _ _
      (after depth rest tail post) (env.extend (ty := .byte) count) middle
  | call _ _ _ inside after | sequence _ _ inside after | reborrow _ _ _ _ inside after =>
    intro ctx env state
    simpa only [Operations.toCode, Operations.run, bind, Option.bind_assoc] using
      inside depth _ _ (after depth rest tail post) env state
  | fork tasks next after =>
    intro ctx env state
    simp only [Operations.toCode, Operations.run, prepend_snd, bind, Option.bind_assoc]
    congr
    funext middle
    exact after depth rest tail post env middle

theorem Operations.run_executes {ops : Operations} {depth : Nat} {state final : State}
    (ran : ops.run depth state = some final) :
    ∃ steps, Structured.Executes Env.empty state (ops.toCode depth (fun _ => .finish) []) steps final := by
  have done : Interprets (fun _ => .finish) some := fun _ _ => rfl
  have agrees := ops.run_agrees depth _ some done Env.empty state
  simp only [ran, Option.bind] at agrees
  obtain ⟨⟨steps, result⟩, executed, rfl⟩ := Option.map_eq_some_iff.mp agrees
  exact ⟨steps, runCode_sound executed⟩

theorem Operations.executes_run {ops : Operations} {depth : Nat} {state final : State} {steps : Program}
    (ran : Structured.Executes Env.empty state (ops.toCode depth (fun _ => .finish) []) steps final) :
    ops.run depth state = some final := by
  have done : Interprets (fun _ => .finish) some := fun _ _ => rfl
  have agrees := ops.run_agrees depth _ some done Env.empty state
  rw [ran.agrees] at agrees
  simpa only [Option.map_some, Option.bind_fun_some] using agrees.symm

/-- A checked block has a declarative execution that preserves the caller's
resource state. The caller can retain live views while this block runs. -/
theorem Operations.checked_trace {ops : Operations} {depth : Nat} {state : State}
    (checked : ops.check depth state.resources = true) :
    ∃ steps final,
      Structured.Executes Env.empty state (ops.toCode depth (fun _ => .finish) []) steps final ∧
      final.resources = state.resources := by
  obtain ⟨final, ran, restored⟩ := Operations.run_preserves_resources checked
  obtain ⟨steps, executed⟩ := Operations.run_executes ran
  exact ⟨steps, final, executed, restored⟩

theorem Operations.fork_agrees {tasks : List ByteTask} {schedule : ByteTask} {next : Operations}
    {state : State} {depth : Nat} (checked : (Operations.fork tasks next).check depth state.resources = true)
    (addresses : RecordAddresses state) (interleaved : TaskSchedule tasks schedule) :
    ∃ serial alternate,
      Runs state (ByteTask.code tasks.flatten) serial ∧ Runs state schedule.code alternate ∧
      serial.resources = state.resources ∧ alternate.resources = state.resources ∧
      (∀ location, serial.byte location = alternate.byte location) ∧
      (Operations.fork tasks next).run depth state = next.run depth serial := by
  have forkOk := (Bool.and_eq_true_iff.mp checked).1
  let serialOrder := TaskSchedule.serial tasks
  obtain ⟨serial, first, restoredFirst⟩ := serialOrder.executes forkOk
  obtain ⟨alternate, second, restoredSecond⟩ := interleaved.executes forkOk
  refine ⟨serial, alternate, first, second, restoredFirst, restoredSecond,
    task_schedule_deterministic forkOk addresses serialOrder interleaved first second, ?_⟩
  simp [Operations.run, bind, Core.run_complete first]

/-- A write footprint that includes every reachable store and called body.
Type-bound dead arms and literal zero-iteration bodies contribute no writes. -/
def Operations.writes : Operations → List Nat
  | .done => []
  | .discard _ next => next.writes
  | .assign target _ next | .copy target _ next | .subtractFrom target _ _ next => target.offset :: next.writes
  | .withView _ _ body next | .repeatFrom _ _ body next |
      .call _ body next | .sequence body next | .reborrow _ _ body next =>
    body.writes ++ next.writes
  | .range first stop body next =>
    (if first.fixedRangeLength stop = some 0 then [] else body.writes) ++ next.writes
  | .branch place comparison right yes no next =>
    let arms := match comparison.guardResult place right with
      | some true => yes.writes
      | some false => no.writes
      | none => yes.writes ++ no.writes
    arms ++ next.writes
  | .fork tasks next => ByteTask.writes tasks.flatten ++ next.writes

private def Frames (writes : List Nat) (before after : State) : Prop :=
  after.handles = before.handles ∧
    ∀ offset ∉ writes, after.byte ⟨0, offset⟩ = before.byte ⟨0, offset⟩

private theorem Frames.addresses {writes : List Nat} {before after : State}
    (frame : Frames writes before after) (roots : RecordAddresses before) : RecordAddresses after :=
  fun id handle found => roots id handle (by simpa only [State.handle, frame.1] using found)

private theorem Frames.thenFrame {left right : List Nat} {start middle final : State}
    (first : Frames left start middle) (second : Frames right middle final) :
    Frames (left ++ right) start final := by
  refine ⟨second.1.trans first.1, fun offset outside => ?_⟩
  exact (second.2 offset (fun h => outside (List.mem_append_right _ h))).trans
    (first.2 offset (fun h => outside (List.mem_append_left _ h)))

private theorem Frames.weaken {left right : List Nat} {start final : State}
    (frame : Frames left start final) (includeWrites : ∀ i ∈ left, i ∈ right) :
    Frames right start final :=
  ⟨frame.1, fun offset outside => frame.2 offset (fun h => outside (includeWrites offset h))⟩

private theorem Place.read_frame {target : Place} {depth : Nat} {state next : State} {value : UInt8}
    (read : target.runRead depth state = some (value, next)) : Frames [] state next := by
  obtain ⟨_, _, rfl⟩ := Place.runRead_correct.mp read
  exact ⟨rfl, fun _ _ => rfl⟩

private theorem ByteOperand.read_frame {operand : ByteOperand Place} {depth : Nat} {state next : State}
    {value : UInt8} (read : operand.read depth state = some (value, next)) : Frames [] state next := by
  cases operand with
  | literal expected =>
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj read)
    exact ⟨rfl, fun _ _ => rfl⟩
  | place target => exact Place.read_frame read

private theorem writeHandle_frames {state final : State} {written : Nat} {value : UInt8}
    (roots : RecordAddresses state) (write : Step state (.write written value) final) :
    Frames [written] state final := by
  cases write with
  | write found alive _ _ =>
    refine ⟨rfl, fun offset outside => State.store_byte_other _ _ _ _ ?_⟩
    rw [roots _ _ found]
    intro same
    exact outside (by simpa using (congrArg ByteLocation.offset same).symm)

private theorem Place.runWrite_frames {target : Place} {depth : Nat} {state final : State}
    {value : UInt8} (roots : RecordAddresses state) (ran : target.runWrite depth state value = some final) :
    Frames [target.offset] state final := by
  cases target with
  | field offset => exact writeHandle_frames roots (Place.runWrite_correct.mp ran).2
  | view index expected =>
    obtain ⟨_, _, _, _, rfl⟩ := Place.view_write_origin ran
    refine ⟨rfl, fun offset outside => State.store_byte_other _ _ _ _ ?_⟩
    intro same
    exact outside (by simpa [Place.offset] using (congrArg ByteLocation.offset same).symm)

private theorem runRepeat_frames (runBody : State → Option State) (count : Nat) (writes : List Nat)
    (frames : ∀ {s next}, RecordAddresses s → runBody s = some next → Frames writes s next)
    {state final : State} (roots : RecordAddresses state)
    (ran : runRepeat runBody count state = some final) : Frames writes state final := by
  induction count generalizing state with
  | zero =>
    cases ran
    exact ⟨rfl, fun _ _ => rfl⟩
  | succ count ih =>
    simp only [runRepeat, bind, Option.bind_eq_some_iff] at ran
    obtain ⟨middle, ranFirst, continued⟩ := ran
    have first := frames roots ranFirst
    exact (first.thenFrame (ih (first.addresses roots) continued)).weaken
      (fun i mem => (List.mem_append.mp mem).elim (·) (·))

private theorem Operations.run_frame (ops : Operations) {depth : Nat} {state final : State}
    (roots : RecordAddresses state) (ran : ops.run depth state = some final) :
    Frames ops.writes state final := by
  induction ops generalizing depth state final with
  | done =>
    cases ran
    exact ⟨rfl, fun _ _ => rfl⟩
  | discard place next ih =>
    simp only [Operations.run, bind, Option.bind_eq_some_iff, Prod.exists] at ran
    obtain ⟨value, middle, read, continued⟩ := ran
    obtain ⟨_, _, rfl⟩ := Place.runRead_correct.mp read
    exact ih (state := state.observe value) roots continued
  | assign written value next ih =>
    simp only [Operations.run, bind, Option.bind_eq_some_iff] at ran
    obtain ⟨middle, write, continued⟩ := ran
    have first := Place.runWrite_frames roots write
    exact first.thenFrame (ih (first.addresses roots) continued)
  | copy written source next ih | subtractFrom written source _ next ih =>
    simp only [Operations.run, bind, Option.bind_eq_some_iff, Prod.exists] at ran
    obtain ⟨value, read, loaded, middle, write, continued⟩ := ran
    obtain ⟨_, _, rfl⟩ := Place.runRead_correct.mp loaded
    have first := Place.runWrite_frames (state := state.observe value) roots write
    exact first.thenFrame (ih (first.addresses roots) continued)
  | withView mode field body next inside after =>
    simp only [Operations.run, bind, Option.bind_eq_some_iff] at ran
    obtain ⟨entered, reservation, middle, executed, released, release, continued⟩ := ran
    have entry : Frames [] state entered := by
      cases execute_sound reservation
      exact ⟨rfl, fun _ _ => rfl⟩
    have inner := inside (entry.addresses roots) executed
    have leaving : Frames [] middle released := by
      cases execute_sound release
      exact ⟨rfl, fun _ _ => rfl⟩
    have toNext : Frames body.writes state released := by
      simpa only [List.nil_append, List.append_nil] using (entry.thenFrame inner).thenFrame leaving
    exact toNext.thenFrame (after (toNext.addresses roots) continued)
  | branch place comparison operand yes no next left right joined =>
    simp only [Operations.run, bind, Option.bind_eq_some_iff, Prod.exists] at ran
    obtain ⟨actual, readLeft, first, value, middle, second, chosen⟩ := ran
    have reads : Frames [] state middle :=
      (Place.read_frame first).thenFrame (ByteOperand.read_frame second)
    have finish {exited : State} {writes : List Nat} (arm : Frames writes middle exited)
        (continues : next.run depth exited = some final) :
        Frames (writes ++ next.writes) state final := by
      have settled : Frames writes state exited := by
        simpa only [List.nil_append] using reads.thenFrame arm
      exact settled.thenFrame (joined (settled.addresses roots) continues)
    simp only [Operations.writes]
    cases known : comparison.guardResult place operand with
    | none =>
      split at chosen
      · obtain ⟨exited, branchRun, cont⟩ := Option.bind_eq_some_iff.mp chosen
        exact finish ((left (reads.addresses roots) branchRun).weaken (fun _ h => List.mem_append_left _ h)) cont
      · obtain ⟨exited, branchRun, cont⟩ := Option.bind_eq_some_iff.mp chosen
        exact finish ((right (reads.addresses roots) branchRun).weaken (fun _ h => List.mem_append_right _ h)) cont
    | some knownValue =>
      have tested := Comparison.guardResult_sound known first second
      cases knownValue
      · simp only [tested, Bool.false_eq_true, ite_false, Option.bind_eq_some_iff] at chosen
        obtain ⟨_, branchRun, cont⟩ := chosen
        exact finish (right (reads.addresses roots) branchRun) cont
      · simp only [tested, ite_true, Option.bind_eq_some_iff] at chosen
        obtain ⟨_, branchRun, cont⟩ := chosen
        exact finish (left (reads.addresses roots) branchRun) cont
  | range first stop body next inside after =>
    simp only [Operations.run, bind, Option.bind_eq_some_iff, Prod.exists] at ran
    obtain ⟨a, observedFirst, readFirst, b, entered, readStop, middle, loop, continued⟩ := ran
    have reads : Frames [] state entered :=
      (ByteOperand.read_frame readFirst).thenFrame (ByteOperand.read_frame readStop)
    by_cases empty : first.fixedRangeLength stop = some 0
    · rw [ByteOperand.fixedRangeLength_sound empty readFirst readStop, runRepeat] at loop
      cases loop
      simpa only [Operations.writes, empty, ite_true, List.nil_append] using
        reads.thenFrame (after (reads.addresses roots) continued)
    · have loopFrame := runRepeat_frames _ _ _ inside (reads.addresses roots) loop
      have middleFrame : Frames body.writes state middle := by
        simpa only [List.nil_append] using reads.thenFrame loopFrame
      simpa only [Operations.writes, ite_eq_right empty] using
        middleFrame.thenFrame (after (middleFrame.addresses roots) continued)
  | repeatFrom bound _ body next inside after =>
    simp only [Operations.run, bind, Option.bind_eq_some_iff, Prod.exists] at ran
    obtain ⟨count, read, snapshot, middle, loop, continued⟩ := ran
    obtain ⟨_, _, rfl⟩ := Place.runRead_correct.mp snapshot
    have loopFrame := runRepeat_frames _ _ _ inside (state := state.observe count) roots loop
    exact loopFrame.thenFrame (after (loopFrame.addresses roots) continued)
  | call _ _ _ inside after | sequence _ _ inside after | reborrow _ _ _ _ inside after =>
    simp only [Operations.run, bind, Option.bind_eq_some_iff] at ran
    obtain ⟨middle, entered, continued⟩ := ran
    have called := inside roots entered
    exact called.thenFrame (after (called.addresses roots) continued)
  | fork tasks next after =>
    simp only [Operations.run, bind, Option.bind_eq_some_iff] at ran
    obtain ⟨joined, scheduled, continued⟩ := ran
    have executed := Core.run_sound scheduled
    have frame : Frames (ByteTask.writes tasks.flatten) state joined :=
      ⟨ByteTask.handles_preserved executed, fun _ outside => ByteTask.frames_byte roots executed outside⟩
    exact frame.thenFrame (after (frame.addresses roots) continued)

/-- Every successful body execution preserves bytes outside the derived write
footprint when existing handles address their declared record fields. -/
theorem Operations.run_preserves_byte {ops : Operations} {depth : Nat} {state final : State}
    {offset : Nat} (roots : RecordAddresses state) (ran : ops.run depth state = some final)
    (outside : offset ∉ ops.writes) : final.byte ⟨0, offset⟩ = state.byte ⟨0, offset⟩ :=
  (ops.run_frame roots ran).2 offset outside

theorem Operations.run_preserves_handles {ops : Operations} {depth : Nat} {state final : State}
    (roots : RecordAddresses state) (ran : ops.run depth state = some final) :
    final.handles = state.handles :=
  (ops.run_frame roots ran).1

inductive FunctionResult where
  | unit
  | byte (offset : Nat)
  | view (mode : AccessMode) (offset : Nat)
  deriving Repr, DecidableEq, ToJson, FromJson

structure FunctionMIR where
  name : String
  paths : List String
  body : Operations
  result : FunctionResult
  deriving Repr, DecidableEq, ToJson, FromJson

structure OwnerMove where
  fromName : String
  toName : String
  deriving Repr, DecidableEq, ToJson, FromJson

/-- The reference MIR includes the initialized record and every helper
definition as well as the executable entry, including unused helpers. -/
structure SourceMIR where
  version : Nat
  record : String
  fields : List (String × UInt8)
  moves : List OwnerMove
  functions : List FunctionMIR
  body : Operations
  result : Nat
  deriving Repr, DecidableEq, ToJson, FromJson

def currentSourceMIRVersion : Nat := 15

private def recordEntry (bytes : List UInt8) : Program :=
  Core.byteRegionEntry 0 bytes

def SourceMIR.entry (mir : SourceMIR) : Program :=
  recordEntry (mir.fields.map Prod.snd)

theorem SourceMIR.entry_views (mir : SourceMIR) {state : State} (ran : Core.run {} mir.entry = some state) :
    state.views = [] :=
  (Core.byteRegionEntry_exact 0 _ ran).2.1

theorem SourceMIR.entry_initialized (mir : SourceMIR) {state : State} {offset : Nat}
    {name : String} {value : UInt8} (ran : Core.run {} mir.entry = some state)
    (field : mir.fields[offset]? = some (name, value)) :
    state.handle offset = some ⟨⟨0, offset⟩, .exclusive⟩ ∧ state.byte ⟨0, offset⟩ = some value := by
  obtain ⟨allocation, _, handles⟩ := Core.byteRegionEntry_exact 0 _ ran
  have within := (List.getElem?_eq_some_iff.mp field).choose
  exact ⟨by simp [handles, within], by simp [State.byte, State.allocation, allocation, bind, field]⟩

theorem SourceMIR.entry_addresses (bytes : List UInt8) {entered : State}
    (ran : Core.run {} (recordEntry bytes) = some entered) : RecordAddresses entered := by
  intro id handle found
  rw [(Core.byteRegionEntry_exact 0 bytes ran).2.2] at found
  split at found
  · cases found
    rfl
  · contradiction

private def exitSteps (result : FunctionResult) : Program :=
  match result with
  | .byte offset => [.read offset, .destroy 0]
  | .view mode offset => [.reserve 0 offset mode, .release 0, .destroy 0]
  | .unit => [.destroy 0]

def SourceMIR.exit (mir : SourceMIR) : Program :=
  exitSteps (.byte mir.result)

private def programCode (bytes : List UInt8) (body : Operations) (result : FunctionResult) : Code [] :=
  Code.prepend (recordEntry bytes) (body.toCode 0 (fun _ => Code.prepend (exitSteps result) .finish) [])

def SourceMIR.code (mir : SourceMIR) : Code [] :=
  programCode (mir.fields.map Prod.snd) mir.body (.byte mir.result)

def FunctionMIR.code (fnMir : FunctionMIR) (bytes : List UInt8) : Code [] :=
  programCode bytes fnMir.body fnMir.result

private def programRun (bytes : List UInt8) (body : Operations) (result : FunctionResult) : Option State := do
  let initial ← Core.run {} (recordEntry bytes)
  let after ← body.run 0 initial
  Core.run after (exitSteps result)

def SourceMIR.run (mir : SourceMIR) : Option State :=
  programRun (mir.fields.map Prod.snd) mir.body (.byte mir.result)

theorem SourceMIR.moves_erased (mir : SourceMIR) (moves : List OwnerMove) :
    { mir with moves := moves }.code = mir.code ∧ { mir with moves := moves }.run = mir.run :=
  ⟨rfl, rfl⟩

def FunctionMIR.run (fnMir : FunctionMIR) (bytes : List UInt8) : Option State :=
  programRun bytes fnMir.body fnMir.result

private theorem programRun_agrees (bytes : List UInt8) (body : Operations) (result : FunctionResult) :
    (runCode Env.empty {} (programCode bytes body result)).map Prod.snd = programRun bytes body result := by
  simp only [programCode, programRun, bind, prepend_snd]
  congr
  funext initial
  refine body.run_agrees 0 _ _ ?_ Env.empty initial
  intro ctx env state
  change (runCode env state (Code.prepend (exitSteps result) .finish)).map Prod.snd = Core.run state (exitSteps result)
  rw [prepend_snd]
  simp [runCode]

theorem SourceMIR.run_agrees (mir : SourceMIR) :
    (runCode Env.empty {} mir.code).map Prod.snd = mir.run :=
  programRun_agrees _ _ _

theorem FunctionMIR.run_agrees (fnMir : FunctionMIR) (bytes : List UInt8) :
    (runCode Env.empty {} (fnMir.code bytes)).map Prod.snd = fnMir.run bytes :=
  programRun_agrees _ _ _

private def checkProgram (bytes : List UInt8) (body : Operations) (result : FunctionResult) : Bool :=
  (checkResources {} (recordEntry bytes)).any fun r =>
    body.check 0 r && (checkResources r (exitSteps result)).any (·.views.isEmpty)

/-- Verify each helper in isolation and check every call again under the
reservations active at that point in the caller. -/
def SourceMIR.check (mir : SourceMIR) : Bool :=
  mir.functions.all (fun fnMir => checkProgram (List.replicate mir.fields.length 0) fnMir.body fnMir.result) &&
    checkProgram (mir.fields.map Prod.snd) mir.body (.byte mir.result)

theorem SourceMIR.entry_runs {mir : SourceMIR} (ok : mir.check = true) :
    ∃ state, Core.run {} mir.entry = some state := by
  have accepted := (Bool.and_eq_true_iff.mp ok).2
  simp only [checkProgram, Option.any_eq_true] at accepted
  obtain ⟨resources, checked, _⟩ := accepted
  have abstract : checkResources ({} : State).resources mir.entry = some resources := checked
  rw [checkResources_correct, Option.map_eq_some_iff] at abstract
  obtain ⟨entered, executed, _⟩ := abstract
  exact ⟨entered, executed⟩

private theorem SourceMIR.parts_checked {mir : SourceMIR} (ok : mir.check = true) {entry : State}
    (entered : Core.run {} mir.entry = some entry) :
    mir.body.check 0 entry.resources = true ∧
      ∃ closing, checkResources entry.resources mir.exit = some closing ∧ closing.views = [] := by
  have accepted := (Bool.and_eq_true_iff.mp ok).2
  simp only [checkProgram, Option.any_eq_true, Bool.and_eq_true, List.isEmpty_iff] at accepted
  obtain ⟨resources, checked, bodyOK, closing, exitOK, closed⟩ := accepted
  change checkResources ({} : State).resources mir.entry = some resources at checked
  rw [checkResources_correct, entered, Option.map_some] at checked
  obtain rfl := Option.some.inj checked
  exact ⟨bodyOK, closing, exitOK, closed⟩

theorem SourceMIR.body_checked {mir : SourceMIR} (ok : mir.check = true) {entry : State}
    (entered : Core.run {} mir.entry = some entry) : mir.body.check 0 entry.resources = true :=
  (SourceMIR.parts_checked ok entered).1

theorem SourceMIR.exit_runs {mir : SourceMIR} (ok : mir.check = true) {entry state : State}
    (entered : Core.run {} mir.entry = some entry) (restored : state.resources = entry.resources) :
    ∃ final, Runs state mir.exit final ∧ final.views = [] := by
  obtain ⟨closing, safe, closed⟩ := (SourceMIR.parts_checked ok entered).2
  rw [← restored, checkResources_correct] at safe
  obtain ⟨final, ran, exactResources⟩ := Option.map_eq_some_iff.mp safe
  exact ⟨final, run_sound ran, (congrArg ResourceState.views exactResources).trans closed⟩

private theorem checkProgram_sound {bytes : List UInt8} {body : Operations} {result : FunctionResult}
    (checked : checkProgram bytes body result = true) :
    Structured.check {} (programCode bytes body result) = true := by
  simp only [checkProgram, Option.any_eq_true, Bool.and_eq_true, List.isEmpty_iff] at checked
  obtain ⟨entry, entered, bodyOK, final, exited, closed⟩ := checked
  have finish : Checks final (fun _ => .finish) := by
    intro ctx facts
    simp [Structured.checkWithFacts, closed]
  exact prepend_check _ _ _ entered _
    (body.check_code bodyOK _ (prepend_check _ _ _ exited _ finish)) []

theorem SourceMIR.executes {mir : SourceMIR} (ok : mir.check = true) :
    ∃ steps final, Structured.Executes Env.empty {} mir.code steps final ∧ final.views = [] :=
  check_executes mir.code Env.empty {} (checkProgram_sound (Bool.and_eq_true_iff.mp ok).2)

private theorem checkProgram_input_length (body : Operations) (result : FunctionResult)
    (bytes reference : List UInt8)
    (same : bytes.length = reference.length) :
    checkProgram bytes body result = checkProgram reference body result := by
  simp only [checkProgram, recordEntry, Core.byteRegionEntry, checkResources, Core.checkInstruction, same]

theorem SourceMIR.helpers_execute {mir : SourceMIR} (ok : mir.check = true)
    (fnMir : FunctionMIR) (declared : fnMir ∈ mir.functions)
    (bytes : List UInt8) (size : bytes.length = mir.fields.length) :
    ∃ steps final, Structured.Executes Env.empty {} (fnMir.code bytes) steps final ∧ final.views = [] := by
  apply check_executes _ Env.empty {}
  have checked := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ok).1 fnMir declared
  rw [← checkProgram_input_length fnMir.body fnMir.result bytes (List.replicate mir.fields.length 0)
    (by simpa using size)] at checked
  exact checkProgram_sound checked

private def HasPost (P : State → Prop) (body : Continuation) : Prop :=
  ∀ {ctx} {env : Env ctx} {state steps final},
    Structured.Executes env state (body ctx) steps final → P final

private theorem repeatCode_post (body : Continuation → Continuation) (count : Nat)
    (P : State → Prop) (preserves : ∀ rest, HasPost P rest → HasPost P (body rest))
    (rest : Continuation) (post : HasPost P rest) :
    HasPost P (repeatCode body count rest) := by
  induction count with
  | zero => exact post
  | succ count ih => exact preserves (repeatCode body count rest) ih

private theorem prepend_post {ctx} {env : Env ctx} (entry : Program) {rest : Code ctx}
    (P : State → Prop) (post : ∀ {state steps final}, Structured.Executes env state rest steps final → P final)
    {state steps final} (ran : Structured.Executes env state (Code.prepend entry rest) steps final) :
    P final := by
  obtain ⟨_, _, _, _, continued⟩ := ran.prepend_split entry
  exact post continued

private theorem Place.guarded_executes {target : Place} {depth : Nat} {env : Env ctx}
    {state final : State} {code : Code ctx} {steps : Program}
    (ran : Structured.Executes env state (target.guardCode depth code) steps final) :
    Structured.Executes env state code steps final := by
  cases target with
  | field => exact ran
  | view =>
    cases ran with
    | requireLocation _ actual => exact actual

private theorem Place.write_continues {target : Place} {depth : Nat} {env : Env ctx}
    {state final : State} {value : Term ctx .byte} {next : Code ctx} {steps : Program}
    (ran : Structured.Executes env state (target.writeCode depth value next) steps final) :
    ∃ middle rest, Structured.Executes env middle next rest final := by
  cases Place.guarded_executes ran with
  | write _ _ following => exact ⟨_, _, following⟩

private theorem Place.read_continues {target : Place} {depth : Nat} {env : Env ctx}
    {state final : State} {body : Code (.byte :: ctx)} {steps : Program}
    (ran : Structured.Executes env state (target.bindCode depth body) steps final) :
    ∃ value middle rest, Structured.Executes (env.extend value) middle body rest final := by
  cases Place.guarded_executes ran with
  | read _ _ following => exact ⟨_, _, _, following⟩

private theorem ByteOperand.continues {operand : ByteOperand Place} {depth : Nat} {env : Env ctx}
    {state final : State} {body : Code (.byte :: ctx)} {steps : Program}
    (ran : Structured.Executes env state (operand.bindCode depth body) steps final) :
    ∃ value middle rest, Structured.Executes (env.extend value) middle body rest final := by
  cases operand with
  | literal =>
    cases ran with
    | letValue _ following => exact ⟨_, _, _, following⟩
  | place => exact Place.read_continues ran

private theorem Operations.toCode_post (ops : Operations) (P : State → Prop)
    (rest : Continuation) (depth : Nat)
    (post : ∀ {ctx} {env : Env ctx} {state steps final},
      Structured.Executes env state (rest ctx) steps final → P final)
    {ctx} {env : Env ctx} {state steps final}
    (run : Structured.Executes env state (ops.toCode depth rest ctx) steps final) : P final := by
  induction ops generalizing rest depth ctx state steps final with
  | done => exact post run
  | discard _ _ ih =>
    obtain ⟨_, _, _, continued⟩ := Place.read_continues run
    exact ih rest depth post continued
  | assign target value next ih =>
    obtain ⟨_, _, continued⟩ := Place.write_continues run
    exact ih rest depth post continued
  | copy target source next ih | subtractFrom target source _ next ih =>
    obtain ⟨_, _, _, afterRead⟩ := Place.read_continues run
    obtain ⟨_, _, continued⟩ := Place.write_continues afterRead
    exact ih rest depth post continued
  | withView mode offset body next inside after =>
    cases run with
    | instruction _ continued =>
      refine inside _ (depth + 1) ?_ continued
      intro _ _ _ _ _ released
      cases released with
      | instruction _ resumed => exact after rest depth post resumed
  | branch place comparison operand yes no next left right joined =>
    obtain ⟨_, _, _, rightRead⟩ := Place.read_continues run
    obtain ⟨_, _, _, chosen⟩ := ByteOperand.continues rightRead
    cases known : comparison.guardResult place operand with
    | none =>
      simp only [known] at chosen
      cases chosen with
      | branchTrue _ ran => exact left _ depth (joined rest depth post) ran
      | branchFalse _ ran => exact right _ depth (joined rest depth post) ran
    | some result =>
      cases result
      · exact right _ depth (joined rest depth post) (by simpa only [known] using chosen)
      · exact left _ depth (joined rest depth post) (by simpa only [known] using chosen)
  | range first stop body next inside after =>
    have repeated (count : Nat) :
        HasPost P (repeatCode (body.toCode depth) count (next.toCode depth rest)) :=
      repeatCode_post (body.toCode depth) count P (fun tail tailPost => inside tail depth tailPost)
        (next.toCode depth rest) (after rest depth post)
    obtain ⟨_, _, _, readStop⟩ := ByteOperand.continues run
    obtain ⟨_, _, _, selected⟩ := ByteOperand.continues readStop
    cases fixed : first.fixedRangeLength stop with
    | some count => exact repeated count (by simpa only [selectRange, fixed] using selected)
    | none =>
      simp only [selectRange, fixed] at selected
      cases selected with
      | selectByte evaluated ran => exact repeated _ ran
  | repeatFrom bound _ body next inside after =>
    obtain ⟨_, _, _, selected⟩ := Place.read_continues run
    cases selected with
    | selectByte evaluated ran =>
      exact repeatCode_post (body.toCode depth) _ P
        (fun tail tailPost => inside tail depth tailPost)
        (next.toCode depth rest) (after rest depth post) ran
  | call _ _ _ inside after | sequence _ _ inside after | reborrow _ _ _ _ inside after =>
    exact inside _ depth (after rest depth post) run
  | fork tasks next after =>
    exact prepend_post _ P (fun continued => after rest depth post continued) run

private theorem programCode_post {bytes body result steps final} (P : State → Prop)
    (exitPost : HasPost P (fun _ => Code.prepend (exitSteps result) .finish))
    (ran : Structured.Executes Env.empty {} (programCode bytes body result) steps final) : P final :=
  prepend_post _ P (fun bodyRun => Operations.toCode_post body P _ 0 exitPost bodyRun) ran

private theorem exitSteps_result {offset : Nat} {state final : State}
    (ran : Runs state (exitSteps (.byte offset)) final) :
    ∃ after value, Step state (.read offset) after ∧
      Step after (.destroy 0) final ∧ final.observations.head? = some value := by
  cases ran with
  | cons reads continued =>
    cases continued with
    | cons destroys finished =>
      cases finished
      obtain ⟨value, observed⟩ := AccessTarget.read_observes (target := .handle offset) reads
      refine ⟨_, value, reads, destroys, ?_⟩
      cases destroys
      simp [observed, State.removeOwner, State.observe]

theorem SourceMIR.exit_result (mir : SourceMIR) {state final : State} (ran : Runs state mir.exit final) :
    ∃ after value, Step state (.read mir.result) after ∧
      Step after (.destroy 0) final ∧ final.observations.head? = some value :=
  exitSteps_result ran

private theorem programCode_result {bytes : List UInt8} {body : Operations} {offset : Nat} {steps final}
    (ran : Structured.Executes Env.empty {} (programCode bytes body (.byte offset)) steps final) :
    ∃ before after value, Step before (.read offset) after ∧
      Step after (.destroy 0) final ∧ final.observations.head? = some value := by
  let P : State → Prop := fun state =>
    ∃ before after value, Step before (.read offset) after ∧
      Step after (.destroy 0) state ∧ state.observations.head? = some value
  change P final
  apply programCode_post P ?_ ran
  intro ctx env state steps final ran
  obtain ⟨_, _, _, exit, finished⟩ := ran.prepend_split (exitSteps (.byte offset))
  cases finished
  obtain ⟨_, _, reads, destroys, observed⟩ := exitSteps_result exit
  exact ⟨_, _, _, reads, destroys, observed⟩

theorem SourceMIR.main_result {mir : SourceMIR} {steps final}
    (ran : Structured.Executes Env.empty {} mir.code steps final) :
    ∃ before after value, Step before (.read mir.result) after ∧
      Step after (.destroy 0) final ∧ final.observations.head? = some value :=
  programCode_result ran

theorem FunctionMIR.result_observed {fnMir : FunctionMIR} {bytes : List UInt8} {offset : Nat}
    {steps final} (returns : fnMir.result = .byte offset)
    (ran : Structured.Executes Env.empty {} (fnMir.code bytes) steps final) :
    ∃ before after value, Step before (.read offset) after ∧
      Step after (.destroy 0) final ∧ final.observations.head? = some value := by
  apply programCode_result (bytes := bytes) (body := fnMir.body)
  simpa only [FunctionMIR.code, returns] using ran

theorem FunctionMIR.view_result_reserved {fnMir : FunctionMIR} {bytes : List UInt8}
    {mode : AccessMode} {offset : Nat} {steps final} (returns : fnMir.result = .view mode offset)
    (ran : Structured.Executes Env.empty {} (fnMir.code bytes) steps final) :
    ∃ before opened released handle, before.handle offset = some handle ∧
      opened.view 0 = some ⟨0, handle.location, mode⟩ ∧
      Step before (.reserve 0 offset mode) opened ∧ Step opened (.release 0) released ∧
      Step released (.destroy 0) final := by
  let P : State → Prop := fun final =>
    ∃ before opened released handle, before.handle offset = some handle ∧
      opened.view 0 = some ⟨0, handle.location, mode⟩ ∧
      Step before (.reserve 0 offset mode) opened ∧ Step opened (.release 0) released ∧
      Step released (.destroy 0) final
  change P final
  have ranView : Structured.Executes Env.empty {} (programCode bytes fnMir.body (.view mode offset)) steps final := by
    simpa only [FunctionMIR.code, returns] using ran
  apply programCode_post P ?_ ranView
  intro ctx env state steps final leaves
  cases leaves with
  | instruction reserve reserved =>
    cases reserved with
    | instruction release released =>
      cases released with
      | instruction destroy dropped =>
        cases dropped
        cases reserve with
        | reserve _ handle _ _ _ =>
          exact ⟨_, _, _, _, handle, by simp [State.view, State.addView], .reserve ‹_› handle ‹_› ‹_› ‹_›,
            release, destroy⟩

end Aethel.SourceVerification
