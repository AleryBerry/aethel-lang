import Aethel.SourceMIR

namespace Aethel.SourceVerification

open Core Functional Structured

/-- A half-open range steps through consecutive indices using its original
endpoints. This reference fragment discards the loop index. -/
inductive RangeExecutes (body : Code []) (stop : Nat) : Nat → State → Program → State → Prop where
  | finished : stop ≤ index → RangeExecutes body stop index state [] state
  | iterate : index < stop → Structured.Executes Env.empty state body bodySteps middle →
      RangeExecutes body stop (index + 1) middle rest final →
      RangeExecutes body stop index state (bodySteps ++ rest) final

theorem RangeExecutes.trace {body : Code []} {first stop : Nat} {state final : State} {steps : Program}
    (ran : RangeExecutes body stop first state steps final) : Runs state steps final := by
  induction ran with
  | finished _ => exact .nil
  | iterate _ began _ rest => exact began.trace.append rest

private theorem runRepeat_range {body : Operations} {depth first stop : Nat} {state final : State}
    (ran : runRepeat (body.run depth) (stop - first) state = some final) :
    ∃ steps, RangeExecutes (body.toCode depth (fun _ => .finish) []) stop first state steps final := by
  have matchCount : ∀ count index start, stop - index = count →
      runRepeat (body.run depth) count start = some final →
      ∃ steps, RangeExecutes (body.toCode depth (fun _ => .finish) []) stop index start steps final := by
    intro count
    induction count with
    | zero =>
      intro index start empty finished
      cases finished
      exact ⟨[], .finished (Nat.sub_eq_zero_iff_le.mp empty)⟩
    | succ count shorter =>
      intro index start remaining executed
      simp only [runRepeat, bind, Option.bind_eq_some_iff] at executed
      obtain ⟨middle, initial, rest⟩ := executed
      obtain ⟨bodySteps, began⟩ := Operations.run_executes initial
      obtain ⟨restSteps, finished⟩ := shorter (index + 1) middle (by omega) rest
      exact ⟨bodySteps ++ restSteps, .iterate (by omega) began finished⟩
  exact matchCount (stop - first) first state rfl ran

/-- The two endpoint expressions run in source order before the first body.
The body can change bytes used by either expression after the snapshot. -/
inductive ForRangeExecutes (depth : Nat) (first stop : ByteOperand Place) (body next : Operations) :
    State → Program → State → Prop where
  | range : ByteOperand.Observes depth first state a firstSteps middle →
      ByteOperand.Observes depth stop middle b stopSteps entered →
      RangeExecutes (body.toCode depth (fun _ => .finish) []) b.toNat a.toNat entered bodySteps stopped →
      Structured.Executes Env.empty stopped (next.toCode depth (fun _ => .finish) []) afterSteps final →
      ForRangeExecutes depth first stop body next state (firstSteps ++ stopSteps ++ bodySteps ++ afterSteps) final

theorem ForRangeExecutes.trace {depth : Nat} {first stop : ByteOperand Place} {body next : Operations}
    {state final : State} {steps : Program}
    (ran : ForRangeExecutes depth first stop body next state steps final) : Runs state steps final := by
  cases ran with
  | range readFirst readStop body rest => exact ((readFirst.trace.append readStop.trace).append body.trace).append rest.trace

theorem Operations.range_matches_for {depth : Nat} {first stop : ByteOperand Place} {body next : Operations}
    {state final : State} (ran : (Operations.range first stop body next).run depth state = some final) :
    ∃ steps, ForRangeExecutes depth first stop body next state steps final := by
  simp only [Operations.run, bind, Option.bind_eq_some_iff, Prod.exists] at ran
  obtain ⟨a, middle, readFirst, b, entered, readStop, stopped, iterations, continued⟩ := ran
  obtain ⟨firstSteps, firstObserved⟩ := ByteOperand.read_correct.mp readFirst
  obtain ⟨stopSteps, stopObserved⟩ := ByteOperand.read_correct.mp readStop
  obtain ⟨bodySteps, bodyRan⟩ := runRepeat_range iterations
  obtain ⟨afterSteps, nextRan⟩ := Operations.run_executes continued
  exact ⟨firstSteps ++ stopSteps ++ bodySteps ++ afterSteps,
    .range firstObserved stopObserved bodyRan nextRan⟩

/-- An independently specified while loop reads its guard before every
iteration, runs the selected body in that state, and stops at the first false
guard. The specification has no fuel parameter. -/
inductive WhileExecutes (target : AccessTarget) (condition : UInt8 → Bool) (body : Code []) :
    State → Program → State → Prop where
  | stop : Step state target.readInstruction after → after = state.observe value →
      condition value = false → WhileExecutes target condition body state [target.readInstruction] after
  | iterate : Step state target.readInstruction after → after = state.observe value → condition value = true →
      Structured.Executes Env.empty after body bodySteps middle →
      WhileExecutes target condition body middle rest final →
      WhileExecutes target condition body state (target.readInstruction :: bodySteps ++ rest) final

theorem WhileExecutes.trace {target : AccessTarget} {condition : UInt8 → Bool} {body : Code []}
    {state final : State} {steps : Program}
    (loop : WhileExecutes target condition body state steps final) : Runs state steps final := by
  induction loop with
  | stop read _ _ => exact .cons read .nil
  | iterate read _ _ bodyRun _ ih =>
    exact .cons read (bodyRun.trace.append ih)

theorem WhileExecutes.guard_at_exit {target : AccessTarget} {condition : UInt8 → Bool} {body : Code []}
    {state final : State} {steps : Program}
    (loop : WhileExecutes target condition body state steps final) :
    ∃ value, condition value = false ∧ (target.location final).bind final.byte = some value := by
  induction loop with
  | stop read observed finished =>
    have readValue := (target.read_correct _ _ _).mpr ⟨read, observed⟩
    have current := AccessTarget.read_current_byte readValue
    cases observed
    cases target <;> exact ⟨_, finished, current⟩
  | iterate _ _ _ _ _ after => exact after

abbrev ResourceInput (entry : ResourceState) := { state : State // state.resources = entry }

/-- Evidence for a checked while loop. The measure decreases across the
actual guard read and selected body execution. The body retains the caller's
handles and reservations. Guard and body checks are independent of heap data. -/
structure CheckedWhile (entry : ResourceState) where
  target : AccessTarget
  condition : UInt8 → Bool
  body : Operations
  depth : Nat
  measure : State → Nat
  guardChecked : checkInstruction entry target.readInstruction = some entry
  bodyChecked : body.check depth entry = true
  decreases : ∀ {start after middle value}, start.resources = entry →
    target.readValue start = some (value, after) → condition value = true →
    body.run depth after = some middle → measure middle < measure start

private def getResult {α : Type} (result : Option α) (existsValue : ∃ value, result = some value) :
    { value : α // result = some value } :=
  match result with
  | some value => ⟨value, rfl⟩
  | none => False.elim (by simp at existsValue)

private theorem CheckedWhile.canRead (loop : CheckedWhile entry) (input : ResourceInput entry) :
    ∃ pair, loop.target.readValue input.val = some pair := by
  have checked : checkInstruction input.val.resources loop.target.readInstruction = some entry := by
    rw [input.property]
    exact loop.guardChecked
  rw [checkInstruction_correct, Option.map_eq_some_iff] at checked
  obtain ⟨middle, first, _⟩ := checked
  have read := execute_sound first
  obtain ⟨value, observed⟩ := loop.target.read_observes read
  exact ⟨(value, middle), (loop.target.read_correct _ _ _).mpr ⟨read, observed⟩⟩

private structure LoopRead (loop : CheckedWhile entry) (input : State) where
  value : UInt8
  after : ResourceInput entry
  ran : loop.target.readValue input = some (value, after.val)

private def CheckedWhile.read (loop : CheckedWhile entry) (input : ResourceInput entry) :
    LoopRead loop input.val :=
  let result := getResult (loop.target.readValue input.val) (loop.canRead input)
  let next : ResourceInput entry := ⟨result.val.2, by
    obtain ⟨_, observed⟩ := (loop.target.read_correct _ _ _).mp result.property
    rw [observed]
    exact input.property⟩
  ⟨result.val.1, next, result.property⟩

private def CheckedWhile.advance (loop : CheckedWhile entry) (input : ResourceInput entry) :
    { next : ResourceInput entry // loop.body.run loop.depth input.val = some next.val } :=
  let checked : loop.body.check loop.depth input.val.resources = true := by
    rw [input.property]
    exact loop.bodyChecked
  let existsNext := Operations.run_preserves_resources (state := input.val) checked
  let result := getResult (loop.body.run loop.depth input.val) (by
    obtain ⟨state, ran, _⟩ := existsNext
    exact ⟨state, ran⟩)
  let next : ResourceInput entry := ⟨result.val, by
    obtain ⟨state, ran, unchanged⟩ := existsNext
    have same := Option.some.inj (result.property.symm.trans ran)
    exact (congrArg State.resources same).trans (unchanged.trans input.property)⟩
  ⟨next, result.property⟩

def CheckedWhile.run (loop : CheckedWhile entry) (input : ResourceInput entry) : ResourceInput entry :=
  let observed := loop.read input
  if take : loop.condition observed.value = true then
    let next := loop.advance observed.after
    have _smaller := loop.decreases input.property observed.ran take next.property
    loop.run next.val
  else
    observed.after
termination_by loop.measure input.val

theorem CheckedWhile.run_correct (loop : CheckedWhile entry) (input : ResourceInput entry) :
    ∃ steps, WhileExecutes loop.target loop.condition
      (loop.body.toCode loop.depth (fun _ => .finish) []) input.val steps (loop.run input).val := by
  induction input using (_root_.measure (fun input : ResourceInput entry => loop.measure input.val)).wf.induction with
  | h initial ih =>
    rw [CheckedWhile.run]
    let observed := loop.read initial
    obtain ⟨guardStep, guardObserved⟩ := (loop.target.read_correct _ _ _).mp observed.ran
    by_cases take : loop.condition observed.value = true
    · simp only [observed, take, dite_eq_left]
      let next := loop.advance observed.after
      have smaller := loop.decreases initial.property observed.ran take next.property
      obtain ⟨bodySteps, bodyRun⟩ := Operations.run_executes next.property
      obtain ⟨rest, continued⟩ := ih next.val smaller
      exact ⟨_, .iterate guardStep guardObserved take bodyRun continued⟩
    · simp only [observed, take]
      exact ⟨_, .stop guardStep guardObserved (Bool.eq_false_iff.mpr take)⟩

private def handleByteMeasure (offset : Nat) (state : State) : Nat :=
  (((AccessTarget.handle offset).location state).bind state.byte).getD 0 |>.toNat

private theorem counter_stored {start after middle : State} {value amount : UInt8}
    {offset depth : Nat}
    (guardRead : (AccessTarget.handle offset).readValue start = some (value, after))
    (executed : (Operations.subtractFrom (.field offset) (.field offset) amount .done).run depth after =
      some middle) :
    ((AccessTarget.handle offset).location middle).bind middle.byte = some (subtractByteSat value amount) := by
  have oldByte := AccessTarget.read_current_byte guardRead
  obtain ⟨_, rfl⟩ := ((AccessTarget.handle offset).read_correct _ _ _).mp guardRead
  simp only [Operations.run, Place.runRead_field, Place.runWrite_field, bind, Option.bind_eq_some_iff, Prod.exists,
    Option.some.injEq] at executed
  obtain ⟨loaded, read, readBody, stored, written, rfl⟩ := executed
  have loadByte := AccessTarget.read_current_byte readBody
  change ((AccessTarget.handle offset).location start).bind start.byte = some loaded at loadByte
  have same := Option.some.inj (oldByte.symm.trans loadByte)
  subst loaded
  cases execute_sound written with
  | write found live _ _ =>
    rename_i handle _ _ _
    have storeLocation : (AccessTarget.handle offset).location
        (read.store handle.location (subtractByteSat value amount)) = some handle.location := by
      change (read.handle offset).map Handle.location = _
      rw [found]
      rfl
    rw [storeLocation]
    exact State.store_byte_written _ _ _ _ live

private def CounterUpdate (entry : ResourceState) (depth offset : Nat) (amount : UInt8)
    (body : Operations) : Prop :=
  ∀ {start after middle value}, start.resources = entry →
    (AccessTarget.handle offset).readValue start = some (value, after) →
    body.run depth after = some middle →
    ((AccessTarget.handle offset).location middle).bind middle.byte = some (subtractByteSat value amount)

private def CheckedWhile.bySaturatingUpdate (entry : ResourceState) (depth offset : Nat) (threshold amount : UInt8)
    (positive : 0 < amount.toNat)
    (canRead : checkInstruction entry (.read offset) = some entry)
    (body : Operations) (checked : body.check depth entry = true)
    (update : CounterUpdate entry depth offset amount body) :
    CheckedWhile entry where
  target := .handle offset
  condition := fun value => decide (threshold.toNat < value.toNat)
  body := body
  depth := depth
  measure := handleByteMeasure offset
  guardChecked := canRead
  bodyChecked := checked
  decreases := by
    intro start after middle value same read take ran
    have written := update same read ran
    have original := AccessTarget.read_current_byte read
    rw [handleByteMeasure, handleByteMeasure, original, written]
    exact subtractByteSat_strict_decrease (Nat.lt_of_le_of_lt (Nat.zero_le _) (of_decide_eq_true take)) positive

def CheckedWhile.saturatingCountdown (entry : ResourceState) (depth offset : Nat) (amount : UInt8)
    (positive : 0 < amount.toNat)
    (canRead : checkInstruction entry (.read offset) = some entry)
    (canSubtract : (Operations.subtractFrom (.field offset) (.field offset) amount .done).check depth entry = true) :
    CheckedWhile entry :=
  CheckedWhile.bySaturatingUpdate entry depth offset 0 amount positive canRead _ canSubtract
    (fun _ read ran => counter_stored read ran)

private theorem afterDecrease_counter {entry : ResourceState} {offset depth : Nat} {amount : UInt8}
    {effects : Operations} (roots : RecordAddresses entry.authorityState) (outside : offset ∉ effects.writes) :
    CounterUpdate entry depth offset amount (.subtractFrom (.field offset) (.field offset) amount effects) := by
  intro start before final value same guard executed
  have sameHandles := congrArg ResourceState.handles same
  dsimp [State.resources] at sameHandles
  have rooted : RecordAddresses start := fun id handle found =>
    roots id handle (by simpa only [State.handle, ResourceState.authorityState, sameHandles] using found)
  obtain ⟨_, observed⟩ := ((AccessTarget.handle offset).read_correct _ _ _).mp guard
  have beforeRoots : RecordAddresses before := observed.symm ▸ rooted
  simp only [Operations.run, Place.runRead_field, Place.runWrite_field, bind, Option.bind_eq_some_iff,
    Prod.exists] at executed
  obtain ⟨loaded, priorStore, loadedStep, stored, storeStep, complete⟩ := executed
  have justDecreased : (Operations.subtractFrom (.field offset) (.field offset) amount .done).run depth before =
      some stored := by
    simp [Operations.run, bind, loadedStep, storeStep]
  have updated := counter_stored guard justDecreased
  have handles := Operations.run_preserves_handles beforeRoots justDecreased
  have storedRoots : RecordAddresses stored := fun id handle found =>
    beforeRoots id handle (by simpa only [State.handle, handles] using found)
  have location : (AccessTarget.handle offset).location stored = some ⟨0, offset⟩ := by
    cases found : stored.handle offset with
    | none => simp [AccessTarget.location, found] at updated
    | some handle => simp [AccessTarget.location, found, storedRoots _ _ found]
  have stillLocated : (AccessTarget.handle offset).location final = some ⟨0, offset⟩ := by
    have kept := Operations.run_preserves_handles storedRoots complete
    simpa only [AccessTarget.location, State.handle, kept] using location
  rw [stillLocated]
  change final.byte ⟨0, offset⟩ = _
  rw [Operations.run_preserves_byte storedRoots complete outside]
  simpa only [location, Option.bind] using updated

def checkSaturatingCountdown (entry : ResourceState) (depth offset : Nat) (amount : UInt8) :
    Option (CheckedWhile entry) :=
  if allowed : (0 < amount.toNat) ∧ checkInstruction entry (.read offset) = some entry ∧
      (Operations.subtractFrom (.field offset) (.field offset) amount .done).check depth entry = true then
    some (CheckedWhile.saturatingCountdown entry depth offset amount allowed.1 allowed.2.1 allowed.2.2)
  else none

theorem CheckedWhile.saturatingCountdown_zero {entry : ResourceState} {depth offset : Nat} {amount : UInt8}
    (positive canRead canSubtract) (input : ResourceInput entry) :
    let final := (CheckedWhile.saturatingCountdown entry depth offset amount positive canRead canSubtract).run input
    ((AccessTarget.handle offset).location final.val).bind final.val.byte = some 0 := by
  obtain ⟨_, ran⟩ := (CheckedWhile.saturatingCountdown entry depth offset amount
    positive canRead canSubtract).run_correct input
  obtain ⟨value, finished, loaded⟩ := ran.guard_at_exit
  have zero : value = 0 := by
    apply UInt8.toNat_inj.mp
    change decide (0 < value.toNat) = false at finished
    simp only [decide_eq_false_iff_not] at finished
    exact Nat.eq_zero_of_not_pos finished
  exact zero ▸ loaded

private theorem countdownIteration_run {start after final : State} {offset depth : Nat} {amount : UInt8}
    {effects : Operations}
    (changed : (Operations.subtractFrom (.field offset) (.field offset) amount effects).run depth start = some after)
    (tested : (AccessTarget.handle offset).readValue after = some (value, final)) :
    (Operations.countdownIteration offset amount effects).run depth start = some final := by
  change ((Operations.subtractFrom (.field offset) (.field offset) amount effects).run depth start).bind
    ((Operations.discard (.field offset) .done).run depth) = _
  rw [changed]
  simp [Operations.run, bind, tested]

private theorem countdown_count_zero {threshold amount : UInt8} {value : Nat} :
    (IterationCount.countdown threshold amount).ofByte value = 0 ↔ value ≤ threshold.toNat := by
  by_cases ended : value ≤ threshold.toNat
  · simp [IterationCount.ofByte, Nat.sub_eq_zero_of_le ended, ended]
  · have positiveDistance : value - threshold.toNat ≠ 0 := by omega
    simp [IterationCount.ofByte, positiveDistance, ended]

theorem IterationCount.countdown_step (threshold amount : UInt8) (positive : 0 < amount.toNat)
    {value : Nat} (entered : threshold.toNat < value) :
    (IterationCount.countdown threshold amount).ofByte (value - amount.toNat) + 1 =
      (IterationCount.countdown threshold amount).ofByte value := by
  let distance := value - threshold.toNat
  have distanceAfter : value - amount.toNat - threshold.toNat = distance - amount.toNat := by
    dsimp [distance]
    omega
  have nonzero : distance ≠ 0 := by dsimp [distance]; omega
  simp only [IterationCount.ofByte, distanceAfter, ← show distance = value - threshold.toNat from rfl]
  by_cases crosses : distance ≤ amount.toNat
  · have ended : distance - amount.toNat = 0 := Nat.sub_eq_zero_of_le crosses
    have first : (distance - 1) / amount.toNat = 0 := Nat.div_eq_of_lt (by omega)
    simp [nonzero, ended, first]
  · have running : distance - amount.toNat ≠ 0 := by omega
    have divides := Nat.div_eq_sub_div positive (show amount.toNat ≤ distance - 1 by omega)
    have rearranged : distance - amount.toNat - 1 = distance - 1 - amount.toNat := by omega
    simp only [ite_eq_right running, ite_eq_right nonzero, rearranged]
    rw [divides]

/-- The compact countdown schedule yields the same byte-machine state as
the independently checked while semantics, including the repeated reads of
the guard and its final observation at or below the threshold. -/
private theorem CheckedWhile.saturatingCountdown_agrees {entry : ResourceState} {depth offset : Nat}
    {threshold amount : UInt8}
    {effects : Operations}
    (positive : 0 < amount.toNat)
    (canRead canSubtract) (update : CounterUpdate entry depth offset amount
      (.subtractFrom (.field offset) (.field offset) amount effects)) (input : ResourceInput entry) (next : Operations) :
    (Operations.countdown offset threshold amount effects next).run depth input.val =
      next.run depth ((CheckedWhile.bySaturatingUpdate entry depth offset threshold amount
        positive canRead _ canSubtract update).run input).val := by
  let loop := CheckedWhile.bySaturatingUpdate entry depth offset threshold amount positive canRead _ canSubtract update
  let iterations := IterationCount.countdown threshold amount
  have schedule : ∀ count (state : ResourceInput entry),
      iterations.ofByte (loop.read state).value.toNat = count →
      runRepeat ((Operations.countdownIteration offset amount effects).run depth) count (loop.read state).after.val =
        some (loop.run state).val := by
    intro count
    induction count with
    | zero =>
      intro state none
      have finished : loop.condition (loop.read state).value = false := by
        change decide (threshold.toNat < (loop.read state).value.toNat) = false
        exact decide_eq_false (Nat.not_lt.mpr (countdown_count_zero.mp none))
      rw [CheckedWhile.run]
      simp only [runRepeat, finished, Bool.false_eq_true, dite_false]
    | succ count ih =>
      intro state size
      let observed := loop.read state
      let advanced := loop.advance observed.after
      have entered : threshold.toNat < observed.value.toNat := by
        apply Nat.lt_of_not_ge
        intro ended
        have countZero := countdown_count_zero (amount := amount) |>.mpr ended
        change iterations.ofByte (loop.read state).value.toNat = 0 at countZero
        omega
      have taken : loop.condition observed.value = true := by
        exact decide_eq_true entered
      have updated := update state.property observed.ran advanced.property
      have loaded := AccessTarget.read_current_byte (loop.read advanced.val).ran
      have reflected := Option.some.inj (loaded.symm.trans updated)
      have remaining : iterations.ofByte (loop.read advanced.val).value.toNat = count := by
        rw [reflected, subtractByteSat_toNat]
        have reduced := IterationCount.countdown_step threshold amount positive entered
        change iterations.ofByte ((loop.read state).value.toNat - amount.toNat) + 1 =
          iterations.ofByte (loop.read state).value.toNat at reduced
        rw [size] at reduced
        exact Nat.succ.inj reduced
      have step := countdownIteration_run advanced.property (loop.read advanced.val).ran
      change (Operations.countdownIteration offset amount effects).run depth observed.after.val =
        some (loop.read advanced.val).after.val at step
      rw [CheckedWhile.run]
      change runRepeat ((Operations.countdownIteration offset amount effects).run depth) (count + 1) observed.after.val =
        some (if _ : loop.condition observed.value = true then loop.run advanced.val else observed.after).val
      rw [dite_eq_left taken]
      change ((Operations.countdownIteration offset amount effects).run depth observed.after.val).bind _ = _
      rw [step]
      exact ih advanced.val remaining
  have resolved := schedule (iterations.ofByte (loop.read input).value.toNat) input rfl
  change ((Operations.countdown offset threshold amount effects next).run depth input.val) =
    next.run depth (loop.run input).val
  simp only [Operations.countdown, Operations.run, Place.runRead_field, bind]
  have initial := (loop.read input).ran
  change (AccessTarget.handle offset).readValue input.val =
      some ((loop.read input).value, (loop.read input).after.val) at initial
  rw [initial]
  change (runRepeat ((Operations.countdownIteration offset amount effects).run depth)
    (iterations.ofByte (loop.read input).value.toNat) (loop.read input).after.val).bind
      (next.run depth) = _
  rw [resolved]
  rfl

theorem Operations.countdown_matches_while {offset depth : Nat} {threshold amount : UInt8} {state : State}
    {effects next : Operations}
    (accepted : (Operations.countdown offset threshold amount effects next).check depth state.resources = true)
    (roots : RecordAddresses state) (outside : offset ∉ effects.writes) :
    ∃ steps stopped final,
      WhileExecutes (.handle offset) (fun value => decide (threshold.toNat < value.toNat))
        ((Operations.subtractFrom (.field offset) (.field offset) amount effects).toCode depth (fun _ => .finish) [])
        state steps stopped ∧
      next.run depth stopped = some final ∧
      (Operations.countdown offset threshold amount effects next).run depth state = some final := by
  obtain ⟨positive, read, descend, rest⟩ := Operations.countdown_checked accepted
  have update : CounterUpdate state.resources depth offset amount
      (.subtractFrom (.field offset) (.field offset) amount effects) :=
    afterDecrease_counter (entry := state.resources) (by exact roots) outside
  let loop := CheckedWhile.bySaturatingUpdate state.resources depth offset threshold amount positive read _ descend update
  let input : ResourceInput state.resources := ⟨state, rfl⟩
  obtain ⟨steps, executed⟩ := loop.run_correct input
  let stopped := loop.run input
  have checked : next.check depth stopped.val.resources = true := by
    rw [stopped.property]
    exact rest
  obtain ⟨final, continued, _⟩ := Operations.run_preserves_resources checked
  exact ⟨steps, stopped.val, final, executed, continued,
    (CheckedWhile.saturatingCountdown_agrees positive read descend update input next).trans continued⟩

end Aethel.SourceVerification
