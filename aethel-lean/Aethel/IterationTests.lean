import Aethel.Iteration
import Aethel.SourceLoops

namespace Aethel.Iteration.Tests

open Core SourceVerification

private def runSourceCountdownTests : IO Unit := do
  let state := (({} : State).addAllocation 0 [7, 44]).addHandle 0 ⟨⟨0, 0⟩, .exclusive⟩
  let initial := state.addView ⟨0, ⟨0, 1⟩, .shared⟩
  let some loop := checkSaturatingCountdown initial.resources 1 0 3
    | throw (IO.userError "Well-founded source countdown rejected a disjoint live view")
  let final := (loop.run ⟨initial, rfl⟩).val
  if final.observations != [0, 1, 1, 4, 4, 7, 7] || final.byte ⟨0, 0⟩ != some 0 ||
      final.byte ⟨0, 1⟩ != some 44 || final.views != initial.views then
    throw (IO.userError "Well-founded source countdown changed its guard trace or caller frame")
  if (Operations.countdown 0 0 3 .done .done).run 1 initial != some final then
    throw (IO.userError "Compact source countdown changed the number of saturated steps or guard reads")
  if (checkSaturatingCountdown initial.resources 1 0 0).isSome then
    throw (IO.userError "Zero decrement accepted as a termination measure")
  let blocked := state.addView ⟨0, ⟨0, 0⟩, .shared⟩
  if (checkSaturatingCountdown blocked.resources 1 0 3).isSome then
    throw (IO.userError "Well-founded source countdown accepted a write through a conflicting view")
  IO.println "4 source-operation countdown regressions passed"

structure LoopState where
  count : Nat
  acc : Nat
  deriving Repr, DecidableEq

def runIterationTests : IO Unit := do
  -- Test 1: drive with 0 fuel returns pending
  let stepHalt (s : Nat) : DriverStep Nat := .halt (s + 1)
  match drive 0 stepHalt 10 with
  | .pending s =>
    if s != 10 then
      throw (IO.userError "drive 0 should return pending initial state")
  | _ => throw (IO.userError "drive 0 should return pending")

  -- Test 2: drive with 1 fuel on halting step returns finished
  match drive 1 stepHalt 10 with
  | .finished s =>
    if s != 11 then
      throw (IO.userError "drive halt should return final state 11")
  | _ => throw (IO.userError "drive halt should finish")

  -- Test 3: drive with failing step returns error
  let stepFail (_s : Nat) : DriverStep Nat := .fail "aborted"
  match drive 1 stepFail 10 with
  | .error msg =>
    if msg != "aborted" then
      throw (IO.userError "drive fail reason mismatch")
  | _ => throw (IO.userError "drive fail should error")

  -- Test 4: multi-step countdown
  let stepDown (s : Nat) : DriverStep Nat :=
    if s > 0 then .step (s - 1) else .halt 0
  match drive 5 stepDown 3 with
  | .finished s =>
    if s != 0 then
      throw (IO.userError "stepDown should finish at 0")
  | _ => throw (IO.userError "stepDown should finish")

  -- Test 5: insufficient fuel returns pending with intermediate state
  match drive 2 stepDown 5 with
  | .pending s =>
    if s != 3 then
      throw (IO.userError "stepDown with fuel 2 on 5 should leave pending 3")
  | _ => throw (IO.userError "insufficient fuel should be pending")

  -- Test 6: structured loopStep on LoopState
  let cond (s : LoopState) : Bool := s.count > 0
  let body (s : LoopState) : LoopState := ⟨s.count - 1, s.acc + 2⟩
  let initState : LoopState := ⟨4, 0⟩
  let loopDriver := loopStep cond body
  match drive 10 loopDriver initState with
  | .finished finalState =>
    if finalState.count != 0 || finalState.acc != 8 then
      throw (IO.userError "loopStep execution produced wrong state")
  | _ => throw (IO.userError "loopStep should finish with fuel 10")

  -- Test 7: loopStep exit condition is false
  match drive 10 loopDriver initState with
  | .finished finalState =>
    if cond finalState != false then
      throw (IO.userError "loop exit condition must be false")
  | _ => throw (IO.userError "expected finished loop")

  -- Test 8: well-founded loopWF on LoopState
  let measure (s : LoopState) : Nat := s.count
  have hProgress : ∀ s, cond s = true → measure (body s) < measure s := by
    intro s hc
    cases s
    dsimp [cond] at hc
    simp only [decide_eq_true_eq] at hc
    dsimp [measure, body]
    omega
  let wfResult := loopWF body cond measure hProgress initState
  if wfResult.count != 0 || wfResult.acc != 8 then
    throw (IO.userError "loopWF produced wrong result")

  -- Test 9: loopWF exit condition is false
  if cond wfResult != false then
    throw (IO.userError "loopWF exit condition must be false")

  -- Test 10: drive_loop_eq_loopWF equivalence
  -- measure initState = 4, fuel = 5 > 4
  have hFuel : measure initState < 5 := by decide
  have hEq := drive_loop_eq_loopWF body cond measure hProgress initState 5 hFuel
  match drive 5 loopDriver initState with
  | .finished s =>
    if s != wfResult then
      throw (IO.userError "drive result does not match loopWF result")
  | _ => throw (IO.userError "drive with fuel > measure must finish")

  IO.println "10 bounded driver and well-founded loop iteration regressions passed"
  runSourceCountdownTests

end Aethel.Iteration.Tests
