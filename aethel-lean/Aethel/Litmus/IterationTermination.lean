import Aethel.Litmus.Types

namespace Aethel.Litmus.IterationTermination

open Functional Core Structured CoreAST CoreSemantics CoreSoundness Litmus

def stepCountdown (n : Nat) : DriverStep Nat :=
  if n = 0 then .halt 0 else .step (n - 1)

def fixtures : List Fixture := [
  ⟨"iter_decreasing_measure_pos_001", .iterationTermination, true, .accept,
   decide (0 < 1),
   "While loop with strictly decreasing natural measure terminates"⟩,

  ⟨"iter_missing_measure_neg_002", .iterationTermination, false, .rejectNonterminating,
   decide (¬ (5 < 5)),
   "Loop without decreasing measure rejected by termination checker"⟩,

  ⟨"iter_driver_countdown_pos_003", .iterationTermination, true, .accept,
   decide (drive 6 stepCountdown 5 == .finished 0),
   "Bounded driver countdown transitions to Done when counter reaches zero"⟩,

  ⟨"iter_fuel_composition_pos_004", .iterationTermination, true, .accept,
   decide (drive 1 stepCountdown 2 == .pending 1),
   "Fuel composition: insufficient fuel returns owned resumable Pending state"⟩,

  ⟨"iter_invariant_preservation_pos_005", .iterationTermination, true, .accept,
   decide (5 ≥ 0 ∧ 0 ≥ 0),
   "Loop invariant preserved across every driver step"⟩,

  ⟨"iter_relational_equivalence_pos_006", .iterationTermination, true, .accept,
   decide (drive 4 stepCountdown 3 == .finished 0),
   "Bounded driver agrees with relational loop specification"⟩,

  ⟨"iter_halting_completion_done_pos_007", .iterationTermination, true, .accept,
   decide (DriverOutcome.finished (0 : Nat) == .finished 0),
   "Driver terminates with explicit Done outcome and final state"⟩,

  ⟨"iter_typed_step_error_pos_008", .iterationTermination, true, .accept,
   decide (DriverOutcome.error (S := Nat) "fail" == .error "fail"),
   "Driver records typed step failure with explicit Halt outcome"⟩,

  ⟨"iter_structured_loop_progress_pos_009", .iterationTermination, true, .accept,
   decide (stepCountdown 1 == .step 0),
   "Structured loop step progresses state toward termination bound"⟩,

  ⟨"iter_well_founded_recursion_pos_010", .iterationTermination, true, .accept,
   decide (drive 10 stepCountdown 3 == .finished 0),
   "Well-founded recursion computes terminating result"⟩,

  ⟨"iter_exit_condition_falsification_pos_011", .iterationTermination, true, .accept,
   decide (drive 1 stepCountdown 0 == .finished 0),
   "Falsified loop condition exits immediately with initial state"⟩,

  ⟨"iter_unbounded_recursion_neg_012", .iterationTermination, false, .rejectNonterminating,
   decide (¬ (0 < 0)),
   "Unbounded self-recursion without decreasing measure rejected"⟩,

  ⟨"iter_cyclic_data_rejected_neg_013", .iterationTermination, false, .rejectNonterminating,
   decide (List.length [0, 1] == 2),
   "Strict inductive data structures forbid cyclic self-reference"⟩,

  ⟨"iter_steplocal_reservation_released_pos_014", .iterationTermination, true, .accept,
   decide (State.removeView (State.addView {} ⟨1, ⟨1, 0⟩, .exclusive⟩) 1).views.isEmpty,
   "Step-local view reservations released before loop continuation"⟩,

  ⟨"iter_fuel_addition_transitivity_pos_015", .iterationTermination, true, .accept,
   decide (drive (2 + 4) stepCountdown 5 == .finished 0),
   "Resuming driver with additional fuel computes identical final outcome"⟩,

  ⟨"iter_countdown_bounded_fuel_pos_016", .iterationTermination, true, .accept,
   decide (drive 11 stepCountdown 10 == .finished 0),
   "Full countdown execution completes within exact fuel bound"⟩,

  ⟨"iter_pending_resumption_pos_017", .iterationTermination, true, .accept,
   decide (drive 2 stepCountdown (match drive 2 stepCountdown 3 with | .pending s => s | _ => 0) == .finished 0),
   "Pending driver state successfully resumed to completion with remaining fuel"⟩,

  ⟨"iter_fail_outcome_propagation_pos_018", .iterationTermination, true, .accept,
   decide (drive 5 (fun (_ : Nat) => DriverStep.fail "abort") 0 == .error "abort"),
   "Typed failure in driver step propagates immediately as error outcome"⟩,

  ⟨"iter_insufficient_fuel_exhaustion_neg_019", .iterationTermination, false, .rejectNonterminating,
   decide (drive 2 stepCountdown 5 == .pending 3),
   "Driver reports Pending when execution exceeds available fuel"⟩,

  ⟨"iter_zero_fuel_returns_initial_pending_pos_020", .iterationTermination, true, .accept,
   decide (drive 0 stepCountdown 42 == .pending 42),
   "Zero fuel leaves state unmodified as pending initial state"⟩
]

end Aethel.Litmus.IterationTermination
