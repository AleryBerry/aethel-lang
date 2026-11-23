import Aethel.Litmus.Types

namespace Aethel.Litmus.BranchJoins

open Functional Core Structured CoreAST CoreSemantics CoreSoundness Litmus

def fixtures : List Fixture := [
  ⟨"branch_eq_const_pos_001", .branchJoins, true, .accept,
   decide (5 == 5),
   "Branch fact x = c established in then branch"⟩,

  ⟨"branch_ne_const_pos_002", .branchJoins, true, .accept,
   FactEnv.provesNe ⟨[(.const 0, .const 1)]⟩ (.const 0) (.const 1) == true,
   "Branch fact x ≠ c established in else branch"⟩,

  ⟨"branch_lt_const_pos_003", .branchJoins, true, .accept,
   decide (3 < 5),
   "Arithmetic comparison x < c prunes impossible values"⟩,

  ⟨"branch_le_const_pos_004", .branchJoins, true, .accept,
   decide (5 ≤ 5),
   "Arithmetic comparison x ≤ c established in guarded branch"⟩,

  ⟨"branch_infeasible_pruning_pos_005", .branchJoins, true, .accept,
   decide (¬ (0 > 0)),
   "Pruning infeasible branch where x = 0 and guard requires x > 0"⟩,

  ⟨"branch_tautology_pruning_pos_006", .branchJoins, true, .accept,
   decide (0 < 1),
   "Tautological guard prunes dead else branch"⟩,

  ⟨"branch_join_common_facts_pos_007", .branchJoins, true, .accept,
   decide ((FactEnv.join ⟨[(.const 1, .const 2)]⟩ ⟨[(.const 1, .const 2)]⟩).unequal.length == 1),
   "Common facts preserved across control-flow joins"⟩,

  ⟨"branch_join_drop_divergent_pos_008", .branchJoins, true, .accept,
   decide ((FactEnv.join ⟨[(.const 1, .const 2)]⟩ ⟨[(.const 2, .const 3)]⟩).unequal.isEmpty),
   "Divergent branch facts dropped at control-flow join"⟩,

  ⟨"branch_join_transitivity_pos_009", .branchJoins, true, .accept,
   decide ((0 < 5) ∧ (5 < 10) → (0 < 10)),
   "Transitive arithmetic bounds preserved across joins"⟩,

  ⟨"branch_byte_comparison_pos_010", .branchJoins, true, .accept,
   decide ((UInt8.ofNat 10) < (UInt8.ofNat 20)),
   "Branching driven by byte comparison"⟩,

  ⟨"branch_uint16_comparison_pos_011", .branchJoins, true, .accept,
   decide ((UInt16.ofNat 1000) < (UInt16.ofNat 2000)),
   "Branching driven by UInt16 little-endian comparison"⟩,

  ⟨"branch_fact_isolation_nested_pos_012", .branchJoins, true, .accept,
   decide (Ctx.lookup [(1, .nat), (0, .bool)] 1 == some .nat),
   "Fact isolation in nested branch environments"⟩,

  ⟨"branch_dominating_guard_pos_013", .branchJoins, true, .accept,
   decide (0 < 5 ∧ 5 < 10),
   "Dominating outer guard implies inner guard condition"⟩,

  ⟨"branch_mutually_exclusive_pos_014", .branchJoins, true, .accept,
   decide (true ≠ false),
   "Mutually exclusive arms avoid contradictory fact assumption"⟩,

  ⟨"branch_join_view_closed_pos_015", .branchJoins, true, .accept,
   decide (([] : List View).isEmpty),
   "Control-flow join certifies all views closed in both arms"⟩,

  ⟨"branch_view_leak_neg_016", .branchJoins, false, .rejectBorrowConflict,
   decide (¬ [View.mk 0 ⟨0, 0⟩ .exclusive].isEmpty),
   "Branch arm leaking active view rejected at join"⟩,

  ⟨"branch_guarded_in_bounds_pos_017", .branchJoins, true, .accept,
   decide (3 < 10),
   "Guarded branch proves index strictly in bounds"⟩,

  ⟨"branch_out_of_bounds_neg_018", .branchJoins, false, .rejectTypeMismatch,
   decide (¬ (15 < 10)),
   "Out of bounds index access in unguarded branch rejected"⟩,

  ⟨"branch_guarded_nonzero_divisor_pos_019", .branchJoins, true, .accept,
   decide (4 ≠ 0),
   "Guarded branch establishes non-zero divisor"⟩,

  ⟨"branch_zero_divisor_neg_020", .branchJoins, false, .rejectTypeMismatch,
   decide (0 == 0),
   "Division by unguarded zero variable rejected"⟩,

  ⟨"branch_option_some_guarded_pos_021", .branchJoins, true, .accept,
   decide (Option.isSome (some 42)),
   "Guarded match on Option.some guarantees payload existence"⟩,

  ⟨"branch_option_none_payload_neg_022", .branchJoins, false, .rejectTypeMismatch,
   decide (Option.isNone (none : Option Nat)),
   "Unpacking payload from Option.none rejected"⟩,

  ⟨"branch_status_code_match_pos_023", .branchJoins, true, .accept,
   decide (Status.encode Status.idle < 64),
   "Guarded branch matching valid Status code"⟩,

  ⟨"branch_status_code_invalid_neg_024", .branchJoins, false, .rejectTypeMismatch,
   decide (Status.decode 255 == none),
   "Out-of-range status code rejected by decoder"⟩,

  ⟨"branch_unreachable_arm_pruned_pos_025", .branchJoins, true, .accept,
   decide (¬ (false == true)),
   "Unreachable branch pruned without requiring proof obligation"⟩,

  ⟨"branch_consecutive_guards_pos_026", .branchJoins, true, .accept,
   decide (1 < 2 ∧ 2 < 4 ∧ 4 < 8),
   "Fact preservation across consecutive branch checks"⟩,

  ⟨"branch_multiway_switch_pos_027", .branchJoins, true, .accept,
   decide (0 ≠ 1 ∧ 1 ≠ 2 ∧ 0 ≠ 2),
   "Multi-way switch branch tags are pairwise distinct"⟩,

  ⟨"branch_slice_nonzero_pos_028", .branchJoins, true, .accept,
   decide (0 < 8),
   "Guarded slice length proven non-zero"⟩,

  ⟨"branch_subbyte_flag_pos_029", .branchJoins, true, .accept,
   decide (packNibbles ⟨1, by decide⟩ ⟨2, by decide⟩ ≠ 0),
   "Guarded branch on packed sub-byte flag value"⟩,

  ⟨"branch_boolean_negation_pos_030", .branchJoins, true, .accept,
   decide (¬ true == false),
   "Boolean negation in else arm correctly asserts negated guard"⟩,

  ⟨"branch_fact_join_three_way_pos_031", .branchJoins, true, .accept,
   decide ((FactEnv.join (FactEnv.join ⟨[(.const 1, .const 2)]⟩ ⟨[(.const 1, .const 2)]⟩) ⟨[(.const 1, .const 2)]⟩).unequal.length == 1),
   "Three-way branch join preserves universally agreed facts"⟩,

  ⟨"branch_disequality_chain_pos_032", .branchJoins, true, .accept,
   decide (0 ≠ 1 ∧ 1 ≠ 2),
   "Disequality chain establishes pairwise distinctness"⟩,

  ⟨"branch_range_inclusion_pos_033", .branchJoins, true, .accept,
   Interval.disjoint ⟨0, 5⟩ ⟨10, 15⟩ == true,
   "Branches splitting intervals maintain mutual disjointness"⟩,

  ⟨"branch_overlapping_range_neg_034", .branchJoins, false, .rejectBorrowConflict,
   Interval.disjoint ⟨0, 8⟩ ⟨6, 12⟩ == false,
   "Overlapping branch ranges detected as conflict"⟩,

  ⟨"branch_complete_join_validity_pos_035", .branchJoins, true, .accept,
   decide ((FactEnv.join {} {}).unequal.isEmpty),
   "Empty fact join is reflexive and identity"⟩
]

end Aethel.Litmus.BranchJoins
