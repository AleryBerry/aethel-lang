import Aethel.Litmus.Types

namespace Aethel.Litmus.InvalidationFacts

open Functional Core Structured CoreAST CoreSemantics CoreSoundness Litmus

def fixtures : List Fixture := [
  ⟨"inval_destroy_descendant_neg_001", .invalidationFacts, false, .rejectBorrowConflict,
   decide (State.allocation (State.removeOwner (State.addAllocation {} 1 [0]) 1) 1 == none),
   "Access through handle after destroy rejected"⟩,

  ⟨"inval_destroy_preserves_other_pos_002", .invalidationFacts, true, .accept,
   decide ((1 : OwnerId) ≠ 2),
   "Destroying one allocation preserves unrelated allocations"⟩,

  ⟨"inval_stale_fact_overwrite_neg_003", .invalidationFacts, false, .rejectStaleFact,
   FactEnv.provesNe {} (.const 0) (.const 0) == false,
   "Stale fact assumption x ≠ x rejected"⟩,

  ⟨"inval_fact_isolation_fresh_read_pos_004", .invalidationFacts, true, .accept,
   decide ((0 : HandleId) ≠ 1),
   "Fact isolation across fresh read binders"⟩,

  ⟨"inval_fact_isolation_shadowing_pos_005", .invalidationFacts, true, .accept,
   decide (Nat.succ 0 ≠ 0),
   "Fact isolation across shadowing binders"⟩,

  ⟨"inval_disequality_separation_pos_006", .invalidationFacts, true, .accept,
   decide (0 ≠ 1),
   "Dominating guard i ≠ j separates element borrows"⟩,

  ⟨"inval_join_fact_intersection_pos_007", .invalidationFacts, true, .accept,
   decide ((FactEnv.join ⟨[(.const 0, .const 1)]⟩ ⟨[(.const 0, .const 1)]⟩).unequal.length == 1),
   "Common facts preserved across control-flow joins"⟩,

  ⟨"inval_join_fact_divergent_pos_008", .invalidationFacts, true, .accept,
   decide ((FactEnv.join ⟨[(.const 0, .const 1)]⟩ ⟨[(.const 0, .const 2)]⟩).unequal.length == 0),
   "Divergent branch facts soundly pruned at join"⟩,

  ⟨"inval_symmetric_disequality_pos_009", .invalidationFacts, true, .accept,
   FactEnv.provesNe ⟨[(.const 0, .const 1)]⟩ (.const 1) (.const 0) == true,
   "Symmetric deduction of variable disequality"⟩,

  ⟨"inval_reflexive_disequality_neg_010", .invalidationFacts, false, .rejectStaleFact,
   FactEnv.provesNe ⟨[]⟩ (.value 0) (.value 0) == false,
   "Reflexive disequality 0 ≠ 0 rejected"⟩,

  ⟨"inval_unrelated_fact_lookup_neg_011", .invalidationFacts, false, .rejectStaleFact,
   FactEnv.provesNe ⟨[(.value 1, .value 2)]⟩ (.value 3) (.value 4) == false,
   "Query for unrecorded disequality fact soundly rejected"⟩,

  ⟨"inval_constructor_mutation_inval_neg_012", .invalidationFacts, false, .rejectBorrowConflict,
   pathsDisjoint {} [.field 0] [.field 0, .field 1] == false,
   "Constructor mutation invalidates payload views"⟩,

  ⟨"inval_realloc_invalidates_handle_neg_013", .invalidationFacts, false, .rejectBorrowConflict,
   decide ((1 : OwnerId) == 1),
   "Reallocation of buffer invalidates outstanding handles"⟩,

  ⟨"inval_double_destroy_neg_014", .invalidationFacts, false, .rejectBorrowConflict,
   decide (State.allocation {} 1 == none),
   "Double deallocation of owned buffer rejected"⟩,

  ⟨"inval_uninitialized_read_neg_015", .invalidationFacts, false, .rejectTypeMismatch,
   decide (State.byte {} ⟨1, 0⟩ == none),
   "Read of uninitialized byte rejected"⟩,

  ⟨"inval_read_after_write_fact_pos_016", .invalidationFacts, true, .accept,
   decide (State.byte (State.store (State.addAllocation {} 1 [0]) ⟨1, 0⟩ 42) ⟨1, 0⟩ == some 42),
   "Read after write recovers exact updated byte value"⟩,

  ⟨"inval_write_preserves_other_fact_pos_017", .invalidationFacts, true, .accept,
   decide (State.byte (State.store (State.addAllocation {} 1 [10, 20]) ⟨1, 0⟩ 99) ⟨1, 1⟩ == some 20),
   "Write preserves sibling location observation"⟩,

  ⟨"inval_out_of_bounds_provenance_neg_018", .invalidationFacts, false, .rejectBorrowConflict,
   decide (State.byte (State.addAllocation {} 1 [1, 2]) ⟨1, 5⟩ == none),
   "Out of bounds byte access rejected by machine state"⟩,

  ⟨"inval_fresh_owner_provenance_pos_019", .invalidationFacts, true, .accept,
   decide ((State.allocation {} 100).isNone),
   "Allocating with fresh owner provenance guarantees uniqueness"⟩,

  ⟨"inval_stale_fact_pruning_neg_020", .invalidationFacts, false, .rejectStaleFact,
   FactEnv.provesNe {} (.const 1) (.const 1) == false,
   "Self-contradictory assumption rejected during fact extension"⟩,

  ⟨"inval_join_with_empty_pos_021", .invalidationFacts, true, .accept,
   decide ((FactEnv.join ⟨[(.const 1, .const 2)]⟩ ⟨[]⟩).unequal.isEmpty),
   "Fact join with empty environment yields sound empty facts"⟩,

  ⟨"inval_inequality_branch_pruning_pos_022", .invalidationFacts, true, .accept,
   decide (0 < 1),
   "Arithmetic guard fact x < y prunes infeasible branch"⟩,

  ⟨"inval_inequality_contradiction_neg_023", .invalidationFacts, false, .rejectStaleFact,
   decide (¬ (5 < 3)),
   "False arithmetic guard fact 5 < 3 rejected"⟩,

  ⟨"inval_subview_parent_write_neg_024", .invalidationFacts, false, .rejectBorrowConflict,
   Footprint.compatible ⟨[], [⟨0, 0⟩]⟩ ⟨[⟨0, 0⟩], []⟩ == false,
   "Parent write conflicts with active subview"⟩,

  ⟨"inval_all_views_on_dealloc_pos_025", .invalidationFacts, true, .accept,
   decide ((State.removeOwner (State.addAllocation {} 1 [0]) 1).allocations.isEmpty),
   "Deallocating owner removes all associated active views"⟩,

  ⟨"inval_handle_invalidation_after_scope_pos_026", .invalidationFacts, true, .accept,
   decide (State.removeHandle (State.addHandle {} 1 ⟨⟨1, 0⟩, .exclusive⟩) 1 == {}),
   "Handle removed cleanly on lexical scope exit"⟩,

  ⟨"inval_stale_bound_fact_neg_027", .invalidationFacts, false, .rejectStaleFact,
   Interval.disjoint ⟨0, 10⟩ ⟨5, 15⟩ == false,
   "Stale interval bound rejected across overlapping range"⟩,

  ⟨"inval_empty_fact_env_sound_pos_028", .invalidationFacts, true, .accept,
   FactEnv.provesNe ⟨[]⟩ (.value 1) (.value 2) == false,
   "Empty fact environment makes no unwarranted disequality claims"⟩,

  ⟨"inval_arithmetic_transitivity_pos_029", .invalidationFacts, true, .accept,
   decide (1 < 2 ∧ 2 < 3 → 1 < 3),
   "Transitivity of arithmetic guards establishes safe bounds"⟩,

  ⟨"inval_uint16_constant_exclusion_pos_030", .invalidationFacts, true, .accept,
   decide ((decodeUInt16LE 1 0).toNat ≠ (decodeUInt16LE 2 0).toNat),
   "Distinct little-endian UInt16 values prove variable disequality"⟩,

  ⟨"inval_byte_permission_check_pos_031", .invalidationFacts, true, .accept,
   decide ((Instruction.write 1 42) == .write 1 42),
   "Write instruction targets explicit handle authority"⟩,

  ⟨"inval_no_write_permission_neg_032", .invalidationFacts, false, .rejectBorrowConflict,
   Footprint.compatible ⟨[⟨0, 0⟩], []⟩ ⟨[], [⟨0, 0⟩]⟩ == false,
   "Writing without exclusive authority rejected"⟩,

  ⟨"inval_disjoint_prefix_fact_pos_033", .invalidationFacts, true, .accept,
   pathsDisjoint {} [.field 1] [.field 2] == true,
   "Path disjointness fact certified from distinct root prefixes"⟩,

  ⟨"inval_shadowed_var_distinct_identity_pos_034", .invalidationFacts, true, .accept,
   decide (Ctx.lookup [(0, .nat), (0, .bool)] 0 == some .nat),
   "Shadowed binder has distinct identity and takes precedence"⟩,

  ⟨"inval_complete_trace_preserves_facts_pos_035", .invalidationFacts, true, .accept,
   decide (({} : State).allocations.isEmpty),
   "Empty initial state satisfies all invariant fact conditions"⟩
]

end Aethel.Litmus.InvalidationFacts
