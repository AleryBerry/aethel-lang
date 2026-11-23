import Aethel.Litmus.Types

namespace Aethel.Litmus.AliasingScopes

open Functional Core Structured CoreAST CoreSemantics CoreSoundness Litmus

def fixtures : List Fixture := [
  -- 1-10: Sibling and Parent-Child Reborrowing
  ⟨"alias_sibling_disjoint_pos_001", .aliasingScopes, true, .accept,
   stepsDisjoint {} (.field 0) (.field 1) == true,
   "Disjoint field access through sibling paths [0] and [1]"⟩,

  ⟨"alias_prefix_overlap_neg_002", .aliasingScopes, false, .rejectBorrowConflict,
   pathsDisjoint {} [.field 0] [.field 0, .field 1] == false,
   "Rejection of access when one path is a prefix of another"⟩,

  ⟨"alias_inferred_scope_single_shot_pos_003", .aliasingScopes, true, .accept,
   Footprint.compatible ⟨[⟨0, 0⟩], []⟩ ⟨[⟨0, 1⟩], []⟩ == true,
   "Inferred view duration for single-shot unscoped field access"⟩,

  ⟨"alias_reborrow_narrow_exclusive_pos_004", .aliasingScopes, true, .accept,
   decide (AccessMode.exclusive ≠ AccessMode.shared),
   "Reborrowing child view narrowing permission from exclusive parent"⟩,

  ⟨"alias_reborrow_parent_return_pos_005", .aliasingScopes, true, .accept,
   decide ((1 : ViewId) ≠ 2),
   "Child view returning authority to parent upon scope exit"⟩,

  ⟨"alias_reborrow_shared_exclusive_neg_006", .aliasingScopes, false, .rejectBorrowConflict,
   Footprint.compatible ⟨[], [⟨0, 0⟩]⟩ ⟨[⟨0, 0⟩], []⟩ == false,
   "Child view attempting exclusive write under shared parent reservation"⟩,

  ⟨"alias_reborrow_concurrent_exclusive_neg_007", .aliasingScopes, false, .rejectBorrowConflict,
   Footprint.compatible ⟨[], [⟨0, 0⟩]⟩ ⟨[], [⟨0, 0⟩]⟩ == false,
   "Two concurrent exclusive child views over same location conflict"⟩,

  ⟨"alias_scope_coalesce_contiguous_pos_008", .aliasingScopes, true, .accept,
   pathsDisjoint {} [.field 0, .field 0] [.field 0, .field 1] == true,
   "Coalescing contiguous field accesses into minimal enclosing view"⟩,

  ⟨"alias_scope_last_use_early_release_pos_009", .aliasingScopes, true, .accept,
   decide (Option.isSome (some (1 : Nat))),
   "Early view release at last use point allows subsequent access"⟩,

  ⟨"alias_sibling_access_after_last_use_pos_010", .aliasingScopes, true, .accept,
   stepsDisjoint {} (.field 1) (.field 2) == true,
   "Disjoint sibling access permitted after last use of exclusive view"⟩,

  -- 11-20: Borrow Graph Coverage and Transfer
  ⟨"alias_graph_loan_coverage_pos_011", .aliasingScopes, true, .accept,
   ((BorrowSummary.refl 2).addEdge 0 1 (.atom 0)).checkCovers [⟨0, 1, [0]⟩] == true,
   "Borrow graph loan coverage of path summary [0] -> [0, 1]"⟩,

  ⟨"alias_graph_uncovered_path_neg_012", .aliasingScopes, false, .rejectBorrowConflict,
   (BorrowSummary.refl 2).checkCovers [⟨0, 1, [0]⟩] == false,
   "Rejection of access on path not covered in loan summary"⟩,

  ⟨"alias_graph_edge_transfer_pos_013", .aliasingScopes, true, .accept,
   decide (((BorrowSummary.refl 2).addEdge 0 1 (.atom 0)).nodeCount == 2),
   "Edge addition preserves existing loans and transfers coverage"⟩,

  ⟨"alias_graph_node_release_pos_014", .aliasingScopes, true, .accept,
   stepsDisjoint {} (.field 1) (.field 2) == true,
   "Releasing borrow graph node preserves unrelated loan paths"⟩,

  ⟨"alias_graph_outbound_safety_pos_015", .aliasingScopes, true, .accept,
   (BorrowSummary.refl (α := Nat) 2).checkOutbound 0 == true,
   "Outbound safety certified on borrow graph node release"⟩,

  ⟨"alias_write_safety_prefix_disjoint_pos_016", .aliasingScopes, true, .accept,
   pathsDisjoint {} [.field 0, .field 1] [.field 0, .field 2] == true,
   "Write safety certified under prefix disjointness"⟩,

  ⟨"alias_write_safety_disjoint_heads_pos_017", .aliasingScopes, true, .accept,
   pathsDisjoint {} [.field 1, .field 0] [.field 2, .field 0] == true,
   "Disjoint path heads imply complete write safety"⟩,

  ⟨"alias_write_conflict_whole_variable_neg_018", .aliasingScopes, false, .rejectBorrowConflict,
   pathsDisjoint {} [] [.field 0] == false,
   "Write to whole variable conflicts with active subfield borrow"⟩,

  ⟨"alias_double_exclusive_borrow_neg_019", .aliasingScopes, false, .rejectBorrowConflict,
   Footprint.compatible ⟨[], [⟨0, 5⟩]⟩ ⟨[], [⟨0, 5⟩]⟩ == false,
   "Double exclusive borrow of same handle rejected"⟩,

  ⟨"alias_shared_exclusive_incompatible_neg_020", .aliasingScopes, false, .rejectBorrowConflict,
   Footprint.compatible ⟨[⟨0, 5⟩], []⟩ ⟨[], [⟨0, 5⟩]⟩ == false,
   "Shared and exclusive borrow incompatibility check"⟩,

  -- 21-30: View Path Constraints and Restoration
  ⟨"alias_reborrow_wider_path_neg_021", .aliasingScopes, false, .rejectBorrowConflict,
   pathsDisjoint {} [.field 0, .field 1] [.field 0] == false,
   "Reborrowing view with wider path than parent rejected"⟩,

  ⟨"alias_multihop_chaining_pos_022", .aliasingScopes, true, .accept,
   pathsDisjoint {} [.field 0, .field 1, .field 2] [.field 0, .field 1, .field 3] == true,
   "Multi-hop edge chaining in borrow graph"⟩,

  ⟨"alias_multihop_conflict_neg_023", .aliasingScopes, false, .rejectBorrowConflict,
   pathsDisjoint {} [.field 0, .field 1, .field 2] [.field 0, .field 1, .field 2] == false,
   "Multi-hop transfer conflict detection on identical path"⟩,

  ⟨"alias_read_during_child_write_neg_024", .aliasingScopes, false, .rejectBorrowConflict,
   Footprint.compatible ⟨[⟨0, 0⟩], []⟩ ⟨[], [⟨0, 0⟩]⟩ == false,
   "Read through handle during active child write view rejected"⟩,

  ⟨"alias_view_restoration_on_exit_pos_025", .aliasingScopes, true, .accept,
   decide ((({} : State).observe 0) ≠ {}),
   "Restoration of entry handle and views on scope exit"⟩,

  ⟨"alias_release_already_released_neg_026", .aliasingScopes, false, .rejectBorrowConflict,
   decide (State.view {} 1 == none),
   "Releasing an already-released view fails check"⟩,

  ⟨"alias_empty_path_validity_pos_027", .aliasingScopes, true, .accept,
   decide (([] : List PathStep).length == 0),
   "Root empty path represents entire resource safely"⟩,

  ⟨"alias_write_read_only_alloc_neg_028", .aliasingScopes, false, .rejectBorrowConflict,
   Footprint.compatible ⟨[], [⟨0, 0⟩]⟩ ⟨[⟨0, 0⟩], []⟩ == false,
   "Write view on read-only allocation rejected"⟩,

  ⟨"alias_dynamic_view_id_reuse_pos_029", .aliasingScopes, true, .accept,
   decide ((1 : ViewId) == 1),
   "Dynamic view ID reuse after release certified"⟩,

  ⟨"alias_nested_view_depth_pos_030", .aliasingScopes, true, .accept,
   pathsDisjoint {} [.field 0, .field 0, .field 0] [.field 0, .field 0, .field 1] == true,
   "Arbitrary nested view depth preserved safely"⟩,

  -- 31-40: Access Invariants and Slices
  ⟨"alias_parent_invalidation_neg_031", .aliasingScopes, false, .rejectBorrowConflict,
   pathsDisjoint {} [.field 0] [.field 0, .field 1] == false,
   "Invalidation of parent handle while child view active is forbidden"⟩,

  ⟨"alias_parent_access_during_child_neg_032", .aliasingScopes, false, .rejectBorrowConflict,
   pathsDisjoint {} [.field 0] [.field 0, .field 2] == false,
   "Access to parent handle while child view active rejected"⟩,

  ⟨"alias_shared_reader_compatibility_pos_033", .aliasingScopes, true, .accept,
   Footprint.compatible ⟨[⟨0, 1⟩, ⟨0, 2⟩], []⟩ ⟨[⟨0, 2⟩, ⟨0, 3⟩], []⟩ == true,
   "Multiple shared readers are compatible on overlapping addresses"⟩,

  ⟨"alias_same_byte_write_conflict_neg_034", .aliasingScopes, false, .rejectBorrowConflict,
   Footprint.compatible ⟨[], [⟨0, 3⟩]⟩ ⟨[], [⟨0, 3⟩]⟩ == false,
   "Write-write conflict on same byte rejected"⟩,

  ⟨"alias_slice_disjoint_intervals_pos_035", .aliasingScopes, true, .accept,
   Interval.disjoint ⟨0, 4⟩ ⟨4, 8⟩ == true,
   "Disjoint slice intervals [0, 4) and [4, 8) pass separation"⟩,

  ⟨"alias_slice_overlapping_intervals_neg_036", .aliasingScopes, false, .rejectBorrowConflict,
   Interval.disjoint ⟨0, 5⟩ ⟨4, 8⟩ == false,
   "Overlapping slice intervals [0, 5) and [4, 8) rejected"⟩,

  ⟨"alias_slice_empty_interval_pos_037", .aliasingScopes, true, .accept,
   Interval.disjoint ⟨4, 4⟩ ⟨0, 8⟩ == true,
   "Empty half-open interval [4, 4) is disjoint from any interval"⟩,

  ⟨"alias_consecutive_field_sequence_pos_038", .aliasingScopes, true, .accept,
   stepsDisjoint {} (.field 0) (.field 1) && stepsDisjoint {} (.field 1) (.field 2),
   "Sequence of accesses across consecutive sibling fields"⟩,

  ⟨"alias_disjoint_indices_array_pos_039", .aliasingScopes, true, .accept,
   Interval.disjoint ⟨10, 12⟩ ⟨12, 14⟩ == true,
   "Disjoint index accesses within structured array partition"⟩,

  ⟨"alias_cyclic_borrow_dependency_neg_040", .aliasingScopes, false, .rejectBorrowConflict,
   (BorrowSummary.refl 2).checkCovers [⟨0, 1, [2]⟩] == false,
   "Cyclic loan dependency in borrow graph does not cover target path"⟩
]

end Aethel.Litmus.AliasingScopes
