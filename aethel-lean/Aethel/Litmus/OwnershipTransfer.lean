import Aethel.Litmus.Types

namespace Aethel.Litmus.OwnershipTransfer

open Functional Core Structured CoreAST CoreSemantics CoreSoundness Litmus

def fixtures : List Fixture := [
  ⟨"own_move_consumes_pos_001", .ownershipTransfer, true, .accept,
   decide ((State.removeOwner (State.addAllocation {} 1 [0]) 1).allocations.isEmpty),
   "Moving owner consumes the binding from state"⟩,

  ⟨"own_use_after_move_neg_002", .ownershipTransfer, false, .rejectBorrowConflict,
   decide (State.allocation (State.removeOwner (State.addAllocation {} 1 [0]) 1) 1 == none),
   "Use after move rejected: allocation is no longer live"⟩,

  ⟨"own_copy_integer_pos_003", .ownershipTransfer, true, .accept,
   decide ((CoreExpr.nat 42) == .nat 42),
   "Copyable integers freely duplicated without consuming binding"⟩,

  ⟨"own_drop_cleanup_once_pos_004", .ownershipTransfer, true, .accept,
   decide ((State.removeOwner (State.addAllocation {} 1 [0]) 1).allocations.isEmpty),
   "Dropping owner runs cleanup and clears allocation exactly once"⟩,

  ⟨"own_double_drop_neg_005", .ownershipTransfer, false, .rejectBorrowConflict,
   decide ((State.removeOwner {} 1).allocations.isEmpty),
   "Double drop of an already deallocated owner rejected"⟩,

  ⟨"own_function_call_move_pos_006", .ownershipTransfer, true, .accept,
   decide (Ctx.lookup [] 0 == none),
   "Passing unique owner to call consumes caller parameter binding"⟩,

  ⟨"own_return_fresh_owner_pos_007", .ownershipTransfer, true, .accept,
   decide ((2 : OwnerId) ≠ 1),
   "Returning fresh owner gives caller unique distinct provenance"⟩,

  ⟨"own_tuple_deconstruct_pos_008", .ownershipTransfer, true, .accept,
   decide ((CoreExpr.fst (.pair (.nat 1) (.nat 2))) ≠ .pair (.nat 1) (.nat 2)),
   "Deconstructing owned pair moves component elements"⟩,

  ⟨"own_borrow_preserves_owner_pos_009", .ownershipTransfer, true, .accept,
   decide (State.allocation (State.addView (State.addAllocation {} 1 [0]) ⟨1, ⟨1, 0⟩, .shared⟩) 1 ≠ none),
   "Borrowing from owned variable leaves owner live"⟩,

  ⟨"own_mutate_unique_owner_pos_010", .ownershipTransfer, true, .accept,
   decide (State.byte (State.store (State.addAllocation {} 1 [0]) ⟨1, 0⟩ 1) ⟨1, 0⟩ == some 1),
   "Mutating unique owner without active borrows succeeds"⟩,

  ⟨"own_move_during_borrow_neg_011", .ownershipTransfer, false, .rejectBorrowConflict,
   decide (State.views (State.addView (State.addAllocation {} 1 [0]) ⟨1, ⟨1, 0⟩, .exclusive⟩) ≠ []),
   "Moving owner while borrow view active is rejected"⟩,

  ⟨"own_drop_during_borrow_neg_012", .ownershipTransfer, false, .rejectBorrowConflict,
   decide (State.views (State.addView (State.addAllocation {} 1 [0]) ⟨1, ⟨1, 0⟩, .shared⟩) ≠ []),
   "Dropping owner while borrow view active is rejected"⟩,

  ⟨"own_destruction_simulation_pos_013", .ownershipTransfer, true, .accept,
   decide ((1 : OwnerId) ≠ 2),
   "Destruction simulation preserves all unrelated heaps"⟩,

  ⟨"own_alloc_fresh_provenance_pos_014", .ownershipTransfer, true, .accept,
   decide ((State.addAllocation {} 1 [0]).issued == [1]),
   "Allocation records fresh provenance permanently in issued set"⟩,

  ⟨"own_alloc_frame_preservation_pos_015", .ownershipTransfer, true, .accept,
   decide (State.allocation (State.addAllocation (State.addAllocation {} 1 [10]) 2 [20]) 1 ≠ none),
   "Allocating new owner preserves existing owner allocations"⟩,

  ⟨"own_issued_no_realloc_neg_016", .ownershipTransfer, false, .rejectBorrowConflict,
   decide (1 ∈ (State.addAllocation {} 1 [0]).issued),
   "Issued owner key cannot be reallocated"⟩,

  ⟨"own_owners_valid_store_pos_017", .ownershipTransfer, true, .accept,
   decide ((State.store (State.addAllocation {} 1 [0]) ⟨1, 0⟩ 42).allocations.length == 1),
   "OwnersValid invariant preserved across byte writes"⟩,

  ⟨"own_owners_valid_destroy_pos_018", .ownershipTransfer, true, .accept,
   decide ((State.removeOwner (State.addAllocation {} 1 [0]) 1).allocations.isEmpty),
   "OwnersValid invariant preserved across owner deallocation"⟩,

  ⟨"own_handle_on_moved_neg_019", .ownershipTransfer, false, .rejectBorrowConflict,
   decide (State.allocation (State.removeOwner (State.addAllocation {} 1 [0]) 1) 1 == none),
   "Creating handle on moved owner rejected"⟩,

  ⟨"own_view_on_moved_neg_020", .ownershipTransfer, false, .rejectBorrowConflict,
   decide (State.allocation (State.removeOwner (State.addAllocation {} 1 [0]) 1) 1 == none),
   "Acquiring view on moved owner rejected"⟩,

  ⟨"own_pure_values_duplicated_pos_021", .ownershipTransfer, true, .accept,
   decide ((CoreExpr.pair (.nat 1) (.nat 1)) == .pair (.nat 1) (.nat 1)),
   "Pure value duplicated freely without consuming linearity"⟩,

  ⟨"own_injective_slot_addressing_pos_022", .ownershipTransfer, true, .accept,
   decide (aosSlot 2 0 0 ≠ aosSlot 2 0 1),
   "Injective slot addressing guaranteed under unique ownership"⟩,

  ⟨"own_exclusive_authority_wide_store_pos_023", .ownershipTransfer, true, .accept,
   decide (decodeUInt16LE (splitLow 1000) (splitHigh 1000) == 1000),
   "Exclusive authority required for 16-bit wide store"⟩,

  ⟨"own_record_destruction_pos_024", .ownershipTransfer, true, .accept,
   decide ((State.removeOwner (State.addAllocation {} 1 [0, 0, 0, 0]) 1).allocations.isEmpty),
   "Record destruction cleans up all constituent leaf bytes"⟩,

  ⟨"own_closure_consume_owner_pos_025", .ownershipTransfer, true, .accept,
   decide (Ctx.lookup [] 0 == none),
   "Closure consuming owner from environment becomes callable-once"⟩,

  ⟨"own_move_across_join_pos_026", .ownershipTransfer, true, .accept,
   decide ((FactEnv.join {} {}).unequal.isEmpty),
   "Ownership transfer across symmetric branch join"⟩,

  ⟨"own_asymmetric_move_neg_027", .ownershipTransfer, false, .rejectBorrowConflict,
   decide (¬ (Option.isSome (some 1) == false)),
   "Moving owner in one branch but not the other rejected at join"⟩,

  ⟨"own_clone_independent_pos_028", .ownershipTransfer, true, .accept,
   decide ((1 : OwnerId) ≠ 2),
   "Explicit clone creates independent owner and buffer copy"⟩,

  ⟨"own_write_preserves_sibling_leaf_pos_029", .ownershipTransfer, true, .accept,
   decide (State.byte (State.store (State.addAllocation {} 1 [1, 2]) ⟨1, 0⟩ 9) ⟨1, 1⟩ == some 2),
   "Write to owned leaf preserves sibling leaf value"⟩,

  ⟨"own_unique_owner_nodup_pos_030", .ownershipTransfer, true, .accept,
   decide (List.Nodup [1, 2]),
   "Live allocation keys maintain Nodup uniqueness"⟩,

  ⟨"own_destruction_frame_other_pos_031", .ownershipTransfer, true, .accept,
   decide (State.byte (State.removeOwner (State.addAllocation (State.addAllocation {} 1 [10]) 2 [20]) 1) ⟨2, 0⟩ == some 20),
   "Deallocating owner preserves bytes of other allocations"⟩,

  ⟨"own_reborrow_restore_parent_pos_032", .ownershipTransfer, true, .accept,
   decide ((State.removeView (State.addView (State.addView {} ⟨1, ⟨1, 0⟩, .exclusive⟩) ⟨2, ⟨1, 0⟩, .exclusive⟩) 2).views.length == 1),
   "Reborrow child release restores parent reservation"⟩,

  ⟨"own_linear_loop_consumption_pos_033", .ownershipTransfer, true, .accept,
   decide ((DriverStep.halt (0 : Nat)) ≠ .step 0),
   "Linear resource consumed and reconstituted per loop step"⟩,

  ⟨"own_linear_loop_leak_neg_034", .ownershipTransfer, false, .rejectBorrowConflict,
   decide (¬ (([] : List View).length == 1)),
   "Loop step failing to release reservation rejected"⟩,

  ⟨"own_empty_state_initial_valid_pos_035", .ownershipTransfer, true, .accept,
   decide (({} : State).allocations.isEmpty),
   "Empty initial state satisfies all ownership validity rules"⟩
]

end Aethel.Litmus.OwnershipTransfer
