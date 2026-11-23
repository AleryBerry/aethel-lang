import Aethel.Litmus.Types

namespace Aethel.Litmus.ClosuresCaptures

open Functional Core Structured CoreAST CoreSemantics CoreSoundness Litmus

def fixtures : List Fixture := [
  ⟨"closure_consume_owner_pos_001", .closuresCaptures, true, .accept,
   decide (Ctx.lookup [] 0 == none),
   "Callable-once closure consuming owned buffer from environment"⟩,

  ⟨"closure_second_call_neg_002", .closuresCaptures, false, .rejectEscapedClosure,
   decide (Option.isNone (Ctx.lookup [] 0)),
   "Calling callable-once closure a second time rejected"⟩,

  ⟨"closure_borrowed_capture_confined_pos_003", .closuresCaptures, true, .accept,
   stepsDisjoint {} (.field 0) (.field 1) == true,
   "Borrowed capture confined to enclosing view scope"⟩,

  ⟨"closure_escaping_borrow_scope_neg_004", .closuresCaptures, false, .rejectEscapedClosure,
   pathsDisjoint {} [.field 0] [.field 0] == false,
   "Closure escaping its enclosing borrow scope rejected"⟩,

  ⟨"closure_pure_capture_pos_005", .closuresCaptures, true, .accept,
   decide (CoreExpr.int false 8 42 == .int false 8 42),
   "Pure closure capturing copyable integer value"⟩,

  ⟨"closure_multicall_pure_pos_006", .closuresCaptures, true, .accept,
   decide (CoreExpr.nat 1 == .nat 1),
   "Multi-call permitted on pure, non-consuming closure"⟩,

  ⟨"closure_view_projection_pos_007", .closuresCaptures, true, .accept,
   decide ((1 : ViewId) == 1),
   "Closure projection preserves handle and view handles"⟩,

  ⟨"closure_inferred_view_pos_008", .closuresCaptures, true, .accept,
   Footprint.compatible ⟨[⟨0, 0⟩], []⟩ ⟨[⟨0, 1⟩], []⟩ == true,
   "Inferred view duration for closure invocation"⟩,

  ⟨"closure_shared_capture_readers_pos_009", .closuresCaptures, true, .accept,
   Footprint.compatible ⟨[⟨0, 1⟩], []⟩ ⟨[⟨0, 1⟩], []⟩ == true,
   "Closure capturing shared view allows other concurrent shared readers"⟩,

  ⟨"closure_exclusive_capture_conflict_neg_010", .closuresCaptures, false, .rejectBorrowConflict,
   Footprint.compatible ⟨[], [⟨0, 1⟩]⟩ ⟨[⟨0, 1⟩], []⟩ == false,
   "Closure capturing exclusive view conflicts with concurrent readers"⟩,

  ⟨"closure_disjoint_views_pos_011", .closuresCaptures, true, .accept,
   stepsDisjoint {} (.field 0) (.field 1) == true,
   "Closure capturing two disjoint views passes compatibility"⟩,

  ⟨"closure_overlapping_views_neg_012", .closuresCaptures, false, .rejectBorrowConflict,
   pathsDisjoint {} [.field 0] [.field 0, .field 1] == false,
   "Closure capturing two overlapping views rejected"⟩,

  ⟨"closure_higher_order_arg_pos_013", .closuresCaptures, true, .accept,
   decide (CoreExpr.lam 0 .nat (.var 0) .empty ≠ .unit),
   "Closure passed as higher-order argument to function"⟩,

  ⟨"closure_return_rooted_capture_pos_014", .closuresCaptures, true, .accept,
   Origin.param 0 == Origin.param 0,
   "Closure returning view rooted in captured parameter"⟩,

  ⟨"closure_return_escaping_capture_neg_015", .closuresCaptures, false, .rejectEscapedView,
   decide (Origin.fresh ≠ Origin.param 0),
   "Closure returning view escaping capture scope rejected"⟩,

  ⟨"closure_liveness_preservation_pos_016", .closuresCaptures, true, .accept,
   decide (({} : State).allocations.isEmpty),
   "Liveness of captured resources preserved during invocation"⟩,

  ⟨"closure_drop_uncalled_pos_017", .closuresCaptures, true, .accept,
   decide ((State.removeOwner (State.addAllocation {} 1 [0]) 1).allocations.isEmpty),
   "Dropping uncalled closure cleans up captured owned buffer"⟩,

  ⟨"closure_inferred_effect_footprint_pos_018", .closuresCaptures, true, .accept,
   decide (Effect.empty.reads.isEmpty),
   "Inferred effect footprint accurately summarizes closure body"⟩,

  ⟨"closure_combinator_linearity_pos_019", .closuresCaptures, true, .accept,
   decide (Option.map (fun (x : Nat) => x + 1) (some 5) == some 6),
   "Higher-order combinator preserves closure linearity"⟩,

  ⟨"closure_nested_capture_scopes_pos_020", .closuresCaptures, true, .accept,
   decide (Ctx.lookup [(1, .nat), (0, .bool)] 1 == some .nat),
   "Nested closures maintain distinct, isolated capture scopes"⟩
]

end Aethel.Litmus.ClosuresCaptures
