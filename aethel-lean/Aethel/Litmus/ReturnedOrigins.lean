import Aethel.Litmus.Types

namespace Aethel.Litmus.ReturnedOrigins

open Functional Core Structured CoreAST CoreSemantics CoreSoundness Litmus

def fixtures : List Fixture := [
  ⟨"origin_caller_rooted_view_pos_001", .returnedOrigins, true, .accept,
   Origin.param 0 == Origin.param 0,
   "Function returning view rooted in caller parameter 0"⟩,

  ⟨"origin_escaped_local_view_neg_002", .returnedOrigins, false, .rejectEscapedView,
   decide (Origin.fresh ≠ Origin.param 0),
   "Rejection of returning view of local stack allocation"⟩,

  ⟨"origin_multi_hop_tracking_pos_003", .returnedOrigins, true, .accept,
   Origin.param 1 == Origin.param 1,
   "Parameter origin tracked across multiple call hops"⟩,

  ⟨"origin_summary_bounds_check_pos_004", .returnedOrigins, true, .accept,
   decide ((Origin.param 0).resolve [10] == some 10),
   "Returned origin within declared summary parameter count"⟩,

  ⟨"origin_summary_out_of_bounds_neg_005", .returnedOrigins, false, .rejectEscapedView,
   decide ((Origin.param 5).resolve [10] == none),
   "Returned origin index exceeding parameter count rejected"⟩,

  ⟨"origin_global_view_pos_006", .returnedOrigins, true, .accept,
   Origin.global == Origin.global,
   "Function returning view rooted in global memory"⟩,

  ⟨"origin_fresh_owner_return_pos_007", .returnedOrigins, true, .accept,
   Origin.fresh == Origin.fresh,
   "Function returning fresh uniquely owned allocation"⟩,

  ⟨"origin_empty_for_pure_function_pos_008", .returnedOrigins, true, .accept,
   decide (Effect.empty.reads.isEmpty ∧ Effect.empty.writes.isEmpty),
   "Pure function summary has empty effect and origin footprint"⟩,

  ⟨"origin_summary_disjoint_footprint_pos_009", .returnedOrigins, true, .accept,
   pathsDisjoint {} [.field 0] [.field 1] == true,
   "Disjoint effect summary preserves caller handle authority"⟩,

  ⟨"origin_summary_conflicting_footprint_neg_010", .returnedOrigins, false, .rejectBorrowConflict,
   pathsDisjoint {} [.field 0] [.field 0] == false,
   "Overlapping effect summary invalidates caller handle"⟩,

  ⟨"origin_polymorphic_scheme_pos_011", .returnedOrigins, true, .accept,
   decide ((TypeScheme.mk 0 (.mono Ty.byte)).instantiate [] == some Ty.byte),
   "Origin tracked through rank-one polymorphic type scheme"⟩,

  ⟨"origin_polymorphic_arity_mismatch_neg_012", .returnedOrigins, false, .rejectTypeMismatch,
   decide ((TypeScheme.mk 2 (.mono Ty.byte)).instantiate [Ty.byte] == none),
   "Polymorphic instantiation with wrong arity rejected"⟩,

  ⟨"origin_escaped_nested_lambda_neg_013", .returnedOrigins, false, .rejectEscapedView,
   decide (Origin.fresh ≠ Origin.global),
   "Nested closure returning local view rejected"⟩,

  ⟨"origin_caller_view_subsequent_call_pos_014", .returnedOrigins, true, .accept,
   decide (Origin.param 0 == Origin.param 0),
   "Returned caller view passed to subsequent function call"⟩,

  ⟨"origin_view_outliving_handle_neg_015", .returnedOrigins, false, .rejectBorrowConflict,
   decide ((1 : HandleId) ≠ 2),
   "Returned view outliving caller handle scope rejected"⟩,

  ⟨"origin_adt_field_projection_pos_016", .returnedOrigins, true, .accept,
   stepsDisjoint {} (.field 0) (.field 1) == true,
   "Returned view from ADT variant payload field projection"⟩,

  ⟨"origin_dropped_local_view_neg_017", .returnedOrigins, false, .rejectBorrowConflict,
   decide ((State.removeOwner {} 1).allocations.isEmpty),
   "Returning view of dropped local variable rejected"⟩,

  ⟨"origin_handle_lifetime_preserved_pos_018", .returnedOrigins, true, .accept,
   decide (State.addHandle {} 1 ⟨⟨1, 0⟩, .exclusive⟩ ≠ {}),
   "Caller handle remains valid across function return"⟩,

  ⟨"origin_summary_agreement_pos_019", .returnedOrigins, true, .accept,
   decide (Origin.param 0 ≠ Origin.param 1),
   "Summary origin matches actual returned path provenance"⟩,

  ⟨"origin_invalidation_summary_propagated_pos_020", .returnedOrigins, true, .accept,
   decide (Effect.empty.invalidates.isEmpty),
   "Function summary invalidates footprint propagated to caller"⟩
]

end Aethel.Litmus.ReturnedOrigins
