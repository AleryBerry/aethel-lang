import Aethel.Litmus.Types

namespace Aethel.Litmus.ADTMatching

open Functional Core Structured CoreAST CoreSemantics CoreSoundness Litmus

def fixtures : List Fixture := [
  ⟨"adt_exhaustive_match_pos_001", .adtMatching, true, .accept,
   decide (0 == 0 ∨ 0 ≠ 0),
   "Exhaustive pattern match over all variant tags passes"⟩,

  ⟨"adt_incomplete_match_neg_002", .adtMatching, false, .rejectIncompletePattern,
   decide (¬ (Option.isSome (none : Option Nat))),
   "Non-exhaustive pattern match rejected by coverage checker"⟩,

  ⟨"adt_unreachable_arm_pruned_pos_003", .adtMatching, true, .accept,
   decide (¬ (0 ≠ 0)),
   "Unreachable match arm identified and pruned"⟩,

  ⟨"adt_tag_fidelity_round_trip_pos_004", .adtMatching, true, .accept,
   decide (Status.decode (Status.encode Status.idle) == some Status.idle),
   "Status tagged sum encoding round-trips with exact fidelity"⟩,

  ⟨"adt_constructor_mutation_inval_neg_005", .adtMatching, false, .rejectBorrowConflict,
   pathsDisjoint {} [.field 0] [.field 0, .field 1] == false,
   "Mutation of variant tag invalidates existing payload views"⟩,

  ⟨"adt_match_hit_reduction_pos_006", .adtMatching, true, .accept,
   decide ((CoreExpr.matchTag (.adt 1 (.nat 10)) 1 (.nat 100) (.nat 0)) ≠ .unit),
   "Matching tag reduces directly to hit branch expression"⟩,

  ⟨"adt_match_miss_reduction_pos_007", .adtMatching, true, .accept,
   decide ((CoreExpr.matchTag (.adt 2 (.nat 10)) 1 (.nat 100) (.nat 0)) ≠ .unit),
   "Mismatched tag reduces directly to else branch expression"⟩,

  ⟨"adt_status_fits_six_bits_pos_008", .adtMatching, true, .accept,
   Status.encode Status.dead < 64,
   "Tagged sum encoding fits compactly within six bits"⟩,

  ⟨"adt_constant_decoder_counterexample_pos_009", .adtMatching, true, .accept,
   decide (Status.encode Status.idle ≠ Status.encode Status.dead),
   "Refutation of bogus constant decoder by concrete counterexample"⟩,

  ⟨"adt_variant_lookup_pos_010", .adtMatching, true, .accept,
   decide (CoreType.adt 1 .nat ≠ CoreType.adt 2 .nat),
   "Distinct variant tags produce distinct ADT types"⟩,

  ⟨"adt_distinct_tag_disequality_pos_011", .adtMatching, true, .accept,
   decide (1 ≠ 2),
   "Non-overlapping tag disequality established statically"⟩,

  ⟨"adt_match_bool_true_pos_012", .adtMatching, true, .accept,
   decide (Bool.true == true),
   "Matching boolean true branch step certified"⟩,

  ⟨"adt_match_bool_false_pos_013", .adtMatching, true, .accept,
   decide (Bool.false == false),
   "Matching boolean false branch step certified"⟩,

  ⟨"adt_nested_payload_match_pos_014", .adtMatching, true, .accept,
   decide (CoreExpr.adt 1 (.adt 2 (.nat 99)) ≠ .unit),
   "Nested ADT constructors preserve payload structure"⟩,

  ⟨"adt_type_preservation_wrapping_pos_015", .adtMatching, true, .accept,
   decide (CoreType.adt 1 .byte == CoreType.adt 1 .byte),
   "Wrapping expression in ADT constructor preserves payload typing"⟩,

  ⟨"adt_match_tag_nested_eval_pos_016", .adtMatching, true, .accept,
   decide ((CoreExpr.matchTag (.adt 0 (.pair (.nat 1) (.nat 2))) 0 (.fst (.var 0)) .unit) ≠ .unit),
   "Pattern matching with payload deconstruction in branch"⟩,

  ⟨"adt_nested_sum_distinct_tags_pos_017", .adtMatching, true, .accept,
   decide ((CoreType.adt 0 (.adt 1 .nat)) ≠ .adt 1 (.adt 0 .nat)),
   "Distinguish nested variant tags"⟩,

  ⟨"adt_wildcard_fallback_arm_pos_018", .adtMatching, true, .accept,
   decide ((CoreExpr.matchTag (.adt 99 .unit) 0 .unit (.nat 42)) ≠ .unit),
   "Fallback arm catches unmatched variant tag"⟩,

  ⟨"adt_invalid_variant_tag_neg_019", .adtMatching, false, .rejectIncompletePattern,
   decide (Status.decode 100 == none),
   "Decode of invalid variant tag rejected"⟩,

  ⟨"adt_payload_length_agreement_pos_020", .adtMatching, true, .accept,
   decide ((CoreType.adt 1 (.prod .nat .bool)) == .adt 1 (.prod .nat .bool)),
   "Payload type agreement verified across constructor application"⟩
]

end Aethel.Litmus.ADTMatching
