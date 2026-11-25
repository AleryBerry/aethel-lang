# Mathematical extraction and adaptation

## Lean-Move

**Extract:** regular-language reachability over owner-rooted paths, derivatives, graph transfer rules, `check_outbound`, relational versus executable typing, and the preservation invariant.

**Assumptions:** references follow structured paths; the evaluated language does not store references in data structures. The outbound predicate is only one part of the write/move rule and machine invariant.

**Aethel adaptation:** use exact concrete regexes independently of symbolic index aliasing. Prove fact validity before interpreting distinct index expressions as distinct values. Check parent/descendant overlap, graph coverage, returned origins, and invalidation separately.

**Counterexamples:** derivatives of `a | b` by `a` and `b` both accept epsilon. Unknown index equality cannot be handled by returning the unconsumed index atom. A loan of `x.a` conflicts with access to all of `x` even though the paths have different lengths.

## Valen

**Extract:** canonical ownership paths, group references, destruction/invalidation effects, type stability, and temporary uniqueness.

**Assumptions:** group references permit aliasing; the prototype and article are not mechanized soundness results. Optimization assumptions require more than preventing use-after-free.

**Aethel adaptation:** distinguish path handles from scoped access reservations. Allow sequential aliasing; statically forbid conflicting access while a reservation is active. Function summaries distinguish reads, writes, invalidations, and returned origins. Constructors can change which descendant paths exist.

**Counterexamples:** a caller using an interior handle after reallocation; a callee violating its declared effects; two aliasable handles incorrectly lowered with exclusive-pointer metadata.

## Zeta

**Extract:** conditional equality/disequality facts, place comparisons, and invalidation on mutation and loop boundaries. Inspect `sentinel-typechecker/src/borrowck/places.rs` and `ensures.rs` at the pinned revision.

**Assumptions:** this implementation is not a proved complete Presburger procedure. Source variable names alone cannot identify stable index values.

**Aethel adaptation:** captured value identities, a satisfied fact environment, conservative joins, and verified loop certificates. Extend the initial disequality checker to affine inequalities through explicit sound inference rules.

**Counterexamples:** distinct variable names evaluating to equal indices; a guard fact used after changing its operand; fixed-width wraparound interpreted as mathematical addition.

## Cogent / Dargent

**Extract:** logical-to-physical representation relations, bit ranges, valid layouts, generated getter/setter behavior, and frame properties.

**Assumptions:** the original development is Isabelle/HOL, not Lean; collection-level AoS/SoA equivalence is additional Aethel work. Invalid external encodings require validation.

**Aethel adaptation:** relate each representation to a common logical store. Prove read agreement, update preservation, untouched-field behavior, allocation validity, and actual memory footprints. Separate storage groups when access contracts demand independence.

**Counterexamples:** packing constructor payloads without a tag; independent logical bit fields sharing a physical read-modify-write byte; comparing unrelated AoS and SoA heaps. Descending alignment is not globally optimal for unconstrained field size/alignment pairs.

## Tree Borrows / MiniRust

**Extract:** allocation provenance, per-access permissions, protectors, explicit allocation and access validity, and alignment checks parameterized by the target.

**Assumptions:** operational aliasing semantics are not a static checker. Copying four permission-state names does not prove checker soundness or LLVM compatibility. The paper artifact and current MiniRust differ.

**Aethel adaptation:** define Aethel's permissions and access footprints directly; prove the checker respects them. Start with scoped concurrency and no raw-pointer escape hatch. Add optimization claims only with their own simulation or stated backend trust.

**Counterexamples:** a 64-byte-aligned base with a 4-byte-offset access incorrectly marked 64-aligned; vector FMA replacing strict separate arithmetic; a parent writing storage delegated to a running child.

## Rust Borrow Checker (rustc_borrowck)

**Extract:** lockstep projection conflict monoid (`Overlap`: `Arbitrary`, `EqualOrDisjoint`, `Disjoint`), `PlaceConflictBias` (`Overlap` vs `NoOverlap`), non-overlapping struct fields and `downcast` enum variants, disjoint constant-index/subslice ranges, and two-phase borrows (`MutBorrowKind::TwoPhaseBorrow`).

**Assumptions:** `rustc_borrowck` compares syntactic MIR `Place`s conservatively under `PlaceConflictBias::Overlap` for runtime `ProjectionElem::Index`, and lacks first-class inter-procedural SoA field splitting over a monolithic array without `unsafe` raw pointer splitting.

**Aethel adaptation:** embed every non-conflicting `rustc_borrowck` addressable place pair into Aethel's compatible byte footprints (`RustBorrowBridge`), refine `TwoPhaseBorrow` to `BorrowPerm`, strictly subsume dynamic index and Bevy-style split SoA column disjointness via `AffineIndex` and `MultiPathViews`, and safely lend verified disjoint views/slices to Rust FFI while rejecting sub-byte bit-packed references.

**Counterexamples:** two distinct runtime indices `a[i]` and `a[j]` under `i < j` are treated as `EqualOrDisjoint` (rejected) by `rustc_borrowck` under `Overlap` bias; borrowing a sub-byte bit-packed field directly as `&T`/`&mut T` breaks Rust pointer alignment and byte-granularity guarantees.

## Rust Trait Solver, Orphan Rule, and ABI (rustc_next_trait_solver & rustc_abi)

**Extract:** `orphan_check_trait_ref` (`InCrate::Local` vs `InCrate::Remote`, fundamental wrappers `Box`/`&`/`&mut`, uncovered type-parameter ordering), `overlapping_trait_impls` coherence, `#[repr(C)]` deterministic declaration-order layout (`ReprOptions` / `FieldsShape::Arbitrary`), and unstable `repr(Rust)` (`field_shuffle_seed`) / `dyn Trait` vtables (`VtblEntry`).

**Assumptions:** Rust enforces global coherence via the orphan rule (blocking downstream retroactive composition of upstream traits on upstream types) and does not check equational trait laws; `repr(Rust)` structs and `dyn Trait` fat pointers have no stable cross-compiler ABI.

**Aethel adaptation:** prove link-safety of Rust orphan-checked ground impls and coherent 1-to-1 migration into Aethel `default instance`s (`RustTraitBridge`); solve Haskell's typeclass trilemma and Rust's orphan limitation in Aethel via open-universe named `instance`s, call-site `using` overrides, polynomial structural lifting (`no newtype` needed), `InstanceId`-branded container coherence, and Lean-checked `trait` laws (`CategoricalTraits`). Cross the FFI boundary strictly from Rust into Aethel using deterministic flat C-ABI structs, Bevy-style split SoA queries, and 64B-aligned AoSoA tile slices (`RustComplexABI`), recording foreign Rust trait contracts honestly without project axioms.

**Counterexamples:** an app crate implementing an upstream trait (`ToJson`) for an upstream type (`Foo`) is rejected by `orphan_check_trait_ref`; an unlawful `Monoid` impl (`empty = 1, combine = +`) passes Rust type-checking despite violating identity laws; passing a `repr(Rust)` or bit-packed container directly as `&[AoS]` causes field/stride mismatch across compilers.

## Segmented AoSoA growth

Rust's typed compiler arena keeps backing chunks separately allocated and grows by adding a chunk descriptor. Aethel's experiment uses fixed-width chunks with one column per field so a row has a stable allocation identity and a simple tile index. Each append resolves its destination and checks exclusive byte access. The Lean proof tracks which bytes and views an append preserves. The benchmark compares this design with geometric growth of a contiguous tiled buffer. A Rust slice over a tile remains subject to the single-allocation rule. [Pinned Rust arena](https://github.com/rust-lang/rust/blob/c884ecfbabb04b04fa5054dafc67ec258ecde745/compiler/rustc_arena/src/lib.rs) · [Experiment](segmented-aosoa/README.md)

## Compiler refactor candidates from the inspection

- The inspected standard-library draft held identical source text for eleven modules in `std/` and the Zig embedding table. Build-time embedding from the source files could preserve standalone import behavior and remove the duplicated module bodies.
- The analyzer and code generator had separate identifier walkers. Their treatment of `using` differed in the inspected snapshot. A shared traversal for syntax with caller-specific binding policies would let borrow liveness and code emission use the same coverage of expression forms. Exercise shadowing and nested `using` before consolidation.

## Source-to-MIR correspondence

The Stage G snapshot first examined during source verification emitted an empty `main` MIR body for `missing_field.aethel`. Its terminal field lookup returned an error type without a diagnostic, so the validator examined the supplied empty body. Stage G now diagnoses the unknown field before MIR emission. The reference checker resolves the return path before lowering. Production MIR still needs a link from every submitted body, effect, guard, and access footprint to compiler input. [Source fixture](../tests/source-verification/missing_field.aethel) · [MIR emitter](../aethel-zig/src/mir.zig)

The reference MIR checker compares complete derived operations, including both branch arms, every helper declaration, returned places, ownership moves, and accesses that read runtime loop bounds. Stage G previously lowered scalar-view comparisons, numeric matches, and loop bounds as pointers. These operations now load the integer value with any required widening. The native borrow checker analyzes the body of the literal zero-iteration loop. The reference checker validates its names and contracts and omits the unreachable body from its resource check. [Scalar view fixture](../tests/source-verification/branch_guard_reads_through_view.aethel) · [Runtime bound fixture](../tests/source-verification/loop_bound_reads_exclusive_view.aethel) · [Zero iterations fixture](../tests/source-verification/zero_iterations_skip_conflicting_body.aethel)

Stage G derives the direct byte-field footprint of a returned view when each return resolves to the same contracted parameter field and the caller can resolve the argument to that record. Ambiguous field results retain the conservative footprint. The three reference-accepted sibling-write fixtures now match native execution, and the unlisted return field reports a source diagnostic. [Returned shared field](../tests/source-verification/returned_shared_view_restores_field_after_branch.aethel) · [Unlisted return field](../tests/source-verification/returned_view_rejects_unlisted_origin_field.aethel)

The byte-field countdown rule matches the full loop before emitting its natural-number decrease certificate. The Lean reference proof connects the same guarded saturating subtraction to actual byte-machine execution, including the final guard read. Native `verify --lean` accepts the resulting v1 decrease certificate. The proof of v1 emission correspondence for the whole module remains open. [Measured countdown](../tests/source-verification/while_countdown_runs_from_maximum_byte.aethel)

The reference checker models explicit transfer of its initialized record allocation and retires the old name. Stage G treats flat records as copyable, so its `move` leaves the old value usable. The checked positive examples agree on the returned bytes. [Retired owner fixture](../tests/source-verification/move_rejects_read_through_old_owner.aethel)

The current production v1 emitter produces identical certificates for two thermostat programs whose only difference is the stored target. The program results are 34 and 79, and both certificates pass the Lean v1 validator. The certificate emitter records each write with the placeholder value `1` and emits summarized reads before writes. The reference checker rejects substituting one program's MIR for the other. [Cold target](../tests/source-verification/production_mir_distinguishes_cold_setting.aethel) · [Hot target](../tests/source-verification/production_mir_distinguishes_hot_setting.aethel)

The reference checker fixes lexical captures in core MIR and checks pure higher-order applications. Native comparisons exposed failures from Zig name shadowing, runtime higher-order calls, and returned capturing closures. [Capture fixture](../tests/source-verification/closure_captures_before_shadowing.aethel) · [Higher-order call fixture](../tests/source-verification/closure_can_be_passed_as_argument.aethel) · [Returned closure fixture](../tests/source-verification/returned_closure_keeps_outer_argument.aethel)
