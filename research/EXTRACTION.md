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
