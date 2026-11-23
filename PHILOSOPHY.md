# Aethel: philosophy and core ideas

Aethel aims to make systems programming readable without making memory behavior mysterious. Its central ideas are an advanced borrow checker, automatic memory alignment, and data structures whose physical organization follows their access patterns.

The programmer describes meaning through algebraic data types and small, explicit functions. The implementation chooses representations and checks whether accesses are safe. Safety, representation correctness, and performance are separate claims that need separate evidence.

## Simple syntax, strong types

Gleam supplies the surface direction: braces, `fn`, `case`, algebraic constructors, and little punctuation. Python supplies the preference for clarity and low ceremony. Haskell supplies algebraic types and parametric polymorphism. Evaluation is strict and mutation is explicit; borrowing these ideas does not imply adopting laziness or every feature of those languages.

Ownership and path contracts should communicate what a function can affect without requiring lifetime parameters throughout ordinary source code. Public interfaces must remain sufficient to check callers independently.

## Borrow the smallest useful part

A reference to an entity's position should not unnecessarily lock its health. A guard proving two indices unequal should allow independent access to those elements. Half-open slices should split naturally when their ranges do not overlap.

The candidate design distinguishes aliasable path handles from scoped access permissions. Handles can identify the same place and alternate sequential accesses. A scoped view reserves access for a block, call, loop, or task; conflicting access through other handles is prohibited while that reservation is active. Returning a view requires a caller-owned origin that remains alive. Destruction, relocation, and constructor changes must invalidate affected descendants.

This combination is a research target. It must earn its safety theorem and demonstrate useful accepted examples before becoming a language guarantee. Initially, views may be local or returned from parameters; references stored in heap data and cyclic reference graphs are outside the core.

## Meaning is independent of layout

An algebraic record describes its fields, not its padding. The same logical collection may use an array of records or separate field columns. Both representations must implement the same logical reads and writes.

Automatic layout respects actual access requirements. Small fields can share a byte when safe; fields requiring independent parallel access receive separate storage. A masked update of one bit still reads and writes a whole storage unit, so logical separation alone cannot establish physical independence.

Layout is selected at allocation and remains fixed for that allocation's lifetime in the initial design. Compact fields use verified accessors rather than pretending every bit has a native pointer. Reordering and packing must preserve constructor tags, neighboring values, bounds, initialization, and provenance.

## Alignment is a property of each access

A well-aligned allocation is only a starting point. Every scalar or vector access must satisfy its own alignment and bounds requirements. A 64-byte-aligned column does not make every interior element 64-byte aligned.

Layout optimality is claimed only under stated hypotheses. AoS/SoA selection is a profitability heuristic, not a universal speed guarantee. Strict floating-point operations keep their semantics across scalar and vector execution; fused operations require explicit permission.

## Prove the language before compiling it

The first implementation is an executable Lean model. Its raw core syntax must represent invalid programs so rejection tests are meaningful. An independent typing judgment and a proved executable checker connect acceptance to semantics. Progress, preservation, representation refinement, and initialization establish whole-execution safety.

No production lexer, AST, compiler passes, or LLVM backend begins before the agreed formal gate. Scoped parallelism requires a separate fork/join permission and race-freedom proof. General threads, atomics, async, FFI, and stored references can be added through later explicit extensions.

Proof status must be honest. A successful build is not a soundness proof; passing examples are not universal guarantees; existing research does not prove that its mechanisms compose. No `sorry`, project axioms, or hidden assumptions may stand in for the claims being made.

## Make flexibility measurable

Maintain named examples of useful safe programs alongside nearby unsafe counterexamples. Compare policies using accepted patterns, annotations, checker complexity, and runtime costs. Unknown disjointness remains an unresolved obligation, never permission to proceed unsafely.

The intended result is a language that explains its decisions: what is borrowed, why two accesses are independent, how data is laid out, and which evidence justifies an optimization.

## Make laws and termination part of the program

Ordinary functions finish on valid finite inputs. A long-lived application runs verified steps and returns owned state between events. Explicit result types make expected failures visible in function signatures. Lean checks the evidence for termination and laws against Aethel's own semantics.

A project's laws describe the behavior its authors care about. An application can require that a sort preserves all elements or that a motion update preserves health regardless of the chosen layout. Ordinary functions and algebraic types give those laws a vocabulary that stays close to the application.

Interop preserves the promises foreign code relies on. A Rust adapter acquires a scoped reservation for its actual physical accesses and keeps Rust-owned representation and destruction on the Rust side. The engineering specification defines those boundaries and the proof obligations.
