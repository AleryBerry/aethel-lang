# Research manifest

## Pinned research snapshots

- Lean-Move evaluated artifact: `c959473c0d1599e1483c60795e7d3fa2e46b768d`, https://github.com/ilyasergey/lean-move ; artifact https://zenodo.org/records/21850968 . Its own Lean toolchain is 4.27.0; Aethel's independent development uses installed Lean 4.35.0.
- Valen: `b2aa19bdcd01570efba6684fac9a3d08a43c7d37`, https://github.com/valen-lang/Valen ; author explanation https://verdagon.dev/blog/valen-group-borrowing .
- Zeta: `4e5b5233961c37935da6b0774218e26949b2a41f`, https://github.com/zeta-lang/zeta ; specification https://gist.github.com/FlameyosSnowy/a49a35ba006238be55d8c3e410c31061 at `8dd0334800230429d1c1a8b79b403fd788ff5853`.
- Dargent: POPL 2023, DOI https://doi.org/10.1145/3571240 ; artifact https://doi.org/10.5281/zenodo.7220452 .
- Tree Borrows: PLDI 2025, DOI https://doi.org/10.1145/3735592 ; frozen artifact https://zenodo.org/records/15002703 .
- MiniRust: `063d784186d3252bee242217f218223205c0b568`, https://github.com/minirust/minirust . Do not silently mix the live specification with the paper-era Tree Borrows state machine.
- Lean agent skills: `7d3da0282e7b724b07620e45cf212f2e05e19334`, https://github.com/leanprover/skills . `lean-proof` applies to proof work. The project's no-placeholder policy overrides the proof skill's allowance for temporary `sorry`.

## Reuse boundary

Current Lean definitions and proofs are written for Aethel. No upstream formalization has been vendored. The citations establish research context, not proof inheritance.

## Law system and Rust interoperability

- Bend 2 at `0e2f38f759cc830849e489307f3d256a7d148288`, https://github.com/bendlang/bend . The companion law/proof workflow and BendTT verdict are described in the guide and `bend2/safe.ts`.
- Rust at `c884ecfbabb04b04fa5054dafc67ec258ecde745`, https://github.com/rust-lang/rust . Inspected `compiler/rustc_borrowck/src/places_conflict.rs`, `compiler/rustc_next_trait_solver/src/coherence.rs`, `compiler/rustc_trait_selection/src/traits/coherence.rs`, `compiler/rustc_hir_analysis/src/coherence/orphan.rs`, `compiler/rustc_abi/src/lib.rs`, `compiler/rustc_middle/src/ty/vtable.rs`, and `library/core/src/slice/raw.rs`. A separate host probe used rustc 1.88.0 and Zig 0.17.0 to sort a Zig-owned scalar buffer in place through a static Rust C-ABI adapter.

The segmented AoSoA experiment also references `compiler/rustc_arena/src/lib.rs` at the same pinned Rust revision `c884ecfbabb04b04fa5054dafc67ec258ecde745`.
