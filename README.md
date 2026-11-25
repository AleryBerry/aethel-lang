# Aethel

A research language combining advanced path borrowing, automatic alignment and access-aware data layout, and a small algebraically typed syntax.

Read [the philosophy](PHILOSOPHY.md), [the engineering plan](docs/ENGINEERING_PLAN.md), and [the verification status](docs/VERIFICATION_STATUS.md).

The formal model and regression suite live in `aethel-lean`, which pins Lean 4.35.0. The experimental compiler in `aethel-zig` uses Zig 0.17.0. The sequential formal gate remains open.

```sh
cd aethel-lean
lake build
lake exe aethel-check
```

Run the complete current verification suite from the project root with
`bash scripts/verify.sh`.

Check and execute the reference byte-record source fragment from `aethel-lean` with
`lake exe aethel-check --source ../tests/source-verification/call_under_disjoint_view.aethel`.
The [verification status](docs/VERIFICATION_STATUS.md#reference-source-checker) includes reference MIR emission and checking commands.

The executable runs Lean regressions for the foundations, the byte resource checker, the pure functional fragment, bounded search, and structured programs. The verification status records the exact proved claims and the remaining formal gate.

The [research manifest](research/MANIFEST.md) records the upstream publications and artifact revisions.
