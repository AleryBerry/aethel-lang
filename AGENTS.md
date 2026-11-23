# Aethel development instructions

Read `PHILOSOPHY.md`, `docs/ENGINEERING_PLAN.md`, and `docs/VERIFICATION_STATUS.md` before extending the formal model.

- The project is Lean-first. Do not start a production lexer, AST, Zig compiler pass, or LLVM backend before the formal gate in the plan passes.
- Use the pinned Lean 4.35.0 installation. Select Zig through the existing zvm installation when compiler work becomes eligible; do not change global toolchain defaults.
- Apply the installed `lean-proof` skill to proof work. Project policy is stricter than its placeholder allowance: never commit proof holes, project axioms, or native-evaluation shortcuts for theorems.
- Build and inspect proof diagnostics incrementally. Fix syntax/types before proof failures and keep completed proofs free of warnings.
- Run `bash scripts/verify.sh` from the project root. It builds Lean, executes regressions, and audits key theorem dependencies. Standard Lean axioms are documented in the verification status.
- Keep an independent mathematical specification for each executable checker. A checker cannot justify its own semantics merely by returning success.
- Update verification status whenever proof coverage changes. Distinguish scalar-slot lemmas, byte-level refinement, machine safety, and compiler assurance.
- Tests of components do not count toward the planned 250+ full-language litmus programs. Add named safety/expressiveness counterexamples when introducing a language feature.
- Put research adaptations and annotations in `research/` and record any new upstream revision explicitly.
