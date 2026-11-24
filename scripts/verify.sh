#!/usr/bin/env bash
set -euo pipefail

cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."
python3 scripts/audit_proofs.py
cd aethel-lean
lake build
lake exe aethel-check
python3 ../scripts/test_source_verification.py .lake/build/bin/aethel-check
lake env lean Audit.lean | python3 ../scripts/audit_proofs.py --axioms
