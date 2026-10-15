#!/usr/bin/env bash
# Linux proof job body (run inside a bounded cgroup by .github/workflows/proof.yml):
# cold build of the library, the Challenge and the Solution, axiom audit, generated-file checks.
# No Mathlib (plan D4). Later rounds append their checks (make_challenge, audit_errata, coverage, threat).
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")/../.."
ROOT="$PWD"
cd lean
lean --version
lake build SmcTamper 2>&1 | tee "$ROOT/lake-build.log"
cd "$ROOT"
python3 validation/ci/axioms.py
echo "linux-proof: OK"
