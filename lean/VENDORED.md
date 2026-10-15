# Vendored infrastructure

Copied (not Lean code) from `../selfspectre` at commit `12160a3` (plan D5) and adapted. Names: `WriteExecute` ->
`SmcTamper`, `PalomarWE` -> `PalomarSMT`, `selfspectre` -> `selfmodtamper`, branch `master` -> `main`.
Hashes are the first 16 hex digits of SHA-256 of the *source* file at that commit.

| File | Source | SHA-256 (source, 16) | Edits |
|---|---|---|---|
| validation/limited_run.py | validation/limited_run.py | ec77aa6b083055a6 | names; none |
| validation/memory_budget.py | validation/memory_budget.py | 8e88e9cf419f01b9 | names; none |
| validation/lean_build.py | validation/lean_build.py | b013080b94ce9475 | names; none |
| validation/build_modules.py | validation/build_modules.py | 3808d2055c30154c | names; none |
| validation/axiom_audit.py | validation/axiom_audit.py | abfdd81aad310f2e | names; none |
| validation/make_challenge.py | validation/make_challenge.py | 9f1bdc8d00bf5fa9 | names; none |
| validation/audit_errata.py | validation/audit_errata.py | d880db985d15b7cf | names; none |
| validation/make_errata.py | validation/make_errata.py | e48a4393171e9584 | names; none |
| validation/extract_layout.py | validation/extract_layout.py | f62102118be4907c | names; none |
| validation/run_listings.py | validation/run_listings.py | 28a186f5f39bb573 | names; none |
| validation/native.py | validation/native.py | 5bc8d94f303e3152 | names; rewritten: compile-only, SelfModTamper.sln Debug/Release x64 |
| validation/ci/axioms.py | validation/ci/axioms.py | 92b91837e6b32cb5 | names; dropped the Solution import (added back in R15) |
| validation/ci/linux.sh | validation/ci/linux.sh | 02ee8a6327fed71d | rewritten: no Mathlib cache, builds SmcTamper only (later rounds append checks) |
| .github/workflows/proof.yml | .github/workflows/proof.yml | c28944bd35a98881 | names, branch; windows-native job reduced to compile-only; the evidence harness is added in R12 |
| .github/workflows/palomar-full.yml | .github/workflows/palomar-full.yml | 6ed6d950e652702b | names, branch; windows-native job reduced to compile-only; the evidence harness is added in R12 |
| validation/palomar/fetch_policy_assets.py | validation/palomar/fetch_policy_assets.py | e1efe36e7c20ada9 | names; policy assets are fetched in R15 |
| validation/palomar/refresh_policy.py | validation/palomar/refresh_policy.py | dbd2624f37584a25 | names; policy assets are fetched in R15 |
| validation/palomar/validate_metadata.py | validation/palomar/validate_metadata.py | 6f91be7c4509ca3e | names; policy assets are fetched in R15 |

New in this repo (not vendored): `validation/build_tex.py` (latexmk in a scratch copy), `validation/check_tables.py`,
`validation/data/paper_tables.json`.
Not copied: `prepare_mathlib.py` (no Mathlib, plan D4), the selfspectre-specific generators and vector scripts.
`lean/lake-manifest.json` is hand-written (no dependencies); `lakefile.proof.toml` equals `lakefile.toml` plus
`buildDir = ".lake/proof-build"` (checked by `lean_build.py`).
