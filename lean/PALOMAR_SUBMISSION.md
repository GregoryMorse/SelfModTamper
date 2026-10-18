# Palomar submission sheet

**Registered 2026-10-18 as PALOMAR-2026-10-18-000004, version 1:** https://palomar-registry.org/entry?id=PALOMAR-2026-10-18-000004&version=1
Registered commit `0a48a85e0f1884a50c6abdcf8617bd315a6b59c2`, tag `palomar-v1`. History: the first three submissions (69a9d34, 1629c62, c37a8d5) received reviews with problems or warnings about the statement/prose alignment (GAPS section E and the commits after 69a9d34); the fourth passed and was registered. The table below describes the registered submission.

| Field | Value |
|---|---|
| Repository | GregoryMorse/SelfModTamper |
| Exact commit | 0a48a85e0f1884a50c6abdcf8617bd315a6b59c2 (tag `palomar-v1`) |
| project_path | lean |
| Comparator config | lean/comparator.json |
| Metadata | lean/formalization.yaml |
| Selected statement | PalomarSMT.mathematical_result (T1 security, T3 necessity of A1-A8, T2 mediation, T4 level matrix) |
| request_id | selfmodtamp1 (as in .github/workflows/palomar-full.yml) |
| Registry entry | PALOMAR-2026-10-18-000004, version 1 (https://palomar-registry.org/entry?id=PALOMAR-2026-10-18-000004&version=1) |

Notes: AI assistance (Claude) is disclosed in formalization.yaml. `Challenge.lean` is about 800 lines / 37 KB (hard limit 1000 / 100 KiB;
preferred 300 / 32 KiB, exceeded). The model is abstract; the platform contract is in PLATFORM_CONTRACT.md. Leave the Palomar ID blank
unless the result is already in the public registry (the first submission was not registered). Status of the gaps is in GAPS.md: the
instruction-level proof of the unrolled kernel (G01), the intro count (G03), the primary sources (G20-G22), the table labels (G24) and the AMD
erratum P14 (withdrawn) are closed; exact clear counts (G04/G05) are non-claims; the author's review of the errata PDF is outstanding.

Changes made after the first review (G45-G49 in GAPS.md): an effective alarm requires a response byte and `k > 0` (in A6/A7); T4 states that
the other assumptions hold; the Harvard observation (C01, C02) is no longer part of the selected statement; status notes made consistent.
