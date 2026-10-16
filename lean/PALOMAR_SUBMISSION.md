# Palomar submission sheet (not yet submitted)

| Field | Value |
|---|---|
| Repository | GregoryMorse/SelfModTamper |
| Exact commit | to be filled after the preflight passes (the commit recorded in FINAL_ACCEPTANCE.json) |
| project_path | lean |
| Comparator config | lean/comparator.json |
| Metadata | lean/formalization.yaml |
| Selected statement | PalomarSMT.mathematical_result (T1 security, T3 necessity of A1-A8, T2 mediation, T4 level matrix, Harvard separation) |
| request_id | selfmodtamp1 (as in .github/workflows/palomar-full.yml) |
| Registry entry | none yet; the author submits and registers |

Notes: AI assistance (Claude) is disclosed in formalization.yaml. `Challenge.lean` is about 800 lines / 38 KB (hard limit 1000 / 100 KiB;
preferred 300 / 32 KiB, exceeded). The model is abstract; the platform contract is in PLATFORM_CONTRACT.md. Open obligations are in GAPS.md
(Level-2 refinement of the unrolled kernel G01/G03/G13, exact clear counts G04/G05, primary-source reading G20-G22, errata item P14, table
label order G24, and the author's review of the errata PDF).
