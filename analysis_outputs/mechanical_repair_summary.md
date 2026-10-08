# Pre-registered mechanical repairs of structural failures

No LLM is involved. The edit templates were written to `artifacts/mechanical_repairs/preregistered_templates.json`
in the harness before any edited proof was compiled, and each is applied only where it is syntactically
applicable. For every attempted edit the harness compiles two files on the same refactored variant in the
pinned Lean environment: the unedited proof (a control that must reproduce the recorded failure) and the
edited proof. Proof, proof_aux and import blocks are exactly those of the evaluated artifact (VERINA source
blocks for reference proofs; the hash-verified primary artifact for model proofs).

## Pre-registered templates

| Template | Rule |
|---|---|
| `unfold_add_helper` | if the proof contains `unfold <f>`, add the generated helper name to that same unfold |
| `simp_add_helper` | if the proof contains `simp [... <f> ...]`, add the generated helper name to that simp list |
| `dsimp_add_helper` | if the proof contains `dsimp [... <f> ...]`, add the generated helper name to that dsimp list |

## By proof source

A record is one (proof source, failing structural variant); it counts as repaired if any applicable
template makes it compile. Rates use only records whose unedited control reproduced the failure.

| Source | Structural failures | Eligible for >=1 template | Control reproduces failure | Repaired (union) | Rate among eligible | Share of all failures |
|---|---|---|---|---|---|---|
| reference | 54 | 54 | 54 | 51 | 94.4% | 94.4% |
| deepseek-prover-v2-7b | 34 | 32 | 32 | 21 | 65.6% | 61.8% |
| goedel-prover-v2-8b | 29 | 28 | 28 | 19 | 67.9% | 65.5% |
| goedel-prover-v2-32b | 25 | 25 | 25 | 18 | 72.0% | 72.0% |
| **all** | 142 | 139 | 139 | 109 | 78.4% | 76.8% |

## Why records are not eligible

| Source | Reason | Records |
|---|---|---|
| deepseek-prover-v2-7b | no pre-registered template is syntactically applicable | 2 |
| goedel-prover-v2-8b | no pre-registered template is syntactically applicable | 1 |

## By template (control-verified edits)

| Template | Source | Edits | Repaired | Success rate |
|---|---|---|---|---|
| `dsimp_add_helper` | deepseek-prover-v2-7b | 14 | 14 | 100.0% |
| `dsimp_add_helper` | goedel-prover-v2-32b | 16 | 13 | 81.2% |
| `dsimp_add_helper` | goedel-prover-v2-8b | 15 | 13 | 86.7% |
| `simp_add_helper` | deepseek-prover-v2-7b | 14 | 4 | 28.6% |
| `simp_add_helper` | goedel-prover-v2-32b | 9 | 5 | 55.6% |
| `simp_add_helper` | goedel-prover-v2-8b | 13 | 6 | 46.2% |
| `simp_add_helper` | reference | 1 | 1 | 100.0% |
| `unfold_add_helper` | deepseek-prover-v2-7b | 4 | 3 | 75.0% |
| `unfold_add_helper` | reference | 53 | 50 | 94.3% |
| `dsimp_add_helper` | **all** | 45 | 40 | 88.9% |
| `simp_add_helper` | **all** | 37 | 16 | 43.2% |
| `unfold_add_helper` | **all** | 57 | 53 | 93.0% |

## By transformation

| Transformation | Failures | Eligible | Control-verified | Repaired (union) |
|---|---|---|---|---|
| T2_helper_extract | 112 | 109 | 109 | 83 |
| T5_branch_extract | 30 | 30 | 30 | 26 |

## Edit size

Across all 139 attempted edits: median 2 changed token(s) (max 2), median 1 changed line(s) (max 1).

## Harness check

139 of 139 unedited controls reproduced the recorded failure; 0 did not and are
excluded from every rate above (listed in `mechanical_repairs.csv` with `control_unedited_fails = False`).

## Reading

Rates are conditional on eligibility: a record whose proof never names the implementation in an `unfold`,
`simp` or `dsimp` invocation cannot be edited by these templates and is reported as ineligible, not as a
repair failure. This bounds the practical cost of the measured structural brittleness for one class of
proofs; it is not a re-proving experiment and says nothing about proofs outside that class.

Row-level data: `mechanical_repairs.csv`; every before/after diff is in `mechanical_repair_diffs/`;
eligibility decisions are in `artifacts/mechanical_repairs/eligibility_ledger.json`.
