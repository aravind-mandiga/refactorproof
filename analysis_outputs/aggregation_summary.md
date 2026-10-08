# Alternative PSR aggregation and common support

Every aggregate below is recomputed from `results/survival_results.csv`. Confidence intervals are
task-cluster bootstrap percentile intervals over 10,000 replicates, seed 20260909.

## Weighting formulas

| Aggregation | Formula |
|---|---|
| `task_normalized` | mean over tasks of (mean over that task's certified variants) |
| `excluding_T1` | same, restricted to variants outside T1 |
| `family_balanced` | mean over tasks of (mean over that task's available families of (mean over that family's variants)) |
| `one_per_task_family_cell` | unweighted mean over (task, family) cells, averaging multiple variants of a family first |

## Results

| Source | Aggregation | PSR (%) | 95% CI | Tasks |
|---|---|---|---|---|
| reference | task_normalized | 47.9 | [44.1, 52.0] | 46 |
| reference | excluding_T1 | 11.5 | [5.7, 18.1] | 46 |
| reference | family_balanced | 48.4 | [44.8, 52.2] | 46 |
| reference | one_per_task_family_cell | 46.8 | [42.5, 51.3] | 46 |
| deepseek-prover-v2-7b | task_normalized | 59.3 | [52.3, 66.7] | 31 |
| deepseek-prover-v2-7b | excluding_T1 | 32.0 | [20.0, 44.6] | 30 |
| deepseek-prover-v2-7b | family_balanced | 58.2 | [51.4, 65.4] | 31 |
| deepseek-prover-v2-7b | one_per_task_family_cell | 56.7 | [51.0, 62.5] | 31 |
| goedel-prover-v2-8b | task_normalized | 64.6 | [57.7, 71.8] | 29 |
| goedel-prover-v2-8b | excluding_T1 | 43.8 | [31.9, 56.0] | 28 |
| goedel-prover-v2-8b | family_balanced | 63.7 | [56.7, 70.9] | 29 |
| goedel-prover-v2-8b | one_per_task_family_cell | 61.0 | [55.6, 67.0] | 29 |
| goedel-prover-v2-32b | task_normalized | 64.5 | [56.5, 72.8] | 26 |
| goedel-prover-v2-32b | excluding_T1 | 43.7 | [30.4, 57.1] | 25 |
| goedel-prover-v2-32b | family_balanced | 63.7 | [55.9, 71.9] | 26 |
| goedel-prover-v2-32b | one_per_task_family_cell | 60.7 | [54.4, 67.5] | 26 |

## Common-support matched comparisons

Pairwise common support uses exactly the (task, family) cells present for both the model and the
reference. The four-source support additionally requires the cell to exist for all three provers.

| Comparison | Support | Cells | Tasks | Model PSR | Reference PSR | Delta | 95% CI |
|---|---|---|---|---|---|---|---|
| deepseek-prover-v2-7b_vs_reference | pairwise_common_cells | 75 | 25 | 59.2 | 43.6 | +15.6 | [8.0, 24.0] |
| goedel-prover-v2-8b_vs_reference | pairwise_common_cells | 71 | 23 | 63.4 | 43.0 | +20.3 | [12.0, 28.7] |
| goedel-prover-v2-32b_vs_reference | pairwise_common_cells | 65 | 21 | 62.4 | 43.5 | +18.8 | [9.9, 27.8] |
| deepseek-prover-v2-7b_vs_reference | four_source_common_cells | 65 | 21 | 60.9 | 43.5 | +17.4 | [8.3, 26.8] |
| goedel-prover-v2-8b_vs_reference | four_source_common_cells | 65 | 21 | 64.6 | 43.5 | +21.1 | [12.3, 30.2] |
| goedel-prover-v2-32b_vs_reference | four_source_common_cells | 65 | 21 | 62.4 | 43.5 | +18.8 | [9.9, 27.8] |

The four-source common support contains 65 (task, family) cells over 21 tasks.

## Reading

- Reference proofs have the lowest PSR under every aggregation: yes.
- DeepSeek-Prover-V2-7B is below both Goedel models under every aggregation: yes. The two
  Goedel models differ by at most 0.3 points under any aggregation, so their relative order carries no information.
- Family-balanced and cell-level weighting move any source's PSR by at most 3.8 points from the task-normalized value.
- Excluding T1 lowers every absolute PSR, because every source survives T1 universally, without reordering the
  sources: deepseek-prover-v2-7b 32.0%, goedel-prover-v2-32b 43.7%, goedel-prover-v2-8b 43.8%, reference 11.5%.
- On the four-source common support (65 cells, 21 tasks) every prover's matched difference is
  positive with a 95% CI excluding zero: yes.

Row-level data: `aggregation_sensitivity.csv`, `common_support.csv`.
