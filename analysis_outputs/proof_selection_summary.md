# First-valid proof sensitivity

Every valid sample of every evaluated checkpoint was re-checked in the pinned Lean environment on all
certified variants of its task (334 valid proof artifacts) on a
24-core CPU node. No proof was generated. Confidence intervals are task-cluster bootstrap percentile intervals
(10,000 replicates, seed 20260909).

## Selection rules

| Rule | Definition |
|---|---|
| `first_valid` | first Lean-valid sample in fixed sample order (the paper's primary analysis) |
| `shortest_valid` | valid sample with the fewest proof tokens (regex tokens of the proof block); ties go to the earliest sample. The metric was fixed in code before any PSR under this rule was computed |
| `random_valid` | one valid sample drawn uniformly at random per task; 1,000 deterministic draws with a fixed seed |
| `all_valid_mean` | per task, mean PSR over all of its valid samples; then unweighted mean over tasks |
| `best_valid_oracle` | POST HOC ORACLE: per task, the valid sample with the highest PSR. Not a deployable selection rule |
| `worst_valid_oracle` | POST HOC ORACLE: per task, the valid sample with the lowest PSR. Not a deployable selection rule |

## Consistency check

Re-evaluating each first valid sample reproduces the frozen primary survival records on 301
of 301 (model, variant) outcomes (0 mismatches).

## How much room the rules have

| Model | Tasks with >=1 valid sample | Tasks with >1 valid sample | Tasks where shortest != first |
|---|---|---|---|
| Qwen/Qwen3-14B | 5 | 2 | 0 |
| Qwen/Qwen3-32B | 5 | 2 | 2 |
| Goedel-LM/Goedel-Prover-V2-8B | 29 | 25 | 17 |
| Goedel-LM/Goedel-Prover-V2-32B | 26 | 24 | 20 |
| deepseek-ai/DeepSeek-Prover-V2-7B | 31 | 26 | 16 |

## Task-normalized PSR under each rule (all certified variants)

| Model | `first_valid` | `shortest_valid` | `random_valid` | `all_valid_mean` | `best_valid_oracle` | `worst_valid_oracle` |
|---|---|---|---|---|---|---|
| Qwen/Qwen3-14B | 38.3 | 38.3 | 38.3 | 38.3 | 38.3 | 38.3 |
| Qwen/Qwen3-32B | 58.3 | 58.3 | 58.3 | 58.3 | 58.3 | 58.3 |
| Goedel-LM/Goedel-Prover-V2-8B | 64.6 | 65.4 | 64.4 | 64.5 | 69.7 | 56.7 |
| Goedel-LM/Goedel-Prover-V2-32B | 64.5 | 70.1 | 66.8 | 66.7 | 76.1 | 55.5 |
| deepseek-ai/DeepSeek-Prover-V2-7B | 59.3 | 55.8 | 59.7 | 59.7 | 65.2 | 50.6 |

## Matched specialized prover minus reference, under each rule

Delta in percentage points with 95% task-cluster bootstrap CI, on exactly the matched variant set.

| Model | Class | Tasks | `first_valid` | `shortest_valid` | `random_valid` | `all_valid_mean` | `best_valid_oracle` | `worst_valid_oracle` |
|---|---|---|---|---|---|---|---|---|
| deepseek-ai/DeepSeek-Prover-V2-7B | all | 25 | +15.6 [8.0, 24.0] | +11.3 [4.9, 18.6] | +15.6 [9.4, 22.0] | +15.5 [9.4, 22.0] | +21.6 [13.3, 29.7] | +4.8 [1.1, 9.0] |
| deepseek-ai/DeepSeek-Prover-V2-7B | structural | 25 | +14.0 [0.0, 28.0] | +8.0 [-2.0, 22.0] | +19.5 [7.9, 31.3] | +19.5 [7.9, 31.3] | +42.0 [22.0, 62.0] | -2.0 [-6.0, 0.0] |
| deepseek-ai/DeepSeek-Prover-V2-7B | semantic | 15 | +37.8 [15.6, 62.2] | +37.8 [6.7, 66.7] | +34.6 [9.1, 60.0] | +34.4 [9.1, 60.0] | +51.1 [26.7, 75.6] | +11.1 [-13.3, 37.8] |
| Goedel-LM/Goedel-Prover-V2-8B | all | 23 | +20.3 [12.0, 28.7] | +22.4 [13.8, 31.0] | +20.7 [13.3, 28.2] | +20.7 [13.3, 28.2] | +26.8 [18.0, 35.5] | +11.4 [4.5, 19.3] |
| Goedel-LM/Goedel-Prover-V2-8B | structural | 23 | +21.7 [4.3, 41.3] | +21.7 [4.3, 39.1] | +22.8 [8.0, 38.6] | +22.9 [8.0, 38.6] | +37.0 [17.4, 56.5] | +6.5 [-4.3, 19.6] |
| Goedel-LM/Goedel-Prover-V2-8B | semantic | 15 | +42.8 [13.3, 71.7] | +51.1 [26.7, 75.6] | +42.0 [13.8, 68.5] | +41.8 [13.8, 68.5] | +57.8 [33.3, 82.2] | +16.7 [-13.3, 46.7] |
| Goedel-LM/Goedel-Prover-V2-32B | all | 21 | +18.8 [9.9, 27.8] | +24.5 [15.8, 33.7] | +20.9 [13.7, 28.5] | +20.9 [13.7, 28.5] | +30.9 [23.0, 38.4] | +8.9 [2.4, 16.8] |
| Goedel-LM/Goedel-Prover-V2-32B | structural | 21 | +23.8 [4.8, 42.9] | +38.1 [16.7, 59.5] | +24.8 [12.4, 38.6] | +24.8 [12.4, 38.6] | +50.0 [31.0, 69.0] | +2.4 [-7.1, 14.3] |
| Goedel-LM/Goedel-Prover-V2-32B | semantic | 14 | +29.8 [0.0, 59.5] | +26.2 [-9.5, 61.9] | +34.8 [10.7, 58.3] | +34.4 [10.7, 58.3] | +61.9 [35.7, 85.7] | +8.3 [-21.4, 38.1] |

## Reading

No matched comparison changes sign under any deployable rule.

Matched comparisons under a deployable rule whose 95% CI does not exclude zero:

- Goedel-LM/Goedel-Prover-V2-32B, semantic, `first_valid`: +29.8 [0.0, 59.5]
- Goedel-LM/Goedel-Prover-V2-32B, semantic, `shortest_valid`: +26.2 [-9.5, 61.9]
- deepseek-ai/DeepSeek-Prover-V2-7B, structural, `first_valid`: +14.0 [0.0, 28.0]
- deepseek-ai/DeepSeek-Prover-V2-7B, structural, `shortest_valid`: +8.0 [-2.0, 22.0]

`random_valid` and `all_valid_mean` coincide in expectation by construction; the draw percentiles in
`proof_selection_sensitivity.csv` and `proof_selection_matched.csv` show how much the benchmark-level
number moves with the luck of which valid proof is picked. The two oracle columns are post hoc bounds and
are not selection rules anyone could deploy.

Row-level data: `proof_selection_sensitivity.csv`, `proof_selection_matched.csv`.
