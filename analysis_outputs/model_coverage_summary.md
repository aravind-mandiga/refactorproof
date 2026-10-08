# Model generation coverage

Denominator is all 189 VERINA tasks attempted by the generation protocol (K=5 samples per
task, fixed order, first Lean-valid sample is the primary artifact). Computed from the per-attempt
`original_proof_valid` flags in `artifacts/model_proofs/<model>/<task>/summary.json`.

## Coverage@k over all 189 attempted tasks

| Model | Coverage@1 | @2 | @3 | @4 | @5 | Tasks with >=1 valid | Valid artifacts |
|---|---|---|---|---|---|---|---|
| Qwen/Qwen3-14B | 0.5% | 1.6% | 2.1% | 2.6% | 2.6% | 5 (2.6%) | 8 |
| Qwen/Qwen3-32B | 1.6% | 1.6% | 2.1% | 2.6% | 2.6% | 5 (2.6%) | 7 |
| Goedel-LM/Goedel-Prover-V2-8B | 9.5% | 14.3% | 14.3% | 14.8% | 15.3% | 29 (15.3%) | 100 |
| Goedel-LM/Goedel-Prover-V2-32B | 11.6% | 13.2% | 13.2% | 13.8% | 13.8% | 26 (13.8%) | 108 |
| deepseek-ai/DeepSeek-Prover-V2-7B | 12.7% | 14.3% | 14.3% | 16.4% | 16.4% | 31 (16.4%) | 111 |

## Distribution of valid samples per task

| Model | 0 valid | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| Qwen/Qwen3-14B | 184 | 3 | 1 | 1 | 0 | 0 |
| Qwen/Qwen3-32B | 184 | 3 | 2 | 0 | 0 | 0 |
| Goedel-LM/Goedel-Prover-V2-8B | 160 | 4 | 5 | 4 | 6 | 10 |
| Goedel-LM/Goedel-Prover-V2-32B | 163 | 2 | 1 | 4 | 3 | 16 |
| deepseek-ai/DeepSeek-Prover-V2-7B | 158 | 5 | 5 | 2 | 5 | 14 |

## Reading

Coverage@5 equals the share of tasks with at least one valid sample, so the two columns agree by
construction. All survival results are conditional on this coverage: a model contributes a task to
PSR only where it produced a Lean-valid proof of the original implementation.

Row-level data: `model_coverage.csv`, `valid_sample_distribution.csv`.
