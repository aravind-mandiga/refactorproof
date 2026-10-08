# Mechanism annotation audit

The mechanism categories are **post hoc and observational**. They describe, with fixed textual
patterns applied in a fixed priority order, how a frozen proof reaches the implementation. They are not
estimates of a causal effect of a tactic: nothing here randomizes the tactic a model chooses.

## Annotation rules (applied in this order)

| Priority | Category | Pattern |
|---|---|---|
| 1 | `rfl_equation` | `have _ : <f> ... = ... := rfl` (or `:= by rfl`) |
| 2 | `unfold` | `unfold ... <f>` |
| 3 | `simp[f]` | `simp`/`simp_all`/`dsimp`/`simpa`/`simp only` with `<f>` in the lemma list |
| 4 | `rw[f]` | `rw`/`rewrite`/`rwa` with `<f>` in the rewrite list |
| 5 | `none` | the proof never names the target function in a bridging tactic |

Records annotated: 185 (110 structural, 75 semantic). 
Unambiguous: 185 of 185 (100.0%); the rest contain more than one bridging construct and are
assigned by priority, with every matched category listed in `all_matched_categories`.

## Mechanism distribution

| Class | Mechanism | Records | Tasks | Survived |
|---|---|---|---|---|
| structural | `rfl_equation` | 12 | 6 | 12 |
| structural | `rw[f]` | 2 | 2 | 0 |
| structural | `simp[f]` | 92 | 31 | 10 |
| structural | `unfold` | 4 | 3 | 0 |
| semantic | `rfl_equation` | 4 | 3 | 0 |
| semantic | `rw[f]` | 2 | 2 | 0 |
| semantic | `simp[f]` | 67 | 19 | 56 |
| semantic | `unfold` | 2 | 2 | 1 |

## Contrasts by individual prover source

Confidence intervals resample whole tasks and keep every record from a sampled task (10,000 replicates, seed 20260909).

| Contrast | Proof source | Group A (rfl bridge) | Group B | Delta | 95% CI | Tasks A |
|---|---|---|---|---|---|---|
| structural_rfl_vs_all_other | all_provers | 12 records, 100.0% | 98 records, 10.2% | +89.8 | [80.4, 97.2] | 6 |
| structural_rfl_vs_all_other | deepseek-prover-v2-7b | 2 records, 100.0% | 37 records, 8.1% | +91.9 | [82.9, 100.0] | 2 |
| structural_rfl_vs_all_other | goedel-prover-v2-8b | 5 records, 100.0% | 33 records, 12.1% | +87.9 | [75.0, 97.2] | 4 |
| structural_rfl_vs_all_other | goedel-prover-v2-32b | 5 records, 100.0% | 28 records, 10.7% | +89.3 | [76.7, 100.0] | 4 |
| structural_rfl_vs_all_other__one_record_per_task_and_source | all_provers | 10 records, 100.0% | 73 records, 11.0% | +89.0 | [78.7, 97.2] | 6 |
| semantic_rfl_vs_simp | all_provers | 4 records, 0.0% | 67 records, 83.6% | -83.6 | [-94.2, -70.0] | 3 |
| semantic_rfl_vs_simp | deepseek-prover-v2-7b | no rfl-bridge record | 22 records | not estimable | -- | 0 |
| semantic_rfl_vs_simp | goedel-prover-v2-8b | 3 records, 0.0% | 22 records, 90.9% | -90.9 | [-100.0, -78.9] | 3 |
| semantic_rfl_vs_simp | goedel-prover-v2-32b | 1 records, 0.0% | 23 records, 73.9% | -73.9 | [-92.0, -53.3] | 1 |
| semantic_rfl_vs_simp__one_record_per_task_and_source | all_provers | 4 records, 0.0% | 46 records, 81.0% | -81.0 | [-93.6, -65.0] | 3 |

Every Group A rate above is exactly 100% (structural) or 0% (semantic). The bootstrap intervals therefore
reflect variation in the comparison group and in which tasks are resampled, and they overstate precision
about the bridge group itself. The task-level test below is the more conservative summary.

## Task-level test

A task counts once per mechanism group, as surviving if any of its records in that group survives. Tasks can
appear in both groups when different provers used different bridges; that overlap is reported.

| Contrast | rfl-bridge tasks with a survivor | Comparison tasks with a survivor | Tasks in both | Fisher exact p (two-sided) |
|---|---|---|---|---|
| structural_rfl_vs_all_other | 6/6 | 6/31 | 5 | 0.0004 |
| semantic_rfl_vs_simp | 0/3 | 17/19 | 3 | 0.0065 |

## Leave-one-task-out

| Contrast | Full-sample delta | LOTO min | LOTO max | Tasks |
|---|---|---|---|---|
| semantic_rfl_vs_simp | -83.6 | -86.2 | -81.0 | 19 |
| structural_rfl_vs_all_other | +89.8 | +89.1 | +92.6 | 32 |

## Same refactored variant, different bridge

Where one prover's proof uses an rfl-equation bridge and another prover's proof of the same task uses a
different bridge, both proofs are checked against the identical certified variant. This removes task and
variant difficulty from the comparison, at the price of very small support. Structural comparisons use
every non-rfl bridge; semantic comparisons use `simp[f]`, matching the pooled contrasts above.

| Class | Shared variants | Tasks | rfl-bridge records surviving | Comparison records surviving |
|---|---|---|---|---|
| structural | 6 | 5 | 9/9 | 2/9 |
| semantic | 3 | 3 | 0/4 | 3/5 |

## Reading

- Leave-one-task-out never changes the sign of either contrast: structural +89.1 to +92.6 points over 32 deletions, semantic -86.2 to -81.0 over 19.
- By source, the structural contrast is positive for 3 of 3 provers (deepseek-ai/DeepSeek-Prover-V2-7B, Goedel-LM/Goedel-Prover-V2-8B, Goedel-LM/Goedel-Prover-V2-32B).
- The semantic contrast is negative for Goedel-LM/Goedel-Prover-V2-8B (3 record(s), 3 task(s)), Goedel-LM/Goedel-Prover-V2-32B (1 record(s), 1 task(s)), and not estimable for deepseek-ai/DeepSeek-Prover-V2-7B, which has no semantic rfl-bridge record.
- The pooled contrasts rest on 6 distinct structural and 3 distinct semantic rfl-bridge tasks. No resampling scheme
  can enlarge that number; it is the honest limit of this analysis.

Row-level data: `mechanism_annotation_audit.csv`, `mechanism_contrasts_by_source.csv`,
`mechanism_leave_one_task_out.csv`.
