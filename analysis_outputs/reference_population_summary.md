# Audit of the reference-proof subset

Source of truth: the `proof` marker block of each `external/verina/datasets/verina/<task>/task.lean`,
the certificate log, and the candidate manifest. Seed 20260909.

## Populations

| Population | Count |
|---|---|
| VERINA tasks in the local dataset | 189 |
| Tasks whose original compiles in the pinned environment | 185 |
| Tasks with a supplied reference proof | 46 |
| Tasks with a supplied reference proof that also compile | 46 |
| Certified RefactorProof variants contributed by reference-proof tasks | 130 |
| Certified variants in total | 458 |

## Why the other tasks have no reference proof

| Reason (read from the source proof block) | Tasks |
|---|---|
| `sorry` | 143 |
| `supplied` | 46 |

Every excluded task carries an explicit `sorry` placeholder in its proof block, so the exclusion is a
property of the VERINA release rather than a filtering choice made here.

## Reference-proof tasks compared with the rest of the construction population

Comparison is against the other tasks in the 185-task construction population. Reference-proof length is
reported only within the subset that has a reference proof; for tasks without one it is undefined and is
**not** imputed.

| Characteristic | Reference-proof tasks | Other construction tasks | Test |
|---|---|---|---|
| Tasks | 46 | 139 | |
| Median implementation LoC | 1.0 | 8.0 | Mann-Whitney p = 2.04e-11 |
| Median implementation tokens | 13.0 | 57.0 | Mann-Whitney p = 1.72e-10 |
| Median applicable transformation families | 2.0 | 3.0 | Mann-Whitney p = 5.59e-01 |
| Recursive implementation | 6.5% | 54.0% | Fisher p = 2.91e-09 |
| VERINA `advanced` category | 0.0% | 56.1% | Fisher p = 9.14e-14 |
| Median reference-proof LoC | 11.0 | undefined (no reference proof) | not comparable |

## Reading

The reference arm is not a random sample of the construction population. Reference-proof tasks have much
shorter implementations (median 1 vs 8 lines, Mann-Whitney p = 2.0e-11), are far less
often recursive (6.5% vs 54.0%, Fisher p = 2.9e-09), and none is in the `advanced`
split (56.1% of the other tasks are). The number of applicable transformation families does
not differ detectably (median 2 vs 3, p = 0.56).

Standalone reference PSR therefore describes VERINA's simplest tasks. Matched model-versus-reference
comparisons are internally unaffected by this selection, because they hold the task set and the variant set
fixed across the two proof sources, but they are restricted to these simpler tasks and do not speak to the
recursive or `advanced` part of VERINA.

Row-level data: `reference_population_audit.csv`.
