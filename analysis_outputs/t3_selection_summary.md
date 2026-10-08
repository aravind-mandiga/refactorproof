# What the T3 certification procedure selects

T3 commutative-swap candidates over the 185-task construction population: 122 generated,
50 certified (41.0%), 72 rejected. This matches Table 1 of the paper.
A further 4 candidates come from applicable tasks whose originals do not compile in the pinned
environment and are excluded from benchmark construction. This is descriptive selection analysis, not a
causal model.

## Certified versus rejected candidates

| Characteristic | Certified | Rejected | Test |
|---|---|---|---|
| Candidates | 50 | 72 | |
| Distinct tasks | 34 | 48 | |
| Median implementation LoC | 10.5 | 13.0 | Mann-Whitney p = 1.74e-02 |
| Median implementation tokens | 97.0 | 88.0 | Mann-Whitney p = 1.43e-01 |
| Recursive implementation | 14.0% | 98.6% | Fisher p = 2.20e-24 |
| Self-recursive | 0.0% | 5.6% | Fisher p = 1.43e-01 |
| Contains `let rec` | 14.0% | 97.2% | Fisher p = 4.51e-23 |
| Contains `where` clause | 0.0% | 1.4% | Fisher p = 1.00e+00 |
| Non-empty helper region | 16.0% | 2.8% | Fisher p = 1.52e-02 |
| VERINA `advanced` category | 50.0% | 47.2% | |
| Has a VERINA reference proof | 30.0% | 2.8% | Fisher p = 2.38e-05 |

## Swapped operator

| Operator | Certified | Rejected | Certification rate |
|---|---|---|---|
| `&&` | 1 | 1 | 50.0% |
| `*` | 15 | 2 | 88.2% |
| `+` | 33 | 68 | 32.7% |
| `||` | 1 | 0 | 100.0% |
| `∧` | 0 | 1 | 0.0% |

## Reference-proof length, within the subset that has one

Certified candidates: n = 15, median reference-proof LoC 8.0. Rejected: n = 2, median 101.5. Tasks without a reference proof are excluded from this row rather than imputed.

## Why candidates are rejected

| Certificate failure category | Candidates |
|---|---|
| tactic_failed | 72 |

## Reading

Recursion is the dominant separator: 14.0% of certified candidates sit in a recursive
implementation versus 98.6% of rejected ones (Fisher p = 2.2e-24), almost always through a
`let rec` helper, where pointwise equality needs task-specific induction that the fixed certificate ladder
does not synthesize. Length differences are small and not consistent across metrics: certified bodies are
shorter in lines (median 10.5 vs 13.0, p = 0.017) but not in tokens (median
97 vs 88, p = 0.14). The certified semantic suite is therefore biased
towards non-recursive implementations, and semantic-class conclusions apply to that certified subset only.

Row-level data: `t3_certified_vs_rejected.csv`.
