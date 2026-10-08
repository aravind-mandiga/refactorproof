# Sensitivity to the two `noncomputable` variants

Two certified variants required Lean's `noncomputable` modifier because the 4.18 code generator
refuses the wrapped body. The modifier changes neither the name, the signature, nor the logical
content, but it does matter for proofs relying on native evaluation, so every headline statistic is
recomputed with those two variants removed.

## The two variants

| Variant | Transformation | Class | Modifier |
|---|---|---|---|
| `verina_advanced_21__T1_let_intro__0` | T1_let_intro | D | `noncomputable` |
| `verina_basic_15__T1_let_intro__0` | T1_let_intro | D | `noncomputable` |

## Effect on every headline statistic

| Analysis | Source | Scope | With all variants | Excluding the two | Change (pp) |
|---|---|---|---|---|---|
| psr | reference | overall | 47.9 | 47.7 | -0.18 |
| psr | reference | D | 100.0 | 100.0 | +0.00 |
| psr | reference | S | 4.3 | 4.3 | +0.00 |
| psr | reference | E | 44.2 | 44.2 | +0.00 |
| psr | deepseek-prover-v2-7b | overall | 59.3 | 59.3 | +0.00 |
| psr | deepseek-prover-v2-7b | D | 100.0 | 100.0 | +0.00 |
| psr | deepseek-prover-v2-7b | S | 13.3 | 13.3 | +0.00 |
| psr | deepseek-prover-v2-7b | E | 72.2 | 72.2 | +0.00 |
| psr | goedel-prover-v2-8b | overall | 64.6 | 64.6 | +0.00 |
| psr | goedel-prover-v2-8b | D | 100.0 | 100.0 | +0.00 |
| psr | goedel-prover-v2-8b | S | 26.8 | 26.8 | +0.00 |
| psr | goedel-prover-v2-8b | E | 72.4 | 72.4 | +0.00 |
| psr | goedel-prover-v2-32b | overall | 64.5 | 64.5 | +0.00 |
| psr | goedel-prover-v2-32b | D | 100.0 | 100.0 | +0.00 |
| psr | goedel-prover-v2-32b | S | 26.0 | 26.0 | +0.00 |
| psr | goedel-prover-v2-32b | E | 67.6 | 67.6 | +0.00 |
| matched_diff | deepseek-prover-v2-7b | all | 15.6 | 15.6 | +0.00 |
| matched_diff | deepseek-prover-v2-7b | S | 14.0 | 14.0 | +0.00 |
| matched_diff | deepseek-prover-v2-7b | E | 37.8 | 37.8 | +0.00 |
| matched_diff | goedel-prover-v2-8b | all | 20.3 | 20.3 | +0.00 |
| matched_diff | goedel-prover-v2-8b | S | 21.7 | 21.7 | +0.00 |
| matched_diff | goedel-prover-v2-8b | E | 42.8 | 42.8 | +0.00 |
| matched_diff | goedel-prover-v2-32b | all | 18.8 | 18.8 | +0.00 |
| matched_diff | goedel-prover-v2-32b | S | 23.8 | 23.8 | +0.00 |
| matched_diff | goedel-prover-v2-32b | E | 29.8 | 29.8 | +0.00 |

## Reading

The largest absolute change across every reported statistic is 0.18 percentage points.
No qualitative conclusion depends on these two variants.

Row-level data: `noncomputable_sensitivity.csv`.
