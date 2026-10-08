# RefactorProof

**Accepted at VeriCodeGen: AI for Verifiable Coding, a NeurIPS 2026 workshop**
([OpenReview](https://openreview.net/forum?id=gRoX0oMTwm)).

Do machine-verified, LLM-generated Lean proofs survive **mechanically certified, behavior-preserving
refactorings** of the program they were written against?

RefactorProof turns [VERINA](https://github.com/sunblaze-ucb/verina) (189 Lean 4 tasks, 46 of which ship a
reference proof) into a robustness benchmark. An implementation is refactored; Lean separately certifies in
its own file that the refactored implementation equals the original; the specification and the proof are
held byte-for-byte fixed. The metric is the task-normalized **Proof Survival Rate** (PSR): the share of
certified variants on which the unchanged proof still compiles.

**Paper**: *How Stable Are LLM-Generated Proofs Under Program Refactoring? A Stress Test for Verifiable
Code Generation*

**Authors**: Aravind Mandiga, Guoming Li

This repository is the code and data release accompanying that paper.

## Transformation families

| Family | Rewrite | Severity | Certified variants |
| --- | --- | --- | --- |
| T1 `let_intro` | the implementation body is wrapped in a `let` binding | D (definitional) | see `results/certification_analysis.csv` |
| T2 `helper_extract` | the body moves verbatim into a private helper; the function calls it | S (structural) | " |
| T3 `comm_swap` | the operands of one commutative operator are swapped | E (semantic) | " |
| T4 `cond_invert` | a tail `if c then A else B` becomes `if not c then B else A` | E (semantic) | " |
| T5 `branch_extract` | the `else` branch moves into a private helper | S (structural) | " |

Across the 185 tasks whose original file compiles in the pinned environment, 458 candidate variants carry a
machine-checked equivalence certificate and form the benchmark.

## Invariants enforced in code

**A** the specification blocks are unchanged (SHA-256) · **B** the evaluated proof is byte-identical to the
one written against the original (SHA-256) · **C** equivalence is certified by Lean in a separate file ·
**D** the certificate is never visible to the survival file (asserted on the rendered source) · **E** no
`sorry`, `admit` or newly introduced axiom anywhere · **F** the public function header is unchanged.

`tests/test_hash_invariants.py` and `tests/test_certification.py` check A, B, E and F directly; `bash
scripts/sanity_check.sh` additionally verifies that the Lean environment matches the pins in
`configs/project.yaml`.

## Layout

```
configs/project.yaml      pinned environment: VERINA commit, Lean toolchain, Mathlib revision, protocol
configs/models.yaml       the generation protocol and every model/prompt condition that was run
src/refactorproof/
  verina_parser.py        marker-based task.lean parser with a byte-perfect round trip, spec/proof hashes
  transformations/        T1-T5 rewrites, each with its own applicability test
  generate.py             candidate generation and the candidate manifest (including inapplicable tasks)
  certify.py              separate-file equivalence certificates (rfl / simp-only / simp ladder)
  survival.py             unchanged-proof survival evaluation; evaluate_reference.py is its entry point
  gen_proofs.py           K-sample proof generation against a vLLM server, using VERINA's own prompting
  evaluate_models.py      applies each model's primary proof to every certified variant
  proof_features.py       text-level tactic and mechanism features
  stats.py                task-cluster bootstrap, paired task-level differences, sign-flip tests
  analyze.py              all canonical CSVs; make_tables.py renders the tables and figures
  revision_v2.py          the appendix analyses that need no Lean; revision_v2_lean.py the ones that do
  variant_eval.py         re-checks one fixed proof against a task's certified variants
benchmark/                the benchmark as a dataset: one record per certified variant with the original
                          and refactored implementation, its certificate and hashes, plus a task index
data/                     task lists, the VERINA audit, and the recorded Lean/Lake versions
artifacts/variants/       per variant: the rewrite, its certificate record, and each proof's check result
artifacts/certificates/   the equivalence certificate Lean files (never imported by a survival file)
results/                  raw records (*.jsonl) and the derived analysis tables (*.csv)
analysis_outputs/         the appendix analyses, one CSV or Markdown summary per question
```

## Environment

Lean **v4.18.0** with the Mathlib revision pinned in `configs/project.yaml`; every Lean compile runs as
`lake env lean` from the VERINA checkout. Mixing Lean versions invalidates the recorded results.

```bash
# Lean: install elan (https://github.com/leanprover/elan), then fetch VERINA at the pinned commit
bash scripts/setup_verina.sh          # clones, verifies the manifest hashes, pulls the Mathlib cache

# Python
python3 -m venv .venv && .venv/bin/pip install -e .
export PYTHONPATH=src
```

The generation arm additionally needs VERINA's own dependencies and vLLM; it is the only part that needs a
GPU. `scripts/` contains the SLURM job scripts used for the runs, parameterized by environment variables
(`RP_ACCOUNT`, `RP_GPU_PARTITION`, `RP_MODELS_DIR`, `RP_VENV`).

## Reproducing

Every step below reads and writes only paths inside the repository.

```bash
# 1. audit the 189 upstream tasks and compile each original implementation
python -m refactorproof.audit --verina-root external/verina --workers 24

# 2. build the benchmark: candidate rewrites, then equivalence certificates
python -m refactorproof.generate --verina-root external/verina --transformations T1 T2 T3 T4 T5 --seed 0
python -m refactorproof.certify  --verina-root external/verina --variants artifacts/variants --workers 24 --timeout 300

# 3. survival of the 46 supplied reference proofs
python -m refactorproof.evaluate_reference --verina-root external/verina --variants artifacts/variants \
    --tasks data/reference_tasks.txt --workers 24 --timeout 300

# 4. survival of each model's primary proof on every certified variant.  results/model_proofs.jsonl is
#    shipped with the repository; the generation arm that produces it is described above.
python -m refactorproof.evaluate_models --verina-root external/verina --variants artifacts/variants \
    --proofs results/model_proofs.jsonl --workers 24

# 5. analysis, tables and figures
python -m refactorproof.analyze     --results results --data data --verina-root external/verina --n-boot 10000
python -m refactorproof.make_tables --results results --out paper_artifacts

# 6. appendix analyses.  The first line expands the per-task generation summaries that the generation
#    and evaluation steps would otherwise have written; the Lean-side steps need the Lean environment.
python scripts/materialize_summaries.py
for t in reference_population model_coverage aggregation per_family noncomputable t3_selection \
         mechanism length_confound seed_sensitivity matched_weighting robust_coverage \
         matched_subset within_task_variability; do
  python -m refactorproof.revision_v2 "$t" --out analysis_outputs
done
python -m refactorproof.revision_v2_lean selection_eval --workers 24   # re-checks every valid sample
python -m refactorproof.revision_v2_lean repairs        --workers 24   # pre-registered one-line repairs
python -m refactorproof.revision_v2 selection      --out analysis_outputs
python -m refactorproof.revision_v2 repair_summary --out analysis_outputs
```

Steps 1-4 rebuild what is already shipped; steps 5-6 regenerate every reported number from the shipped
records. All randomness is seeded: the bootstrap uses 10,000 replicates resampled over tasks, and the
appendix analyses use the seed recorded in `src/refactorproof/revision_v2.py`.

## Where each reported number comes from

| Reported | File |
| --- | --- |
| Benchmark construction: applicability, certification rate, rfl share | `results/certification_analysis.csv` |
| Main PSR by proof source and severity class, with CIs | `results/main_metrics.csv`, `results/by_severity.csv`, `results/by_transformation.csv` |
| Tactic and mechanism profile per proof source | `results/proof_features.csv` |
| Matched model-vs-reference differences | `results/matched_comparison.csv` |
| Coverage@k of each generation run | `results/coverage.csv`, `results/coverage_curve.csv` |
| Prompt-condition comparisons and the transformation-class interaction | `results/strategy_comparison.csv`, `results/strategy_interaction.csv` |
| Reference-proof subset audit | `analysis_outputs/reference_population_audit.csv` |
| Alternative PSR weightings and common support | `analysis_outputs/aggregation_sensitivity.csv`, `analysis_outputs/common_support.csv` |
| Per-family matched effects | `analysis_outputs/per_family_matched.csv` |
| Sensitivity to the first-valid selection rule | `analysis_outputs/proof_selection_sensitivity.csv`, `analysis_outputs/proof_selection_matched.csv` |
| What the T3 certification procedure selects | `analysis_outputs/t3_certified_vs_rejected.csv` |
| Mechanism contrasts, leave-one-task-out, per-source | `analysis_outputs/mechanism_*.csv` |
| Pre-registered mechanical repairs | `analysis_outputs/mechanical_repairs.csv` and the diffs beside it |
| Proof-length control | `analysis_outputs/length_confound.csv` |
| Bootstrap-seed sensitivity of the matched intervals | `analysis_outputs/matched_ci_seed_sensitivity.csv` |
| Matched differences with T1 (and T2) excluded, and with families weighted equally | `analysis_outputs/matched_weighting.csv` |
| End-to-end robust coverage: proving the original task *and* surviving a sampled variant | `analysis_outputs/robust_coverage.csv` |
| Characterization of the matched tasks against the reference subset and the construction population | `analysis_outputs/matched_subset_characterization.csv`, `analysis_outputs/matched_subset_tasks.csv` |
| Within-task variability of survival across valid proofs of the same task | `analysis_outputs/within_task_variability.csv`, `analysis_outputs/within_task_variability_tasks.csv` |

## Data

`results/model_proofs.jsonl` is the canonical record of every generated sample: the proof text, its hashes,
the generation parameters, whether Lean accepted it on the original task, and the first error if not.
`results/survival_reference.jsonl` and `results/survival_models.jsonl` hold one record per
(proof, certified variant) pair; `results/survival_results.csv` is those records joined with the variant
metadata and the proof features, and is what the analysis reads.

Two entries in `configs/models.yaml` are not complete runs and are called out here so the record is not
mistaken for one: the `goedel-prover-v2-8b__unfold` prompt condition was stopped after 17 of the 189 tasks,
and `goedel-prover-v2-8b__simp` is declared but was never run. The aborted condition stays in the raw
records for completeness, and the completeness filter in `make_tables.py` keeps it out of every rendered
table. Wall-clock fields in the records are normalized to UTC.

Every shipped analysis output is byte-reproducible from the shipped records by the commands above, with two
exceptions: `results/mechanism_regression.csv` and `analysis_outputs/length_confound.csv` are maximum-likelihood
logit fits, and their coefficients reproduce to roughly twelve significant digits rather than bit-exactly,
because the optimizer is sensitive to how the input is parsed and to the machine it runs on.

Not included: the raw model responses and the per-sample Lean logs (about 3.6 GB, and regenerable with
`gen_proofs --recheck`), and the VERINA checkout itself, which `scripts/setup_verina.sh` fetches at the
pinned commit.

## Citation

```bibtex
@inproceedings{mandiga2026refactorproof,
  title     = {How Stable Are LLM-Generated Proofs Under Program Refactoring? A Stress Test for
               Verifiable Code Generation},
  author    = {Mandiga, Aravind and Li, Guoming},
  booktitle = {NeurIPS 2026 Workshop on AI for Verifiable Coding (VeriCodeGen)},
  year      = {2026},
  url       = {https://openreview.net/forum?id=gRoX0oMTwm}
}
```

## License

Apache-2.0 (see `LICENSE`). Material derived from VERINA is covered by the same license; see `NOTICE`,
which also lists every third-party asset the experiments use with its license.
