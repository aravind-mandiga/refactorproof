# The RefactorProof benchmark

RefactorProof contains 458 certified variants across 180 of the 185 VERINA
tasks that compile in the pinned environment. Each variant rewrites the implementation of a task, leaves its
specification and its proof untouched byte-for-byte, and carries a Lean proof that the rewritten
implementation equals the original one. The question the benchmark asks is whether a proof written against
the original program still compiles against the refactored one. The remaining 5
compiling tasks have no variant because no transformation applies or none certifies.

## Files

| File | Contents |
| --- | --- |
| `variants.jsonl` | one record per certified variant: the original and refactored implementation, the certificate, and the hashes that pin the specification and proof |
| `tasks.csv` | one row per task: tier, whether VERINA supplies a reference proof, and how many variants of each family it has |

The Lean sources themselves stay where the pipeline writes them: the equivalence certificates in
`artifacts/certificates/<task>/<variant>.lean`, and the compiled evaluation files in the `variant_dir` each
record names. `results/` holds the raw survival records and the analysis tables.

## Composition

| Family | Rewrite | Class | Variants |
| --- | --- | --- | --- |
| T1 `let_intro` | the implementation body is wrapped in a `let` binding | D (definitional) | 180 |
| T2 `helper_extract` | the body moves verbatim into a private helper that the function calls | S (structural) | 178 |
| T3 `comm_swap` | the operands of one commutative operator are swapped | E (semantic) | 50 |
| T4 `cond_invert` | a tail `if c then A else B` becomes `if not c then B else A` | E (semantic) | 32 |
| T5 `branch_extract` | the `else` branch moves into a private helper | S (structural) | 18 |

By class: 180 definitional, 196 structural, 82 semantic.
378 of 458 certificates close by reflexivity; the rest need a simp-based ladder, recorded per
variant in `certificate_level`. 46 of the 180 tasks have a reference proof supplied
upstream by VERINA.

## What each record guarantees

Every variant satisfies, checked in code rather than by inspection:

**A** the specification blocks are unchanged (`spec_hash`) · **B** the evaluated proof is byte-identical to
the one written against the original (`proof_hash`) · **C** the equivalence is proved by Lean in a separate
file · **D** that certificate is never visible to the file the proof is checked in · **E** no `sorry`,
`admit`, or newly introduced axiom · **F** the public function signature is unchanged.

The certificate and the evaluation file are rendered from the same record, so the refactored implementation
cannot differ between them; `src/refactorproof/survival.py` asserts the hashes above, and that none of
`rp_equiv`, `RPOrig`, `RPRef` appears in the evaluated source, before compiling.

## Using it

```python
import json
variants = [json.loads(l) for l in open("benchmark/variants.jsonl")]
semantic = [v for v in variants if v["severity"] == "E"]          # the hard cases
t2 = [v for v in variants if v["transformation"] == "T2_helper_extract"]
```

To evaluate a proof of your own, put it in the task's proof block and compile the task with
`refactored_code` in place of the original implementation; `src/refactorproof/survival.py` does exactly this
and enforces the invariants while doing so. Report Coverage@k, conditional PSR, and the end-to-end
combination of the two, as the paper does.

## Provenance and license

Derived from [VERINA](https://github.com/sunblaze-ucb/verina) at the commit pinned in
`configs/project.yaml`, under Apache-2.0. The specification and proof blocks of each task are reproduced
unchanged; only the implementation is rewritten. See `NOTICE`.
