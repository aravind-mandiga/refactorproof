-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isEven_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  -- !benchmark @start code
  let __rp_tmp_a74ca03e : Bool :=
    n % 2 == 0
  __rp_tmp_a74ca03e
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isEven_postcond (n : Int) (result: Bool) (h_precond : isEven_precond (n)) :=
  -- !benchmark @start postcond
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isEven_spec_satisfied (n: Int) (h_precond : isEven_precond (n)) :
    isEven_postcond (n) (isEven (n) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : isEven_postcond n (isEven n h_precond) h_precond := by
    simp only [isEven_postcond, isEven_precond, isEven, and_true]
    -- Simplify the goal using the definitions and properties of parity
    <;>
    by_cases h : n % 2 = 0 <;>
    simp_all [Int.emod_emod]
    <;>
    (try { omega }) <;>
    (try { aesop }) <;>
    (try {
      norm_num at *
      <;>
      omega }) <;>
    (try {
      simp_all [Int.emod_emod]
      <;>
      omega })
    <;>
    aesop

  exact h_main
  -- !benchmark @end proof
