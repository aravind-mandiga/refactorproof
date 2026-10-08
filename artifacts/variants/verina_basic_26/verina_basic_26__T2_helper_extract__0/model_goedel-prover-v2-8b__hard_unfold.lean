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

private def isEven__rp_helper_3a986bdd (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  n % 2 == 0
-- !benchmark @end code_aux


def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  -- !benchmark @start code
  isEven__rp_helper_3a986bdd n h_precond
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
  unfold isEven isEven_postcond
  have h_main : (isEven (n) h_precond → n % 2 = 0) ∧ (¬ isEven (n) h_precond → n % 2 ≠ 0) := by
    constructor
    · -- Prove the first implication: isEven (n) h_precond → n % 2 = 0
      intro h
      -- Since isEven (n) h_precond is n % 2 = 0, this is trivially true
      simp_all [isEven, isEven_precond, isEven_postcond]
      <;> aesop
    · -- Prove the second implication: ¬ isEven (n) h_precond → n % 2 ≠ 0
      intro h
      -- Since ¬ isEven (n) h_precond is ¬ (n % 2 = 0), this is equivalent to n % 2 ≠ 0
      simp_all [isEven, isEven_precond, isEven_postcond]
      <;> aesop
  -- Use the main result to conclude the proof
  simpa [isEven, isEven_precond, isEven_postcond] using h_main
  -- !benchmark @end proof
