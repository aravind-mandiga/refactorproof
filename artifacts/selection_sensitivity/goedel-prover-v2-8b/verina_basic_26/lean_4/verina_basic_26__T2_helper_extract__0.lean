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
  have h1 : (isEven (n) h_precond → n % 2 = 0) := by
    intro h
    have h₂ : n % 2 == 0 := by simpa [isEven] using h
    have h₃ : n % 2 = 0 := by
      -- Since `n % 2 == 0` is `n % 2 = 0`, we can directly use this fact.
      norm_num [Int.emod_eq_of_lt] at h₂ ⊢ <;> omega
    exact h₃

  have h2 : (¬ isEven (n) h_precond → n % 2 ≠ 0) := by
    intro h
    have h₂ : ¬(n % 2 == 0) := by simpa [isEven] using h
    have h₃ : n % 2 ≠ 0 := by
      by_contra h₄
      -- If n % 2 = 0, then n % 2 == 0, contradicting h₂.
      have h₅ : n % 2 == 0 := by simpa [Int.emod_eq_zero_of_dvd] using h₄
      contradiction
    exact h₃

  have h3 : isEven_postcond (n) (isEven (n) h_precond) h_precond := by
    constructor
    · -- Prove the first part: isEven (n) h_precond → n % 2 = 0
      exact h1
    · -- Prove the second part: ¬ isEven (n) h_precond → n % 2 ≠ 0
      exact h2

  exact h3
  -- !benchmark @end proof
