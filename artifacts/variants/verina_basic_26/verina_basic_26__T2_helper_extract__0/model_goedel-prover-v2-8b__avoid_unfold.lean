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
  have h₁ : (isEven (n) h_precond → (n % 2 = 0)) := by
    intro h
    have h₂ : isEven (n) h_precond = (n % 2 == 0) := rfl
    rw [h₂] at h
    -- Now we need to show that if n % 2 == 0 is true, then n % 2 = 0.
    -- This is straightforward because n % 2 == 0 is defined as n % 2 = 0 in Lean.
    simpa [Int.emod_eq_of_lt] using h

  have h₂ : (¬ isEven (n) h_precond → (n % 2 ≠ 0)) := by
    intro h
    have h₃ : isEven (n) h_precond = (n % 2 == 0) := rfl
    rw [h₃] at h
    -- Now we need to show that if ¬ (n % 2 == 0), then n % 2 ≠ 0.
    -- This is straightforward because n % 2 == 0 is defined as n % 2 = 0 in Lean.
    by_contra h₄
    -- Assume n % 2 = 0.
    have h₅ : n % 2 = 0 := by simpa [Int.emod_eq_of_lt] using h₄
    -- Since n % 2 = 0, we have n % 2 == 0.
    have h₆ : (n % 2 == 0) := by simpa [Int.emod_eq_of_lt] using h₅
    -- This contradicts the assumption that ¬ (n % 2 == 0).
    contradiction

  have h₃ : isEven_postcond (n) (isEven (n) h_precond) h_precond := by
    constructor
    · -- Prove the first part: isEven (n) h_precond → n % 2 = 0
      intro h
      exact h₁ h
    · -- Prove the second part: ¬ isEven (n) h_precond → n % 2 ≠ 0
      intro h
      exact h₂ h

  exact h₃
  -- !benchmark @end proof
