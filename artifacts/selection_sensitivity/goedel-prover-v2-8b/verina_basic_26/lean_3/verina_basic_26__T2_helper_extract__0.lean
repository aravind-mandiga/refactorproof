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
  have h_main : isEven_postcond (n) (isEven (n) h_precond) h_precond := by
    have h₁ : isEven_postcond (n) (isEven (n) h_precond) h_precond = ((isEven (n) h_precond → n % 2 = 0) ∧ (¬ isEven (n) h_precond → n % 2 ≠ 0)) := by
      rfl
    rw [h₁]
    have h₂ : isEven (n) h_precond = (n % 2 == 0) := by
      simp [isEven, h_precond]
      <;> aesop
    rw [h₂]
    constructor
    · -- Prove the first condition: (n % 2 == 0 → n % 2 = 0)
      intro h
      have h₃ : n % 2 = 0 := by
        simp_all [Int.emod_eq_emod_iff_emod_sub_eq_zero]
        <;> aesop
      simp_all
    · -- Prove the second condition: (¬(n % 2 == 0) → n % 2 ≠ 0)
      intro h
      have h₃ : n % 2 ≠ 0 := by
        simp_all [Int.emod_eq_emod_iff_emod_sub_eq_zero]
        <;> aesop
      simp_all
  exact h_main
  -- !benchmark @end proof
