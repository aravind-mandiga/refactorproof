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
  have h_main : n % 2 = 0 ∨ n % 2 = 1 := by
    have h₁ : n % 2 = 0 ∨ n % 2 = 1 := by
      have h₂ : 0 ≤ n % 2 := by
        -- Prove that n % 2 is non-negative
        have h₃ : 0 ≤ n % 2 := by
          apply Int.emod_nonneg
          <;> norm_num
        exact h₃
      have h₃ : n % 2 < 2 := by
        -- Prove that n % 2 is less than 2
        have h₄ : n % 2 < 2 := by
          have h₅ : n % 2 < 2 := by
            omega
          exact h₅
        exact h₄
      -- Since n % 2 is an integer between 0 and 2, it must be either 0 or 1
      have h₄ : n % 2 = 0 ∨ n % 2 = 1 := by
        have h₅ : n % 2 ≥ 0 := h₂
        have h₆ : n % 2 < 2 := h₃
        have h₇ : n % 2 ≤ 1 := by
          omega
        interval_cases n % 2 <;> norm_num at h₅ h₆ h₇ ⊢ <;> omega
      exact h₄
    exact h₁

  have h_final : isEven_postcond (n) (isEven (n) h_precond) h_precond := by
    have h₁ : (isEven (n) h_precond → n % 2 = 0) ∧ (¬isEven (n) h_precond → n % 2 ≠ 0) := by
      cases h_main with
      | inl h₂ =>
        -- Case: n % 2 = 0
        have h₃ : isEven (n) h_precond = true := by
          simp [isEven, h₂]
          <;> norm_num
          <;> rfl
        have h₄ : (isEven (n) h_precond → n % 2 = 0) := by
          rw [h₃]
          simp [h₂]
        have h₅ : (¬isEven (n) h_precond → n % 2 ≠ 0) := by
          rw [h₃]
          intro h₆
          simp_all
        exact ⟨h₄, h₅⟩
      | inr h₂ =>
        -- Case: n % 2 = 1
        have h₃ : isEven (n) h_precond = false := by
          simp [isEven, h₂]
          <;> norm_num
          <;> rfl
        have h₄ : (isEven (n) h_precond → n % 2 = 0) := by
          rw [h₃]
          intro h₅
          simp_all
        have h₅ : (¬isEven (n) h_precond → n % 2 ≠ 0) := by
          rw [h₃]
          intro h₆
          simp_all [h₂]
          <;> norm_num at *
          <;> omega
        exact ⟨h₄, h₅⟩
    simpa [isEven_postcond] using h₁

  exact h_final
  -- !benchmark @end proof
