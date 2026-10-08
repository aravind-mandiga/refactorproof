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
  have h_main : (isEven (n) h_precond → n % 2 = 0) ∧ (¬ isEven (n) h_precond → n % 2 ≠ 0) := by
    by_cases h : n % 2 = 0
    · -- Case 1: n % 2 = 0
      have h₁ : isEven (n) h_precond = true := by
        simp [isEven, h, Int.emod_eq_of_lt]
        <;> norm_num
      constructor
      · -- Prove (isEven (n) h_precond → n % 2 = 0)
        intro h₂
        rw [h₁] at h₂
        simp at h₂
        <;> simp_all
      · -- Prove (¬ isEven (n) h_precond → n % 2 ≠ 0)
        intro h₂
        rw [h₁] at h₂
        simp at h₂
        <;> simp_all
    · -- Case 2: n % 2 ≠ 0
      have h₁ : isEven (n) h_precond = false := by
        simp [isEven]
        <;>
        (try norm_num) <;>
        (try
          {
            have h₂ : n % 2 ≠ 0 := h
            have h₃ : n % 2 = 1 ∨ n % 2 = -1 := by
              have h₄ : n % 2 = 1 ∨ n % 2 = -1 := by
                have : n % 2 = 1 ∨ n % 2 = -1 := by
                  have h₅ : n % 2 = 1 ∨ n % 2 = -1 := by
                    omega
                  exact h₅
                exact this
              exact h₄
            cases h₃ with
            | inl h₃ =>
              simp [h₃]
              <;> norm_num
            | inr h₃ =>
              simp [h₃]
              <;> norm_num
          }) <;>
        (try omega)
      constructor
      · -- Prove (isEven (n) h_precond → n % 2 = 0)
        intro h₂
        rw [h₁] at h₂
        simp at h₂
        <;> simp_all
      · -- Prove (¬ isEven (n) h_precond → n % 2 ≠ 0)
        intro h₂
        rw [h₁] at h₂
        simp at h₂
        <;> simp_all
  -- Use the main result to prove the postcondition
  simpa [isEven_postcond] using h_main
  -- !benchmark @end proof
