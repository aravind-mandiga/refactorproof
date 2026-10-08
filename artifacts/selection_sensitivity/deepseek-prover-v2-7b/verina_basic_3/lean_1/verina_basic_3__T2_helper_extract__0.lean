-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isDivisibleBy11_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def isDivisibleBy11__rp_helper_c39b37ae (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  n % 11 == 0
-- !benchmark @end code_aux


def isDivisibleBy11 (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  -- !benchmark @start code
  isDivisibleBy11__rp_helper_c39b37ae n h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isDivisibleBy11_postcond (n : Int) (result: Bool) (h_precond : isDivisibleBy11_precond (n)) :=
  -- !benchmark @start postcond
  (result → (∃ k : Int, n = 11 * k)) ∧ (¬ result → (∀ k : Int, ¬ n = 11 * k))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isDivisibleBy11_spec_satisfied (n: Int) (h_precond : isDivisibleBy11_precond (n)) :
    isDivisibleBy11_postcond (n) (isDivisibleBy11 (n) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : (isDivisibleBy11 n h_precond → (∃ k : Int, n = 11 * k)) ∧ (¬ isDivisibleBy11 n h_precond → ∀ k : Int, ¬ n = 11 * k) := by
    constructor
    · -- Prove that if isDivisibleBy11 n h_precond, then ∃ k : Int, n = 11 * k
      intro h
      have h₁ : n % 11 = 0 := by
        -- Convert the condition to use the definition of isDivisibleBy11
        simpa [isDivisibleBy11, isDivisibleBy11_precond] using h
      -- Use the fact that n % 11 = 0 to find k such that n = 11 * k
      use n / 11
      have h₂ : n % 11 = 0 := h₁
      have h₃ : n = 11 * (n / 11) := by
        have h₄ := Int.emod_add_ediv n 11
        omega
      linarith
    · -- Prove that if ¬ isDivisibleBy11 n h_precond, then ∀ k : Int, ¬ n = 11 * k
      intro h
      intro k
      have h₁ : n % 11 ≠ 0 := by
        by_contra h₂
        have h₃ : n % 11 = 0 := by omega
        have h₄ : isDivisibleBy11 n h_precond := by
          simp [isDivisibleBy11, isDivisibleBy11_precond, h₃]
          <;> omega
        contradiction
      -- Use the fact that n % 11 ≠ 0 to show that n ≠ 11 * k for any integer k
      intro h₂
      have h₃ : n % 11 = 0 := by
        have h₄ := congr_arg (· % 11) h₂
        simp at h₄
        <;> simp [Int.mul_emod, Int.add_emod, Int.sub_emod, Int.emod_emod] at h₄ ⊢
        <;> omega
      contradiction
  exact h_main
  -- !benchmark @end proof
