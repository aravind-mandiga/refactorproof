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
  have h_main : isDivisibleBy11_postcond (n) (isDivisibleBy11 (n) h_precond) h_precond := by
    have h₁ : (isDivisibleBy11 (n) h_precond) → (∃ k : Int, n = 11 * k) := by
      intro h
      have h₂ : n % 11 = 0 := by simpa [isDivisibleBy11] using h
      -- We need to find an integer k such that n = 11 * k
      use n / 11
      have h₃ : n % 11 = 0 := h₂
      have h₄ : n = 11 * (n / 11) + (n % 11) := by
        omega
      rw [h₃] at h₄
      linarith
    have h₂ : (¬ isDivisibleBy11 (n) h_precond) → (∀ k : Int, ¬ n = 11 * k) := by
      intro h
      intro k hk
      have h₃ : n % 11 = 0 := by
        -- We need to show that n % 11 = 0
        have h₄ : n = 11 * k := hk
        have h₅ : n % 11 = 0 := by
          rw [h₄]
          simp [Int.mul_emod, Int.emod_emod]
          <;> norm_num
        exact h₅
      have h₄ : ¬ isDivisibleBy11 (n) h_precond := h
      have h₅ : isDivisibleBy11 (n) h_precond ↔ n % 11 = 0 := by
        simp [isDivisibleBy11]
        <;> tauto
      simp_all
    exact ⟨h₁, h₂⟩
  exact h_main
  -- !benchmark @end proof
