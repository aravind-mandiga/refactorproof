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
  have h_main : isDivisibleBy11_postcond n (isDivisibleBy11 n h_precond) h_precond := by
    unfold isDivisibleBy11_postcond
    constructor
    · -- Prove the forward direction: if isDivisibleBy11 n h_precond, then ∃ k, n = 11 * k
      intro h
      have h₁ : n % 11 = 0 := by simpa [isDivisibleBy11, h_precond] using h
      -- Since n % 11 = 0, we can write n = 11 * k for some integer k
      have h₂ : ∃ k : Int, n = 11 * k := by
        use n / 11
        have h₃ : n % 11 = 0 := h₁
        have h₄ : n = 11 * (n / 11) := by
          have h₅ : n % 11 = 0 := h₁
          omega
        linarith
      exact h₂
    · -- Prove the backward direction: if ¬isDivisibleBy11 n h_precond, then ∀ k : Int, ¬n = 11 * k
      intro h
      have h₁ : ¬(n % 11 = 0) := by simpa [isDivisibleBy11, h_precond] using h
      intro k hk
      have h₂ : n % 11 = 0 := by
        have h₃ : n = 11 * k := by omega
        have h₄ : n % 11 = 0 := by
          rw [h₃]
          simp [Int.mul_emod, Int.emod_emod]
        exact h₄
      exact h₁ h₂
  exact h_main
  -- !benchmark @end proof
