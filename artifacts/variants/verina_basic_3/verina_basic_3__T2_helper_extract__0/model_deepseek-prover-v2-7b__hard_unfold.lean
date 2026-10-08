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
  unfold isDivisibleBy11 isDivisibleBy11_postcond
  have h_main : ((isDivisibleBy11 (n) h_precond) → (∃ k : Int, n = 11 * k)) ∧ (¬ (isDivisibleBy11 (n) h_precond) → (∀ k : Int, ¬ (n = 11 * k))) := by
    constructor
    · -- Prove the first part: if result is true, then n is divisible by 11
      intro h
      have h₁ : n % 11 = 0 := by
        simp [isDivisibleBy11, h_precond] at h ⊢
        <;> simp_all (config := {decide := true})
        <;> aesop
      -- Use the fact that n % 11 = 0 to find k such that n = 11 * k
      use n / 11
      have h₂ := Int.emod_add_ediv n 11
      have h₃ := Int.emod_add_ediv n 11
      simp [h₁] at h₂ h₃ ⊢
      <;> ring_nf at h₂ h₃ ⊢ <;> omega
    · -- Prove the second part: if result is false, then n is not divisible by 11
      intro h
      intro k hk
      have h₁ : n % 11 ≠ 0 := by
        simp [isDivisibleBy11, h_precond] at h ⊢
        <;> simp_all (config := {decide := true})
        <;> aesop
      have h₂ : n % 11 = 0 := by
        have h₃ : n = 11 * k := by omega
        rw [h₃]
        simp [Int.mul_emod, h₁]
      exact h₁ h₂
  exact h_main
  -- !benchmark @end proof
