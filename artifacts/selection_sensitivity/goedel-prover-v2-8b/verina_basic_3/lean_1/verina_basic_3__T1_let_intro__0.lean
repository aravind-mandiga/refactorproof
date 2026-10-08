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

-- !benchmark @end code_aux


def isDivisibleBy11 (n : Int) (h_precond : isDivisibleBy11_precond (n)) : Bool :=
  -- !benchmark @start code
  let __rp_tmp_24877dad : Bool :=
    n % 11 == 0
  __rp_tmp_24877dad
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
  have h_main : (isDivisibleBy11 (n) h_precond → (∃ k : Int, n = 11 * k)) ∧ (¬ isDivisibleBy11 (n) h_precond → (∀ k : Int, ¬ n = 11 * k)) := by
    constructor
    · -- Prove the first condition: if isDivisibleBy11 (n) h_precond is true, then there exists k such that n = 11 * k
      intro h
      -- Since isDivisibleBy11 (n) h_precond is true, n % 11 = 0
      have h₁ : n % 11 = 0 := by simpa [isDivisibleBy11] using h
      -- Use the integer division to find k
      use n / 11
      have h₂ : n = 11 * (n / 11) := by
        have h₃ := Int.emod_add_ediv n 11
        omega
      linarith
    · -- Prove the second condition: if ¬ isDivisibleBy11 (n) h_precond, then for all k, ¬ n = 11 * k
      intro h
      intro k hk
      -- If n = 11 * k, then n % 11 = 0, which contradicts ¬ isDivisibleBy11 (n) h_precond
      have h₁ : n % 11 = 0 := by
        have h₂ := hk
        simp [Int.mul_emod, Int.emod_emod] at h₂ ⊢
        <;> omega
      have h₂ : isDivisibleBy11 (n) h_precond := by
        simp [isDivisibleBy11]
        <;> omega
      exact h h₂
  exact h_main
  -- !benchmark @end proof
