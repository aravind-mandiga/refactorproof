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
    · -- Prove the first part: if isDivisibleBy11 (n) h_precond, then ∃ k : Int, n = 11 * k
      intro h
      have h₁ : n % 11 = 0 := by
        simp [isDivisibleBy11] at h
        <;> norm_cast at h ⊢ <;> simp_all [Int.emod_eq_zero_of_dvd]
        <;> omega
      -- Use the fact that n % 11 = 0 to find k such that n = 11 * k
      have h₂ : ∃ k : Int, n = 11 * k := by
        use n / 11
        have h₃ : n = 11 * (n / 11) + (n % 11) := by
          have h₄ := Int.emod_add_ediv n 11
          linarith
        rw [h₁] at h₃
        linarith
      exact h₂
    · -- Prove the second part: if ¬ isDivisibleBy11 (n) h_precond, then ∀ k : Int, ¬ n = 11 * k
      intro h
      have h₁ : n % 11 ≠ 0 := by
        simp [isDivisibleBy11] at h
        <;> norm_cast at h ⊢ <;> simp_all [Int.emod_eq_zero_of_dvd]
        <;> omega
      -- Use the fact that n % 11 ≠ 0 to show that n cannot be written as 11 * k
      intro k hk
      have h₂ : n % 11 = 0 := by
        have h₃ : n = 11 * k := hk
        have h₄ : n % 11 = (11 * k) % 11 := by rw [h₃]
        have h₅ : (11 * k : Int) % 11 = 0 := by
          simp [Int.mul_emod, Int.emod_emod]
        rw [h₄, h₅]
      contradiction
  -- Combine the results to prove the postcondition
  simp only [isDivisibleBy11_postcond] at *
  tauto
  -- !benchmark @end proof
