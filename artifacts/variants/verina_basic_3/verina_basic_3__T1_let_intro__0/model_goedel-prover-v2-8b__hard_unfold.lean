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
  unfold isDivisibleBy11 isDivisibleBy11_postcond
  have h_main₁ : (isDivisibleBy11 (n) h_precond → (∃ k : Int, n = 11 * k)) := by
    intro h
    have h₁ : n % 11 = 0 := by simpa [isDivisibleBy11] using h
    have h₂ : n = 11 * (n / 11) := by
      have h₃ : n % 11 = 0 := h₁
      have h₄ : n = 11 * (n / 11) + (n % 11) := by
        rw [Int.emod_def]
        <;> ring_nf
        <;> omega
      rw [h₃] at h₄
      linarith
    exact ⟨n / 11, by linarith⟩

  have h_main₂ : (¬ isDivisibleBy11 (n) h_precond → (∀ k : Int, ¬ n = 11 * k)) := by
    intro h
    intro k hk
    have h₁ : n % 11 ≠ 0 := by
      intro h₂
      apply h
      simpa [isDivisibleBy11] using h₂
    have h₂ : n % 11 = 0 := by
      have h₃ : n = 11 * k := hk
      rw [h₃]
      simp [Int.mul_emod, Int.emod_emod]
    contradiction

  constructor
  · -- Prove the first part: (isDivisibleBy11 (n) h_precond → (∃ k : Int, n = 11 * k))
    exact h_main₁
  · -- Prove the second part: (¬ isDivisibleBy11 (n) h_precond → (∀ k : Int, ¬ n = 11 * k))
    exact h_main₂
  -- !benchmark @end proof
