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
  have h_main : isDivisibleBy11_postcond (n) (isDivisibleBy11 (n) h_precond) h_precond := by
    constructor
    · -- First, prove that if `isDivisibleBy11 n h_precond` is true, then `n = 11 * k` for some `k`.
      intro h
      have h₁ : n % 11 = 0 := by
        simp [isDivisibleBy11, h_precond] at h ⊢
        <;> aesop
      -- We know that `n % 11 = 0`, so `n = 11 * (n / 11)`.
      have h₂ : ∃ k : ℤ, n = 11 * k := by
        use n / 11
        have h₃ : n % 11 = 0 := h₁
        have h₄ : n = 11 * (n / 11) := by
          omega
        linarith
      exact h₂
    · -- Next, prove that if `isDivisibleBy11 n h_precond` is false, then `n ≠ 11 * k` for any `k`.
      intro h
      have h₁ : n % 11 ≠ 0 := by
        simp [isDivisibleBy11, h_precond] at h ⊢
        <;> aesop
      intro k h₂
      have h₃ : n % 11 = 0 := by
        have h₄ : n = 11 * k := by omega
        have h₅ : n % 11 = 0 := by
          rw [h₄]
          simp [Int.mul_emod, Int.emod_emod]
        exact h₅
      contradiction
  exact h_main
  -- !benchmark @end proof
