-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def lastDigit_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def lastDigit (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  -- !benchmark @start code
  let __rp_tmp_c1b8a8ca : Nat :=
    n % 10
  __rp_tmp_c1b8a8ca
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def lastDigit_postcond (n : Nat) (result: Nat) (h_precond : lastDigit_precond (n)) :=
  -- !benchmark @start postcond
  (0 ≤ result ∧ result < 10) ∧
  (n % 10 - result = 0 ∧ result - n % 10 = 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem lastDigit_spec_satisfied (n: Nat) (h_precond : lastDigit_precond (n)) :
    lastDigit_postcond (n) (lastDigit (n) h_precond) h_precond := by
  -- !benchmark @start proof
  have h₁ : 0 ≤ n % 10 ∧ n % 10 < 10 := by
    have h₁₁ : 0 ≤ n % 10 := by
      -- Prove that 0 ≤ n % 10 using the fact that n % 10 is a natural number.
      exact Nat.zero_le _
    have h₁₂ : n % 10 < 10 := by
      -- Prove that n % 10 < 10 using the property of the modulus operation.
      exact Nat.mod_lt n (by norm_num)
    exact ⟨h₁₁, h₁₂⟩

  have h₂ : n % 10 - (n % 10) = 0 := by
    have h₂₁ : n % 10 ≤ n % 10 := by
      -- Prove that n % 10 ≤ n % 10 using the reflexive property of ≤.
      exact le_refl _
    -- Use the fact that n % 10 ≤ n % 10 to conclude that n % 10 - (n % 10) = 0.
    have h₂₂ : n % 10 - (n % 10) = 0 := by
      have h₂₃ : n % 10 - (n % 10) = 0 := by
        omega
      exact h₂₃
    exact h₂₂

  have h₃ : (n % 10) - (n % 10) = 0 := by
    have h₃₁ : (n % 10) ≤ (n % 10) := by
      -- Prove that n % 10 ≤ n % 10 using the reflexive property of ≤.
      exact le_refl _
    -- Use the fact that n % 10 ≤ n % 10 to conclude that (n % 10) - (n % 10) = 0.
    have h₃₂ : (n % 10) - (n % 10) = 0 := by
      omega
    exact h₃₂

  have h₄ : lastDigit_postcond (n) (lastDigit (n) h_precond) h_precond := by
    have h₄₁ : lastDigit (n) h_precond = n % 10 := rfl
    rw [h₄₁]
    constructor
    · -- Prove 0 ≤ n % 10 < 10
      constructor
      · -- Prove 0 ≤ n % 10
        exact Nat.zero_le _
      · -- Prove n % 10 < 10
        exact Nat.mod_lt n (by norm_num)
    · -- Prove n % 10 - (n % 10) = 0 and (n % 10) - (n % 10) = 0
      constructor
      · -- Prove n % 10 - (n % 10) = 0
        exact h₂
      · -- Prove (n % 10) - (n % 10) = 0
        exact h₃

  exact h₄
  -- !benchmark @end proof
