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

private def lastDigit__rp_helper_8d571788 (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  n % 10
-- !benchmark @end code_aux


def lastDigit (n : Nat) (h_precond : lastDigit_precond (n)) : Nat :=
  -- !benchmark @start code
  lastDigit__rp_helper_8d571788 n h_precond
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
  have h₁ : 0 ≤ n % 10 := by
    have h₁ : 0 ≤ n % 10 := by
      -- Prove that the last digit is a non-negative integer.
      exact Nat.zero_le (n % 10)
    exact h₁

  have h₂ : n % 10 < 10 := by
    have h₂ : n % 10 < 10 := by
      -- Use the property of the modulo operation to show that n % 10 is less than 10.
      have h₂₁ : n % 10 < 10 := Nat.mod_lt n (by norm_num)
      exact h₂₁
    exact h₂

  have h₃ : n % 10 - (n % 10) = 0 := by
    have h₃ : n % 10 - (n % 10) = 0 := by
      -- Prove that n % 10 - (n % 10) = 0 using the property of subtraction in natural numbers.
      have h₃₁ : n % 10 - (n % 10) = 0 := by
        -- Use the fact that any number minus itself is zero.
        simp [Nat.sub_self]
      exact h₃₁
    exact h₃

  have h₄ : (n % 10) - (n % 10) = 0 := by
    have h₄ : (n % 10) - (n % 10) = 0 := by
      -- Use the property of subtraction where any natural number subtracted from itself equals zero.
      have h₄₁ : (n % 10) - (n % 10) = 0 := by
        -- Apply the `Nat.sub_self` lemma to show that `n % 10 - (n % 10) = 0`.
        apply Nat.sub_self
      exact h₄₁
    exact h₄

  have h₅ : (0 ≤ (lastDigit (n) h_precond) ∧ (lastDigit (n) h_precond) < 10) ∧ (n % 10 - (lastDigit (n) h_precond) = 0 ∧ (lastDigit (n) h_precond) - n % 10 = 0) := by
    have h₅₁ : lastDigit (n) h_precond = n % 10 := by
      -- Prove that lastDigit (n) h_precond = n % 10
      rfl
    rw [h₅₁]
    constructor
    · -- Prove the first part: 0 ≤ (n % 10) ∧ (n % 10) < 10
      constructor
      · -- Prove 0 ≤ (n % 10)
        exact h₁
      · -- Prove (n % 10) < 10
        exact h₂
    · -- Prove the second part: (n % 10) - (n % 10) = 0 ∧ (n % 10) - (n % 10) = 0
      constructor
      · -- Prove (n % 10) - (n % 10) = 0
        exact h₃
      · -- Prove (n % 10) - (n % 10) = 0
        exact h₄

  exact h₅
  -- !benchmark @end proof
