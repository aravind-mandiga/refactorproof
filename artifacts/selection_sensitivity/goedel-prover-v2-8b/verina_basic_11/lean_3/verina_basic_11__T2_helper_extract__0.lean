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
  have h₁ : lastDigit (n) h_precond = n % 10 := by
    rfl

  have h₂ : 0 ≤ n % 10 := by
    exact Nat.zero_le _

  have h₃ : n % 10 < 10 := by
    have h₃ : n % 10 < 10 := Nat.mod_lt n (by norm_num)
    exact h₃

  have h₄ : n % 10 - (n % 10) = 0 := by
    have h₄ : n % 10 - (n % 10) = 0 := by
      simp [Nat.sub_self]
    exact h₄

  have h₅ : (n % 10) - n % 10 = 0 := by
    have h₅ : (n % 10) - n % 10 = 0 := by
      simp [Nat.sub_self]
    exact h₅

  have h₆ : (0 ≤ (n % 10) ∧ (n % 10) < 10) ∧ (n % 10 - (n % 10) = 0 ∧ (n % 10) - n % 10 = 0) := by
    refine' ⟨⟨h₂, h₃⟩, _⟩
    exact ⟨h₄, h₅⟩

  have h₇ : lastDigit_postcond n (lastDigit n h_precond) h_precond := by
    rw [h₁]
    exact h₆

  exact h₇
  -- !benchmark @end proof
