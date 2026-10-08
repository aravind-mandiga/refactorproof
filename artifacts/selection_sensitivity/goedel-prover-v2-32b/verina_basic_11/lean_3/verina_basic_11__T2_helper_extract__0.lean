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
    simp [lastDigit]
    <;>
    simp_all [lastDigit_precond]
    <;>
    aesop

  have h₂ : (0 ≤ lastDigit (n) h_precond ∧ lastDigit (n) h_precond < 10) := by
    have h₃ : lastDigit (n) h_precond = n % 10 := h₁
    have h₄ : 0 ≤ lastDigit (n) h_precond := by
      -- Prove that 0 ≤ lastDigit(n)
      have h₅ : 0 ≤ n % 10 := by
        -- Since n % 10 is a natural number, it is always ≥ 0
        exact Nat.zero_le (n % 10)
      -- Use the fact that lastDigit(n) = n % 10
      rw [h₃]
      exact h₅
    have h₅ : lastDigit (n) h_precond < 10 := by
      -- Prove that lastDigit(n) < 10
      have h₆ : n % 10 < 10 := by
        -- Since n % 10 is the remainder when n is divided by 10, it must be < 10
        have h₇ : n % 10 < 10 := Nat.mod_lt n (by decide)
        exact h₇
      -- Use the fact that lastDigit(n) = n % 10
      rw [h₃]
      exact h₆
    -- Combine the two results
    exact ⟨h₄, h₅⟩

  have h₃ : (n % 10 - lastDigit (n) h_precond = 0 ∧ lastDigit (n) h_precond - n % 10 = 0) := by
    have h₄ : lastDigit (n) h_precond = n % 10 := h₁
    constructor
    · -- Prove that n % 10 - lastDigit(n) = 0
      rw [h₄]
      <;> simp [Nat.sub_self]
    · -- Prove that lastDigit(n) - n % 10 = 0
      rw [h₄]
      <;> simp [Nat.sub_self]

  have h₄ : lastDigit_postcond (n) (lastDigit (n) h_precond) h_precond := by
    have h₅ : (0 ≤ lastDigit (n) h_precond ∧ lastDigit (n) h_precond < 10) := h₂
    have h₆ : (n % 10 - lastDigit (n) h_precond = 0 ∧ lastDigit (n) h_precond - n % 10 = 0) := h₃
    simp_all [lastDigit_postcond, lastDigit_precond]
    <;>
    (try omega) <;>
    (try simp_all) <;>
    (try norm_num) <;>
    (try aesop)
    <;>
    (try
      {
        cases n <;> simp_all [Nat.mod_eq_of_lt]
        <;> norm_num <;> omega
      })

  apply h₄
  -- !benchmark @end proof
