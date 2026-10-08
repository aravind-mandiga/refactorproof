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
  have h_last_digit : lastDigit n h_precond = n % 10 := by
    rfl

  have h_zero_le : 0 ≤ n % 10 := by
    -- Since n % 10 is a natural number, it is always non-negative.
    exact Nat.zero_le _

  have h_lt_ten : n % 10 < 10 := by
    -- By the property of the modulus operation, n % 10 is always less than 10.
    have h : n % 10 < 10 := Nat.mod_lt n (by decide)
    exact h

  have h_sub_self : n % 10 - (n % 10) = 0 := by
    -- Any natural number minus itself is 0.
    have h₁ : n % 10 - (n % 10) = 0 := by
      simp [Nat.sub_self]
    exact h₁

  have h_main : lastDigit_postcond n (lastDigit n h_precond) h_precond := by
    have h₁ : lastDigit n h_precond = n % 10 := h_last_digit
    have h₂ : 0 ≤ n % 10 := h_zero_le
    have h₃ : n % 10 < 10 := h_lt_ten
    have h₄ : n % 10 - (n % 10) = 0 := h_sub_self
    have h₅ : (n % 10) - (n % 10) = 0 := by
      simp [Nat.sub_self]
    simp_all [lastDigit_postcond, lastDigit_precond]
    <;>
    (try omega) <;>
    (try simp_all) <;>
    (try ring_nf at *) <;>
    (try omega)
    <;>
    (try
      {
        cases n <;> simp_all [Nat.mod_eq_of_lt]
        <;> omega
      })

  exact h_main
  -- !benchmark @end proof
