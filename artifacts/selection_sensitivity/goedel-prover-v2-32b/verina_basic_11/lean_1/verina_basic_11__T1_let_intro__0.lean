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
  have h_result : lastDigit (n) h_precond = n % 10 := by
    simp [lastDigit]
    <;>
    trivial

  have h_zero_le_result : 0 ≤ lastDigit (n) h_precond := by
    have h₁ : 0 ≤ lastDigit (n) h_precond := by
      -- Since lastDigit (n) h_precond is a natural number, it is always non-negative.
      exact Nat.zero_le _
    exact h₁

  have h_result_lt_ten : lastDigit (n) h_precond < 10 := by
    rw [h_result]
    have h₁ : n % 10 < 10 := by
      apply Nat.mod_lt
      <;> norm_num
    exact h₁

  have h_mod_sub_result : n % 10 - lastDigit (n) h_precond = 0 := by
    rw [h_result]
    <;> simp [Nat.sub_self]
    <;>
    (try decide)
    <;>
    (try omega)

  have h_result_sub_mod : lastDigit (n) h_precond - n % 10 = 0 := by
    rw [h_result]
    <;> simp [Nat.sub_self]
    <;>
    (try decide)
    <;>
    (try omega)

  simp_all [lastDigit_postcond, lastDigit_precond]
  <;>
  (try omega)
  <;>
  (try decide)
  <;>
  (try
    {
      constructor <;>
      (try omega) <;>
      (try decide)
    })
  -- !benchmark @end proof
