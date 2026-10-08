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
  have h_result_def : lastDigit n h_precond = n % 10 := by
    rfl

  have h_bounds : 0 ≤ (n % 10 : ℕ) ∧ (n % 10 : ℕ) < 10 := by
    have h₁ : 0 ≤ (n % 10 : ℕ) := by
      -- Since `n % 10` is a natural number, it is trivially greater than or equal to 0.
      exact Nat.zero_le _
    have h₂ : (n % 10 : ℕ) < 10 := by
      -- The remainder of `n` when divided by 10 is always less than 10.
      have h₃ : n % 10 < 10 := Nat.mod_lt n (by norm_num)
      exact h₃
    exact ⟨h₁, h₂⟩

  have h_sub1 : (n % 10 : ℕ) - (n % 10 : ℕ) = 0 := by
    have h₁ : (n % 10 : ℕ) - (n % 10 : ℕ) = 0 := by
      -- Since any number minus itself is zero, this is straightforward.
      simp [Nat.sub_self]
    exact h₁

  have h_sub2 : (n % 10 : ℕ) - (n % 10 : ℕ) = 0 := by
    have h₁ : (n % 10 : ℕ) - (n % 10 : ℕ) = 0 := by
      -- Since any number minus itself is zero, this is straightforward.
      simp [Nat.sub_self]
    exact h₁

  have h_main : lastDigit_postcond n (lastDigit n h_precond) h_precond := by
    have h₁ : lastDigit n h_precond = n % 10 := h_result_def
    have h₂ : 0 ≤ (n % 10 : ℕ) ∧ (n % 10 : ℕ) < 10 := h_bounds
    have h₃ : (n % 10 : ℕ) - (n % 10 : ℕ) = 0 := h_sub1
    have h₄ : (n % 10 : ℕ) - (n % 10 : ℕ) = 0 := h_sub2
    simp only [h₁, lastDigit_postcond, lastDigit_precond] at *
    <;>
    (try norm_num at *) <;>
    (try simp_all) <;>
    (try omega) <;>
    (try ring_nf at *) <;>
    (try norm_num) <;>
    (try aesop)
    <;>
    (try
      {
        constructor <;>
        (try constructor) <;>
        (try simp_all) <;>
        (try omega) <;>
        (try ring_nf at *) <;>
        (try norm_num) <;>
        (try aesop)
      })
    <;>
    (try
      {
        simp_all [Nat.mod_lt]
        <;>
        omega
      })

  exact h_main
  -- !benchmark @end proof
