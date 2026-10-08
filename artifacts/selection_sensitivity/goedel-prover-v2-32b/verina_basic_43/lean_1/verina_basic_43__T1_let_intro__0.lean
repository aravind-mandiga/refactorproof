-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def sumOfFourthPowerOfOddNumbers_precond (n : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def sumOfFourthPowerOfOddNumbers (n : Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) : Nat :=
  -- !benchmark @start code
  let __rp_tmp_6abd56c6 : Nat :=
    match n with
    | 0 => 0
    | n + 1 =>
      let prev := sumOfFourthPowerOfOddNumbers n h_precond
      let nextOdd := 2 * n + 1
      prev + nextOdd^4
  __rp_tmp_6abd56c6
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def sumOfFourthPowerOfOddNumbers_postcond (n : Nat) (result: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :=
  -- !benchmark @start postcond
  15 * result = n * (2 * n + 1) * (7 + 24 * n^3 - 12 * n^2 - 14 * n)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem sumOfFourthPowerOfOddNumbers_spec_satisfied (n: Nat) (h_precond : sumOfFourthPowerOfOddNumbers_precond (n)) :
    sumOfFourthPowerOfOddNumbers_postcond (n) (sumOfFourthPowerOfOddNumbers (n) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : ∀ (n : ℕ), 15 * sumOfFourthPowerOfOddNumbers n (by trivial) = n * (2 * n + 1) * (7 + 24 * n ^ 3 - 12 * n ^ 2 - 14 * n) := by
    intro n
    have h : ∀ (n : ℕ), 15 * sumOfFourthPowerOfOddNumbers n (by trivial) = n * (2 * n + 1) * (7 + 24 * n ^ 3 - 12 * n ^ 2 - 14 * n) := by
      intro n
      induction n with
      | zero =>
        simp [sumOfFourthPowerOfOddNumbers]
      | succ n ih =>
        simp_all [sumOfFourthPowerOfOddNumbers, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib,
          Nat.mul_add, Nat.add_mul, Nat.pow_succ, Nat.mul_assoc]
        <;>
          (try ring_nf at * <;>
            try
              {
                cases n with
                | zero => norm_num
                | succ n =>
                  simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.mul_add, Nat.add_mul,
                    Nat.pow_succ, Nat.mul_assoc] at *
                  <;> ring_nf at * <;>
                    norm_num at * <;>
                    (try omega) <;>
                    (try
                      {
                        nlinarith
                      })
              }) <;>
          (try
            {
              ring_nf at *
              <;>
                norm_num at *
              <;>
                (try omega)
              <;>
                (try nlinarith)
            }) <;>
          (try
            {
              simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.mul_add, Nat.add_mul,
                Nat.pow_succ, Nat.mul_assoc] at *
              <;> ring_nf at * <;>
                norm_num at * <;>
                (try omega) <;>
                (try nlinarith)
            })
        <;>
          (try
            {
              simp_all [sumOfFourthPowerOfOddNumbers, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib,
                Nat.mul_add, Nat.add_mul, Nat.pow_succ, Nat.mul_assoc]
              <;> ring_nf at * <;>
                norm_num at * <;>
                (try omega) <;>
                (try nlinarith)
            })
    exact h n
  have h₁ : 15 * sumOfFourthPowerOfOddNumbers n h_precond = n * (2 * n + 1) * (7 + 24 * n ^ 3 - 12 * n ^ 2 - 14 * n) := by
    have h₂ := h_main n
    simpa [h_precond] using h₂
  simpa [sumOfFourthPowerOfOddNumbers_postcond, h_precond] using h₁
  -- !benchmark @end proof
