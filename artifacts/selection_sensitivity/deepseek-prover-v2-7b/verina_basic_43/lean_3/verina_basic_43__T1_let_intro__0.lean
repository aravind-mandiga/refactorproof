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
  have h_main : 15 * sumOfFourthPowerOfOddNumbers n h_precond = n * (2 * n + 1) * (7 + 24 * n ^ 3 - 12 * n ^ 2 - 14 * n) := by
    have h₁ : ∀ n : Nat, 15 * sumOfFourthPowerOfOddNumbers n h_precond = n * (2 * n + 1) * (7 + 24 * n ^ 3 - 12 * n ^ 2 - 14 * n) := by
      intro n
      induction n with
      | zero =>
        norm_num [sumOfFourthPowerOfOddNumbers, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.mul_add, Nat.add_mul]
      | succ n ih =>
        simp_all [sumOfFourthPowerOfOddNumbers, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        <;>
        (try ring_nf at * <;> omega) <;>
        (try
          {
            cases n with
            | zero => norm_num
            | succ n =>
              simp_all [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              <;> ring_nf at * <;> omega
          }
        ) <;>
        (try omega) <;>
        (try linarith) <;>
        (try
          {
            cases n with
            | zero => norm_num
            | succ n =>
              simp_all [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
              <;> ring_nf at * <;> omega
          }
        )
    simpa using h₁ n
  simpa [sumOfFourthPowerOfOddNumbers_postcond] using h_main
  -- !benchmark @end proof
