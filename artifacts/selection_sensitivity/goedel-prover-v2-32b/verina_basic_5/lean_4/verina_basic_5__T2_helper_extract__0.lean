-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def multiply_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def multiply__rp_helper_3cc08e31 (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  a * b
-- !benchmark @end code_aux


def multiply (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  -- !benchmark @start code
  multiply__rp_helper_3cc08e31 a b h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def multiply_postcond (a : Int) (b : Int) (result: Int) (h_precond : multiply_precond (a) (b)) :=
  -- !benchmark @start postcond
  result - a * b = 0 ∧ a * b - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem multiply_spec_satisfied (a: Int) (b: Int) (h_precond : multiply_precond (a) (b)) :
    multiply_postcond (a) (b) (multiply (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : multiply_postcond (a) (b) (multiply (a) (b) h_precond) h_precond := by
    simp [multiply_precond, multiply, multiply_postcond]
    <;>
    (try decide) <;>
    (try ring_nf) <;>
    (try norm_num) <;>
    (try
      {
        constructor <;>
        simp_all [Int.mul_emod] <;>
        ring_nf at * <;>
        norm_num at * <;>
        linarith
      })
    <;>
    (try
      {
        constructor <;>
        simp_all [Int.mul_emod] <;>
        ring_nf at * <;>
        norm_num at * <;>
        linarith
      })
  exact h_main
  -- !benchmark @end proof
