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
  have h1 : (multiply (a) (b) h_precond) - a * b = 0 := by
    simp [multiply, multiply_precond, mul_comm]
    <;>
    ring
    <;>
    aesop

  have h2 : a * b - (multiply (a) (b) h_precond) = 0 := by
    simp [multiply, multiply_precond, mul_comm] at *
    <;>
    ring_nf at * <;>
    aesop

  constructor <;> simp_all [multiply_postcond]
  <;>
  aesop
  -- !benchmark @end proof
