-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  3 * x
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  -- !benchmark @start postcond
  result / 3 = x ∧ result / 3 * 3 = result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Triple_spec_satisfied (x: Int) (h_precond : Triple_precond (x)) :
    Triple_postcond (x) (Triple (x) h_precond) h_precond := by
  -- !benchmark @start proof
  have h₁ : (Triple (x) h_precond) / 3 = x := by
    have h₂ : Triple (x) h_precond = x * 3 := by
      -- Expand the definition of `Triple`
      rfl
    rw [h₂]
    -- Simplify the expression using the properties of integer division
    <;>
    (try omega) <;>
    (try
      {
        -- Use the fact that `x * 3 / 3 = x` for integer division
        have h₃ : (x * 3) / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_right (by decide : (3 : ℤ) ≠ 0)
          <;> ring
        linarith
      }) <;>
    (try omega) <;>
    (try
      {
        -- Use the properties of integer division to prove the result
        have h₃ : (x * 3) / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_right (by decide : (3 : ℤ) ≠ 0)
          <;> ring
        linarith
      })
    <;>
    omega

  have h₂ : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    have h₃ : Triple (x) h_precond = x * 3 := by
      rfl
    rw [h₃] at *
    <;>
    (try omega) <;>
    (try
      {
        -- Use the properties of multiplication and division to simplify the expression.
        have h₄ : (x * 3) / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_right (by decide : (3 : ℤ) ≠ 0)
          <;> ring
        <;>
        (try omega) <;>
        (try linarith) <;>
        (try nlinarith) <;>
        simp_all [h₁] <;>
        omega
      }) <;>
    omega

  constructor
  · -- Prove the first part: result / 3 = x
    exact h₁
  · -- Prove the second part: (result / 3) * 3 = result
    exact h₂
  -- !benchmark @end proof
