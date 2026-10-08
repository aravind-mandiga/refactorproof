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
  let __rp_tmp_d53b48dc : Int :=
    x * 3
  __rp_tmp_d53b48dc
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
  have h_result : Triple (x) h_precond = x * 3 := by
    simp [Triple]
    <;> ring
    <;> simp_all

  have h_div : (x * 3 : Int) / 3 = x := by
    have h₁ : (x * 3 : Int) = 3 * x := by ring
    rw [h₁]
    -- Use the property of integer division to simplify (3 * x) / 3 to x
    have h₂ : (3 : Int) ≠ 0 := by norm_num
    have h₃ : (3 * x : Int) / 3 = x := by
      apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : Int) ≠ 0)
      <;> ring
      <;> simp_all
    rw [h₃]
    <;> simp_all

  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    have h₁ : (Triple (x) h_precond : Int) = x * 3 := by
      rw [h_result]
    have h₂ : (Triple (x) h_precond : Int) / 3 = x := by
      rw [h₁]
      -- Use the previously proven fact that (x * 3) / 3 = x
      have h₃ : (x * 3 : Int) / 3 = x := h_div
      exact h₃
    have h₃ : (Triple (x) h_precond : Int) / 3 * 3 = (Triple (x) h_precond : Int) := by
      rw [h₁]
      -- Use the previously proven fact that (x * 3) / 3 = x to simplify the expression
      have h₄ : (x * 3 : Int) / 3 = x := h_div
      have h₅ : ((x * 3 : Int) / 3) * 3 = x * 3 := by
        rw [h₄]
        <;> ring
      -- Simplify the expression using the above facts
      linarith
    -- Combine the results to satisfy the postcondition
    constructor <;>
    (try simp_all [Triple_postcond]) <;>
    (try omega) <;>
    (try ring_nf at *) <;>
    (try simp_all) <;>
    (try linarith)
    <;>
    (try
      {
        norm_num at *
        <;>
        (try omega)
      })
    <;>
    (try
      {
        ring_nf at *
        <;>
        (try omega)
      })
    <;>
    (try
      {
        simp_all [Triple_postcond]
        <;>
        (try omega)
      })

  exact h_main
  -- !benchmark @end proof
