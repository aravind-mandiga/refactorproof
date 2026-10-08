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

private def Triple__rp_helper_c4a61f58 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  x * 3
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  Triple__rp_helper_c4a61f58 x h_precond
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
  have h_main₁ : (Triple (x) h_precond) / 3 = x := by
    have h : Triple (x) h_precond = x * 3 := rfl
    rw [h]
    <;>
    (try simp [Int.mul_ediv_cancel_left]) <;>
    (try omega) <;>
    (try ring_nf) <;>
    (try omega) <;>
    (try norm_num) <;>
    (try simp_all [Triple_precond]) <;>
    (try omega)
    <;>
    (try
      {
        -- Use the property that (x * 3) / 3 = x to prove this
        have h₀ : (x * 3) / 3 = x := by
          -- Use the property that (x * 3) / 3 = x
          omega
        omega
      })
    <;>
    (try omega)
    <;>
    (try
      {
        -- Use the property that (x * 3) / 3 = x to prove this
        have h₀ : (x * 3) / 3 = x := by
          -- Use the property that (x * 3) / 3 = x
          omega
        omega
      })
    <;>
    (try omega)

  have h_main₂ : (Triple (x) h_precond) / 3 * 3 = (Triple (x) h_precond) := by
    have h : Triple (x) h_precond = x * 3 := rfl
    rw [h]
    <;>
    (try ring_nf) <;>
    (try simp [Int.mul_ediv_cancel_left]) <;>
    (try omega) <;>
    (try nlinarith) <;>
    (try norm_num) <;>
    (try omega)
    <;>
    (try
      {
        have h₀ : ((x * 3 : ℤ) / 3) * 3 = x * 3 := by
          -- Use the property that (x * 3) / 3 * 3 = x * 3
          omega
        omega
      })
    <;>
    (try omega)
    <;>
    (try
      {
        have h₀ : ((x * 3 : ℤ) / 3) * 3 = x * 3 := by
          -- Use the property that (x * 3) / 3 * 3 = x * 3
          omega
        omega
      })
    <;>
    (try omega)

  constructor
  · -- Prove the first goal: result / 3 = x
    exact h_main₁
  · -- Prove the second goal: result / 3 * 3 = result
    exact h_main₂
  -- !benchmark @end proof
