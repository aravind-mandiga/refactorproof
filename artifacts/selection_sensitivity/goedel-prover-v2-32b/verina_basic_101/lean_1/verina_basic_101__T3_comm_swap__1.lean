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
  let y := x * 2
  x + y
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
  have h_result : Triple (x) h_precond = 3 * x := by
    dsimp [Triple]
    <;> ring_nf
    <;> simp_all [Triple_precond]
    <;> linarith

  have h_div : (Triple (x) h_precond) / 3 = x := by
    have h₁ : (Triple (x) h_precond) = 3 * x := h_result
    rw [h₁]
    have h₂ : (3 : ℤ) ≠ 0 := by norm_num
    have h₃ : (3 * x : ℤ) / 3 = x := by
      -- Use the property of integer division to simplify (3 * x) / 3 to x
      have h₄ : (3 * x : ℤ) / 3 = x := by
        apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
        <;> ring_nf
        <;> norm_num
      exact h₄
    exact h₃

  have h_mul : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    have h₁ : (Triple (x) h_precond) = 3 * x := h_result
    have h₂ : (Triple (x) h_precond) / 3 = x := h_div
    calc
      ((Triple (x) h_precond) / 3) * 3 = x * 3 := by rw [h₂]
      _ = 3 * x := by ring
      _ = Triple (x) h_precond := by
        rw [h₁]
        <;> ring

  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    dsimp [Triple_postcond]
    constructor
    · -- Prove the first condition: result / 3 = x
      exact h_div
    · -- Prove the second condition: result / 3 * 3 = result
      have h₁ : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := h_mul
      -- Use the previously proven statement to directly conclude the second condition
      linarith

  exact h_main
  -- !benchmark @end proof
