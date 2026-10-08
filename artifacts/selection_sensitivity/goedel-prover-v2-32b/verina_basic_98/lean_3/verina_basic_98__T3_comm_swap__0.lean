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
  have h_main : (x * 3 : ℤ) / 3 = x := by
    have h₁ : (x * 3 : ℤ) / 3 = x := by
      have h₂ : (x * 3 : ℤ) = 3 * x := by ring
      rw [h₂]
      -- Use the property of integer division to simplify (3 * x) / 3
      have h₃ : (3 * x : ℤ) / 3 = x := by
        -- Prove that (3 * x) / 3 = x using the fact that 3 * x is a multiple of 3
        have h₄ : (3 * x : ℤ) / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
          <;> ring_nf
          <;> norm_num
          <;> linarith
        exact h₄
      exact h₃
    exact h₁

  have h1 : (Triple (x) h_precond) / 3 = x := by
    have h2 : Triple (x) h_precond = x * 3 := by
      simp [Triple]
      <;> ring_nf
    rw [h2]
    -- Now we need to show that (x * 3) / 3 = x
    -- This is already proven in h_main
    have h3 : (x * 3 : ℤ) / 3 = x := h_main
    exact_mod_cast h3

  have h2 : (Triple (x) h_precond) / 3 * 3 = Triple (x) h_precond := by
    have h3 : (Triple (x) h_precond) / 3 = x := h1
    have h4 : Triple (x) h_precond = x * 3 := by
      simp [Triple]
      <;> ring_nf
    rw [h3]
    -- Now we need to show that x * 3 = Triple (x) h_precond
    -- This follows from the definition of Triple
    have h5 : Triple (x) h_precond = x * 3 := by
      simp [Triple]
      <;> ring_nf
    linarith

  have h_final : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    constructor
    · -- Prove the first part of the conjunction: (Triple (x) h_precond) / 3 = x
      exact h1
    · -- Prove the second part of the conjunction: (Triple (x) h_precond) / 3 * 3 = Triple (x) h_precond
      exact h2

  exact h_final
  -- !benchmark @end proof
