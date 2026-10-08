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

private def Triple__rp_helper_65b561a3 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  let y := x * 2
  y + x
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  Triple__rp_helper_65b561a3 x h_precond
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
  have h_triple : Triple (x) h_precond = 3 * x := by
    dsimp [Triple]
    <;> ring_nf
    <;> norm_num
    <;> linarith

  have h1 : (Triple (x) h_precond) / 3 = x := by
    rw [h_triple]
    have h₂ : (3 * x : ℤ) / 3 = x := by
      have h₃ : (3 * x : ℤ) / 3 = x := by
        apply Int.ediv_eq_of_eq_mul_right (show (3 : ℤ) ≠ 0 by norm_num)
        <;> ring_nf
        <;> omega
      exact h₃
    exact h₂

  have h2 : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    rw [h1]
    rw [h_triple]
    <;> ring_nf
    <;> omega

  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    constructor
    · -- Prove the first part: result / 3 = x
      exact h1
    · -- Prove the second part: (result / 3) * 3 = result
      exact h2

  exact h_main
  -- !benchmark @end proof
