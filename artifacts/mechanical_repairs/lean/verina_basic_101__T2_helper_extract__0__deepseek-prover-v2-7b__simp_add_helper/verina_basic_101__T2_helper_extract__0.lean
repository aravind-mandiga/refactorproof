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
  have h₁ : (Triple (x) h_precond) / 3 = x := by
    have h₁ : Triple (x) h_precond = 3 * x := by
      -- Simplify the expression for Triple x using the given definition
      simp [Triple, Triple_precond, Triple__rp_helper_65b561a3]
      <;> ring
      <;> omega
    rw [h₁]
    -- Use the property of integer division to prove the result
    have h₂ : (3 * x : ℤ) / 3 = x := by
      have h₃ : (3 : ℤ) ∣ 3 * x := by
        use x
        <;> ring
      -- Use the property of divisibility to simplify the division
      omega
    exact h₂

  have h₂ : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    have h₂ : Triple (x) h_precond = 3 * x := by
      have h₂ : Triple (x) h_precond = 3 * x := by
        -- Simplify the expression for Triple x using the given definition
        simp [Triple, Triple_precond]
        <;> ring
        <;> omega
      exact h₂
    rw [h₂]
    have h₃ : ((3 * x : ℤ) / 3) * 3 = 3 * x := by
      have h₄ : (3 * x : ℤ) / 3 = x := by
        have h₅ : (3 : ℤ) ∣ 3 * x := by
          use x
          <;> ring
        -- Use the property of divisibility to simplify the division
        omega
      rw [h₄]
      <;> ring
    exact h₃

  simp_all [Triple_postcond, Triple, Triple_precond]
  <;>
  (try omega) <;>
  (try ring_nf at * <;> norm_num at * <;> linarith) <;>
  (try nlinarith) <;>
  (try
    {
      cases Int.emod_two_eq_zero_or_one x <;>
      cases Int.emod_two_eq_zero_or_one (x + 1) <;>
      simp_all [Int.emod_eq_of_lt] <;>
      omega
    })
  -- !benchmark @end proof
