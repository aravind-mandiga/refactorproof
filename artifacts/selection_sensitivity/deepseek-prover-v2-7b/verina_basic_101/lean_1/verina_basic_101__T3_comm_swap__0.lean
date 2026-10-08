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
  let y := 2 * x
  y + x
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
  have h_main1 : (Triple (x) h_precond) / 3 = x := by
    have h₁ : Triple (x) h_precond = 3 * x := by
      -- Simplify the expression for Triple(x)
      simp [Triple]
      <;> ring
      <;> simp_all [Triple_precond]
    rw [h₁]
    -- Use the property of integer division to show that (3 * x) / 3 = x
    have h₂ : (3 * x : ℤ) / 3 = x := by
      -- Prove that (3 * x) / 3 = x using the fact that 3 * x is divisible by 3
      omega
    exact h₂

  have h_main2 : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    have h₁ : Triple (x) h_precond = 3 * x := by
      -- Simplify the expression for Triple(x)
      simp [Triple]
      <;> ring
      <;> simp_all [Triple_precond]
    rw [h₁] at *
    -- Simplify the expression using the fact that x is an integer
    have h₂ : (3 * x : ℤ) / 3 * 3 = 3 * x := by
      -- Prove that (3 * x) / 3 * 3 = 3 * x
      have h₃ : (3 * x : ℤ) / 3 * 3 = 3 * x := by
        -- Use the property of integer division and multiplication
        have h₄ : (3 * x : ℤ) % 3 = 0 := by
          -- Prove that 3 * x is divisible by 3
          simp [Int.mul_emod]
        -- Use the fact that 3 * x is divisible by 3 to simplify the expression
        omega
      exact h₃
    exact h₂
  -- Combine the results to prove the theorem
  constructor
  exact h_main1
  exact h_main2
  -- !benchmark @end proof
