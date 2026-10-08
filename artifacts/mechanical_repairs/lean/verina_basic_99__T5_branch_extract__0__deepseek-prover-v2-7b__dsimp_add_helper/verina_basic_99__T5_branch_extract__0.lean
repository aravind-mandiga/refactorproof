-- !benchmark @start import type=solution
import Mathlib
import Aesop
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

private def Triple__rp_branch_609232c2 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  let y := 2 * x
  x + y
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  if x < 18 then
    let a := 2 * x
    let b := 4 * x
    (a + b) / 2
  else
    Triple__rp_branch_609232c2 x h_precond
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
  have h_main : (Triple (x) h_precond) / 3 = x ∧ (Triple (x) h_precond) / 3 * 3 = (Triple (x) h_precond) := by
    have h₁ : Triple (x) h_precond = 3 * x := by
      -- We need to compute the value of Triple(x) based on the condition x < 18
      dsimp [Triple, Triple__rp_branch_609232c2]
      split_ifs with h
      · -- Case x < 18
        simp [mul_comm]
        <;> ring_nf at *
        <;> omega
      · -- Case x ≥ 18
        simp [mul_comm]
        <;> ring_nf at *
        <;> omega
    rw [h₁]
    constructor
    · -- Prove that (3 * x) / 3 = x
      have h₂ : (3 * x) / 3 = x := by
        have h₃ : x ≤ x := by linarith
        have h₄ : x ≥ x := by linarith
        -- Use the fact that 3 * x is divisible by 3
        omega
      linarith
    · -- Prove that (3 * x) / 3 * 3 = 3 * x
      have h₂ : ((3 * x) / 3 * 3) = 3 * x := by
        have h₃ : x ≤ x := by linarith
        have h₄ : x ≥ x := by linarith
        -- Use the fact that 3 * x is divisible by 3
        omega
      linarith
  exact h_main
  -- !benchmark @end proof
