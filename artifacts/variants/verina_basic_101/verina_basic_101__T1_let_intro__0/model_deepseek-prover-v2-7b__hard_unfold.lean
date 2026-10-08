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
  let __rp_tmp_1171a237 : Int :=
    let y := x * 2
    y + x
  __rp_tmp_1171a237
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
  unfold Triple Triple_postcond
  have h_main : (Triple (x) h_precond) / 3 = x := by
    have h₁ : Triple (x) h_precond = 3 * x := by
      simp [Triple, Triple_precond, mul_comm]
      <;> ring
      <;> simp_all
      <;> omega
    rw [h₁]
    -- Now we need to prove that (3 * x) / 3 = x
    -- This is straightforward since 3 * x is divisible by 3
    have h₂ : (3 * x) / 3 = x := by
      have h₃ : (3 * x) / 3 = x := by
        omega
      exact h₃
    rw [h₂]
    <;> simp_all
    <;> omega

  have h_main2 : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    have h₁ : Triple (x) h_precond = 3 * x := by
      simp [Triple, Triple_precond, mul_comm]
      <;> ring
      <;> simp_all
      <;> omega
    rw [h₁] at *
    have h₂ : ((3 * x) / 3) * 3 = 3 * x := by
      have h₃ : (3 * x) / 3 * 3 = 3 * x := by
        have h₄ : (3 * x) / 3 * 3 = 3 * x := by
          have h₅ : (3 * x) % 3 = 0 := by
            omega
          omega
        exact h₄
      exact h₃
    omega

  constructor
  · exact h_main
  · exact h_main2
  -- !benchmark @end proof
