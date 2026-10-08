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

private def Triple__rp_helper_5b862de8 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  if x < 18 then
    let a := 2 * x
    let b := 4 * x
    (a + b) / 2
  else
    let y := 2 * x
    x + y
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  Triple__rp_helper_5b862de8 x h_precond
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
  have h_main : Triple_postcond x (Triple x h_precond) h_precond := by
    dsimp [Triple_postcond] at *
    have h₁ : Triple x h_precond = if x < 18 then (2 * x + 4 * x) / 2 else x + 2 * x := by
      simp [Triple, h_precond]
      <;> aesop
    rw [h₁]
    split_ifs with h₂
    · -- Case: x < 18
      have h₃ : (2 * x + 4 * x) / 2 = 3 * x := by
        have h₄ : (2 * x + 4 * x) = 6 * x := by ring
        rw [h₄]
        <;> omega
      rw [h₃]
      <;>
      (try omega) <;>
      (try
        {
          constructor <;>
          (try omega) <;>
          (try
            {
              have h₅ : x ≤ 18 := by omega
              have h₆ : x ≥ -18 := by omega
              interval_cases x <;> norm_num <;> omega
            }
          )
        }
      ) <;>
      (try
        {
          simp_all [Int.mul_ediv_cancel_left]
          <;> omega
        }
      )
    · -- Case: x ≥ 18
      have h₃ : x + 2 * x = 3 * x := by ring
      rw [h₃]
      <;>
      (try omega) <;>
      (try
        {
          constructor <;>
          (try omega) <;>
          (try
            {
              have h₄ : x ≥ 18 := by omega
              have h₅ : x ≤ 18 := by omega
              omega
            }
          )
        }
      ) <;>
      (try
        {
          simp_all [Int.mul_ediv_cancel_left]
          <;> omega
        }
      )
  exact h_main
  -- !benchmark @end proof
