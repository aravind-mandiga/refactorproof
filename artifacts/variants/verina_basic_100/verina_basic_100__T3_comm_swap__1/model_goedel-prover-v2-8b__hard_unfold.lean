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

-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  if x = 0 then 0 else
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
  unfold Triple Triple_postcond
  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    unfold Triple Triple_postcond
    split_ifs <;> simp_all [Int.mul_ediv_cancel_left]
    <;>
    (try omega) <;>
    (try
      {
        -- Prove that (3 * x) / 3 = x
        have h₁ : (3 * x : ℤ) / 3 = x := by
          have h₂ : (3 * x : ℤ) / 3 = x := by
            omega
          exact h₂
        -- Prove that ((3 * x) / 3) * 3 = 3 * x
        have h₂ : ((3 * x : ℤ) / 3) * 3 = 3 * x := by
          have h₃ : ((3 * x : ℤ) / 3) * 3 = 3 * x := by
            omega
          exact h₃
        omega
      }) <;>
    (try
      {
        -- Prove that x = 0
        have h₁ : x = 0 := by
          omega
        simp [h₁] at * <;> omega
      }) <;>
    (try
      {
        -- Prove that x ≠ 0
        have h₁ : x ≠ 0 := by
          omega
        have h₂ : (3 * x : ℤ) / 3 = x := by
          have h₃ : (3 * x : ℤ) / 3 = x := by
            omega
          exact h₃
        have h₃ : ((3 * x : ℤ) / 3) * 3 = 3 * x := by
          have h₄ : ((3 * x : ℤ) / 3) * 3 = 3 * x := by
            omega
          exact h₄
        omega
      })
  exact h_main
  -- !benchmark @end proof
