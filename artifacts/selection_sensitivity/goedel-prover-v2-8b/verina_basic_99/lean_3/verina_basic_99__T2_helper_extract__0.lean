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
  have h_triple : Triple (x) h_precond = 3 * x := by
    by_cases hx : x < 18
    · -- Case: x < 18
      have h₁ : Triple (x) h_precond = (2 * x + 4 * x) / 2 := by
        simp [hx, Triple, h_precond]
        <;> norm_num
      rw [h₁]
      have h₂ : (2 * x + 4 * x : ℤ) / 2 = 3 * x := by
        have h₃ : 2 * x + 4 * x = 6 * x := by ring
        rw [h₃]
        have h₄ : (6 * x : ℤ) / 2 = 3 * x := by
          have h₅ : (6 * x : ℤ) / 2 = 3 * x := by
            have h₆ : (6 * x : ℤ) / 2 = 3 * x := by
              omega
            exact h₆
          exact h₅
        exact h₄
      rw [h₂]
    · -- Case: x ≥ 18
      have h₁ : Triple (x) h_precond = x + 2 * x := by
        simp [hx, Triple, h_precond]
        <;> norm_num
        <;> omega
      rw [h₁]
      <;> ring
      <;> omega

  have h_div : (3 * x : ℤ) / 3 = x := by
    have h₁ : (3 * x : ℤ) / 3 = x := by
      have h₂ : (3 * x : ℤ) = 3 * x := by ring
      rw [h₂]
      -- Use the property of integer division to simplify the expression
      have h₃ : (3 * x : ℤ) / 3 = x := by
        -- Prove that (3 * x) / 3 = x using the properties of integer division
        have h₄ : (3 * x : ℤ) % 3 = 0 := by
          omega
        have h₅ : (3 * x : ℤ) / 3 = x := by
          omega
        exact h₅
      exact h₃
    exact h₁

  have h_div_mul : (3 * x : ℤ) / 3 * 3 = 3 * x := by
    have h₁ : (3 * x : ℤ) / 3 = x := h_div
    have h₂ : (3 * x : ℤ) / 3 * 3 = 3 * x := by
      rw [h₁]
      <;> ring
      <;> omega
    exact h₂

  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    rw [h_triple]
    constructor
    · -- Prove that (3 * x) / 3 = x
      exact h_div
    · -- Prove that (3 * x) / 3 * 3 = 3 * x
      exact h_div_mul

  exact h_main
  -- !benchmark @end proof
