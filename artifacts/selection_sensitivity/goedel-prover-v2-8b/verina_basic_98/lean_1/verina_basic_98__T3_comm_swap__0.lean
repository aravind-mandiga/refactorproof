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
  have h₁ : (Triple (x) h_precond) / 3 = x := by
    have h₂ : Triple (x) h_precond = x * 3 := rfl
    rw [h₂]
    have h₃ : (x * 3 : ℤ) / 3 = x := by
      have h₄ : (x * 3 : ℤ) = 3 * x := by ring
      rw [h₄]
      -- Use the lemma `Int.mul_ediv_cancel_left` to simplify the expression
      have h₅ : (3 : ℤ) ≠ 0 := by norm_num
      have h₆ : (3 * x : ℤ) / 3 = x := by
        apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
        <;> ring
      exact h₆
    exact h₃

  have h₂ : (Triple (x) h_precond) / 3 * 3 = Triple (x) h_precond := by
    have h₃ : Triple (x) h_precond = x * 3 := rfl
    rw [h₃]
    have h₄ : (x * 3 : ℤ) / 3 = x := by
      have h₅ : (x * 3 : ℤ) = 3 * x := by ring
      rw [h₅]
      -- Use the lemma `Int.mul_ediv_cancel_left` to simplify the expression
      have h₆ : (3 : ℤ) ≠ 0 := by norm_num
      have h₇ : (3 * x : ℤ) / 3 = x := by
        apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
        <;> ring
      exact h₇
    -- Now we have (x * 3 : ℤ) / 3 = x, so we can simplify the goal
    rw [h₄]
    <;> ring

  have h₃ : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    refine' ⟨_, _⟩
    · -- Prove the first condition: (Triple (x) h_precond) / 3 = x
      exact h₁
    · -- Prove the second condition: (Triple (x) h_precond) / 3 * 3 = Triple (x) h_precond
      exact h₂

  exact h₃
  -- !benchmark @end proof
