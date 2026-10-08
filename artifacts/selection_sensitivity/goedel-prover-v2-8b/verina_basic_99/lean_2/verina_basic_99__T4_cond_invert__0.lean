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
  if ¬ (x < 18) then
    let y := 2 * x
    x + y
  else
    let a := 2 * x
    let b := 4 * x
    (a + b) / 2
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
  have h_result : Triple (x) h_precond = 3 * x := by
    by_cases h : x < 18
    · -- Case: x < 18
      have h₁ : Triple (x) h_precond = (2 * x + 4 * x) / 2 := by
        dsimp [Triple, Triple_precond]
        <;> simp [h]
        <;> ring_nf
        <;> norm_num
      rw [h₁]
      have h₂ : (2 * x + 4 * x : ℤ) = 6 * x := by ring
      rw [h₂]
      have h₃ : (6 * x : ℤ) / 2 = 3 * x := by
        have h₄ : (6 * x : ℤ) = 2 * (3 * x) := by ring
        rw [h₄]
        have h₅ : (2 * (3 * x) : ℤ) / 2 = 3 * x := by
          have h₆ : (2 * (3 * x) : ℤ) / 2 = 3 * x := by
            omega
          exact h₆
        exact h₅
      rw [h₃]
    · -- Case: x ≥ 18
      have h₁ : Triple (x) h_precond = x + 2 * x := by
        dsimp [Triple, Triple_precond]
        <;> simp [h, le_of_not_lt]
        <;> ring_nf
        <;> norm_num
      rw [h₁]
      <;> ring
      <;> omega

  have h_div : (Triple (x) h_precond) / 3 = x := by
    rw [h_result]
    have h₁ : (3 * x : ℤ) / 3 = x := by
      have h₂ : (3 * x : ℤ) = 3 * x := by ring
      rw [h₂]
      have h₃ : (3 * x : ℤ) / 3 = x := by
        omega
      exact h₃
    exact h₁

  have h_mul : (Triple (x) h_precond) / 3 * 3 = Triple (x) h_precond := by
    rw [h_div]
    <;> rw [h_result]
    <;> ring
    <;> omega

  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    constructor
    · -- Prove result / 3 = x
      exact h_div
    · -- Prove result / 3 * 3 = result
      exact h_mul

  exact h_main
  -- !benchmark @end proof
