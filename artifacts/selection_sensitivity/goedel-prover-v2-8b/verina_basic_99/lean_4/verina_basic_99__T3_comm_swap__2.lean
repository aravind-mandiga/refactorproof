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
  if x < 18 then
    let a := 2 * x
    let b := 4 * x
    (a + b) / 2
  else
    let y := x * 2
    x + y
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
  have h_main : Triple x h_precond = 3 * x := by
    by_cases h : x < 18
    · -- Case: x < 18
      have h₁ : Triple x h_precond = (2 * x + 4 * x) / 2 := by
        simp [Triple, h, h_precond]
        <;> ring_nf
        <;> norm_num
        <;> omega
      rw [h₁]
      have h₂ : (2 * x + 4 * x : ℤ) / 2 = 3 * x := by
        have h₃ : (2 * x + 4 * x : ℤ) = 6 * x := by ring
        rw [h₃]
        have h₄ : (6 * x : ℤ) / 2 = 3 * x := by
          have h₅ : (6 : ℤ) * x / 2 = 3 * x := by
            omega
          exact h₅
        exact h₄
      rw [h₂]
    · -- Case: x ≥ 18
      have h₁ : Triple x h_precond = x + 2 * x := by
        simp [Triple, h, h_precond]
        <;> ring_nf
        <;> norm_num
        <;> omega
      rw [h₁]
      have h₂ : x + 2 * x = 3 * x := by ring
      rw [h₂]

  have h_div : (Triple x h_precond) / 3 = x := by
    rw [h_main]
    have h₁ : (3 * x : ℤ) / 3 = x := by
      have h₂ : (3 : ℤ) * x / 3 = x := by
        omega
      exact h₂
    exact h₁

  have h_mul : (Triple x h_precond) / 3 * 3 = Triple x h_precond := by
    rw [h_main]
    have h₁ : (3 * x : ℤ) / 3 * 3 = 3 * x := by
      have h₂ : (3 : ℤ) * x / 3 = x := by
        omega
      rw [h₂]
      <;> ring
    exact h₁

  have h_final : Triple_postcond x (Triple x h_precond) h_precond := by
    constructor
    · -- Prove the first part of the conjunction: result / 3 = x
      exact h_div
    · -- Prove the second part of the conjunction: (result / 3) * 3 = result
      exact h_mul

  exact h_final
  -- !benchmark @end proof
