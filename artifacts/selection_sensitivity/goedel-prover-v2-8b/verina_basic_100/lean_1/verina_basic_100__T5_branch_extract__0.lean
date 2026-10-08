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

private def Triple__rp_branch_9f218861 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  let y := 2 * x
  x + y
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  if x = 0 then 0 else
    Triple__rp_branch_9f218861 x h_precond
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
  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    by_cases hx : x = 0
    · -- Case: x = 0
      have h₁ : Triple (x) h_precond = 0 := by
        simp [Triple, hx]
      have h₂ : (Triple (x) h_precond : ℤ) / 3 = x := by
        rw [h₁]
        simp [hx]
      have h₃ : (Triple (x) h_precond : ℤ) / 3 * 3 = Triple (x) h_precond := by
        rw [h₁]
        <;> simp [hx]
      exact ⟨h₂, h₃⟩
    · -- Case: x ≠ 0
      have h₁ : Triple (x) h_precond = 3 * x := by
        have h₂ : x ≠ 0 := hx
        have h₃ : Triple (x) h_precond = 3 * x := by
          simp [Triple, h₂, Int.mul_add, Int.add_mul, Int.mul_one, Int.mul_zero]
          <;> ring_nf
          <;> omega
        exact h₃
      have h₂ : (Triple (x) h_precond : ℤ) / 3 = x := by
        rw [h₁]
        have h₃ : (3 * x : ℤ) / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_left
          <;> ring_nf
          <;> norm_num
          <;> omega
        exact h₃
      have h₃ : (Triple (x) h_precond : ℤ) / 3 * 3 = Triple (x) h_precond := by
        rw [h₂, h₁]
        <;> ring_nf
        <;> omega
      exact ⟨h₂, h₃⟩
  exact h_main
  -- !benchmark @end proof
