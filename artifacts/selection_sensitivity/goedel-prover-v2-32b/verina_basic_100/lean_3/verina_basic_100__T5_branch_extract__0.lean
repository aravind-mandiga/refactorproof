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
  have h_triple_eq : Triple x h_precond = 3 * x := by
    by_cases hx : x = 0
    · -- Case: x = 0
      simp [hx, Triple, Triple_precond]
      <;> norm_num
    · -- Case: x ≠ 0
      simp [hx, Triple, Triple_precond]
      <;> ring_nf at *
      <;> simp_all [hx]
      <;> norm_num
      <;> linarith

  have h_div : (3 * x : ℤ) / 3 = x := by
    have h₁ : (3 : ℤ) ≠ 0 := by norm_num
    have h₂ : (3 * x : ℤ) / 3 = x := by
      apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
      <;> ring_nf
      <;> simp [mul_assoc]
      <;> linarith
    exact h₂

  have h_main : Triple_postcond x (Triple x h_precond) h_precond := by
    rw [h_triple_eq]
    have h₁ : (3 * x : ℤ) / 3 = x := h_div
    have h₂ : ((3 * x : ℤ) / 3) * 3 = 3 * x := by
      rw [h₁]
      <;> ring
    constructor
    · -- Prove (3 * x) / 3 = x
      exact h₁
    · -- Prove ((3 * x) / 3) * 3 = 3 * x
      exact h₂

  exact h_main
  -- !benchmark @end proof
