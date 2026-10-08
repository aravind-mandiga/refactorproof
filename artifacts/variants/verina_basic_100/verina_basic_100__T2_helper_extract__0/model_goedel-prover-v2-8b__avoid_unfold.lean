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

private def Triple__rp_helper_574d859a (x : Int) (h_precond : Triple_precond (x)) : Int :=
  if x = 0 then 0 else
    let y := 2 * x
    x + y
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  Triple__rp_helper_574d859a x h_precond
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
    have h₁ : Triple (x) h_precond = if x = 0 then 0 else 3 * x := by
      by_cases hx : x = 0
      · -- Case: x = 0
        rw [hx]
        simp [Triple, hx]
        <;> norm_num
      · -- Case: x ≠ 0
        simp [Triple, hx]
        <;> ring
        <;> simp_all
        <;> norm_num
        <;> omega
    rw [h₁]
    constructor
    · -- Prove (if x = 0 then 0 else 3 * x) / 3 = x
      split_ifs with hx
      · -- Subcase: x = 0
        simp [hx]
      · -- Subcase: x ≠ 0
        have h₂ : (3 * x : ℤ) / 3 = x := by
          have h₃ : (3 * x : ℤ) % 3 = 0 := by
            omega
          have h₄ : (3 * x : ℤ) / 3 = x := by
            omega
          exact h₄
        simp_all
    · -- Prove ((if x = 0 then 0 else 3 * x) / 3) * 3 = (if x = 0 then 0 else 3 * x)
      split_ifs with hx
      · -- Subcase: x = 0
        simp [hx]
      · -- Subcase: x ≠ 0
        have h₂ : (3 * x : ℤ) / 3 = x := by
          have h₃ : (3 * x : ℤ) % 3 = 0 := by
            omega
          have h₄ : (3 * x : ℤ) / 3 = x := by
            omega
          exact h₄
        have h₃ : ((3 * x : ℤ) / 3) * 3 = 3 * x := by
          rw [h₂]
          <;> ring
          <;> omega
        simp_all
  exact h_main
  -- !benchmark @end proof
