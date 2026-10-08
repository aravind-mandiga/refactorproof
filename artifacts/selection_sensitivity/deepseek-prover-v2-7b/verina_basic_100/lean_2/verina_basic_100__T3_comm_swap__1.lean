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
  have h_main : (Triple (x) h_precond) / 3 = x ∧ (Triple (x) h_precond) / 3 * 3 = Triple (x) h_precond := by
    by_cases hx : x = 0
    · -- Case x = 0
      have h₁ : Triple (x) h_precond = 0 := by
        simp [Triple, hx]
        <;> simp_all [Triple_precond, h_precond]
      rw [h₁]
      constructor
      · -- Prove 0 / 3 = x
        norm_num [hx]
        <;> aesop
      · -- Prove (0 / 3) * 3 = 0
        norm_num [hx]
        <;> aesop
    · -- Case x ≠ 0
      have h₁ : Triple (x) h_precond = 3 * x := by
        simp [Triple, hx, mul_comm]
        <;> ring_nf
        <;> aesop
      rw [h₁]
      constructor
      · -- Prove (3 * x) / 3 = x
        have h₂ : (3 * x) / 3 = x := by
          have h₃ : x ≠ 0 := hx
          omega
        exact h₂
      · -- Prove ((3 * x) / 3) * 3 = 3 * x
        have h₂ : ((3 * x) / 3) * 3 = 3 * x := by
          have h₃ : x ≠ 0 := hx
          have h₄ : (3 * x : ℤ) / 3 = x := by
            have h₅ : (3 * x : ℤ) / 3 = x := by
              omega
            exact h₅
          have h₅ : ((3 * x : ℤ) / 3) * 3 = (x : ℤ) * 3 := by
            rw [h₄]
            <;> ring
          have h₆ : ((3 * x : ℤ) / 3) * 3 = 3 * x := by
            linarith
          exact h₆
        linarith
  exact h_main
  -- !benchmark @end proof
