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
  have h_main : Triple_postcond x (Triple x h_precond) h_precond := by
    by_cases hx : x = 0
    · -- Case: x = 0
      have h₁ : Triple x h_precond = 0 := by
        simp [hx, Triple]
        <;> simp_all [Triple_precond]
        <;> norm_num
      have h₂ : (Triple x h_precond) / 3 = x := by
        rw [h₁]
        simp [hx]
        <;> norm_num
      have h₃ : (Triple x h_precond) / 3 * 3 = Triple x h_precond := by
        rw [h₁]
        <;> norm_num
      exact ⟨h₂, h₃⟩
    · -- Case: x ≠ 0
      have h₁ : Triple x h_precond = 3 * x := by
        have h₂ : ¬x = 0 := hx
        simp [h₂, Triple]
        <;> ring_nf
        <;> simp_all [Triple_precond]
        <;> norm_num
        <;> linarith
      have h₂ : (Triple x h_precond) / 3 = x := by
        rw [h₁]
        have h₃ : (3 * x : Int) / 3 = x := by
          have h₄ : (3 : Int) ≠ 0 := by norm_num
          have h₅ : (x * 3 : Int) / 3 = x := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : Int) ≠ 0)
            <;> ring_nf
            <;> simp [mul_assoc]
          have h₆ : (3 * x : Int) = (x * 3 : Int) := by ring
          rw [h₆]
          exact h₅
        exact h₃
      have h₃ : (Triple x h_precond) / 3 * 3 = Triple x h_precond := by
        rw [h₂]
        have h₄ : (x : Int) * 3 = 3 * x := by ring
        have h₅ : (x : Int) * 3 = Triple x h_precond := by
          rw [h₁]
          <;> ring
        linarith
      exact ⟨h₂, h₃⟩
  exact h_main
  -- !benchmark @end proof
