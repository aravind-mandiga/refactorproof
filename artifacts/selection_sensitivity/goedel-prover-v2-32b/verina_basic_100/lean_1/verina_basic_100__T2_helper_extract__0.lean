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
  have h_main : Triple_postcond x (Triple x h_precond) h_precond := by
    have h₁ : Triple x h_precond = if x = 0 then 0 else 3 * x := by
      dsimp [Triple]
      split_ifs with h
      · -- Case: x = 0
        simp [h]
      · -- Case: x ≠ 0
        have h₂ : x + 2 * x = 3 * x := by ring
        simp_all [h₂]
        <;> ring_nf
        <;> simp_all
        <;> linarith
    rw [h₁]
    split_ifs with h
    · -- Case: x = 0
      constructor
      · -- Prove 0 / 3 = x
        norm_num [h]
      · -- Prove 0 / 3 * 3 = 0
        norm_num [h]
    · -- Case: x ≠ 0
      have h₂ : (3 : Int) ≠ 0 := by norm_num
      have h₃ : (3 * x : Int) / 3 = x := by
        have h₄ : (3 : Int) * x / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : Int) ≠ 0)
          <;> ring_nf
          <;> simp_all
          <;> linarith
        exact h₄
      constructor
      · -- Prove (3 * x) / 3 = x
        exact h₃
      · -- Prove (3 * x) / 3 * 3 = 3 * x
        have h₄ : (3 * x : Int) / 3 * 3 = 3 * x := by
          have h₅ : (3 : Int) ∣ 3 * x := by
            use x
            <;> ring
          have h₆ : (3 * x : Int) / 3 * 3 = 3 * x := by
            have h₇ : (3 * x : Int) / 3 * 3 = 3 * x := by
              apply Int.ediv_mul_cancel h₅
            exact h₇
          exact h₆
        exact h₄
  exact h_main
  -- !benchmark @end proof
