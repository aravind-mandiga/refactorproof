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

private def Triple__rp_branch_609232c2 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  let y := 2 * x
  x + y
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  if x < 18 then
    let a := 2 * x
    let b := 4 * x
    (a + b) / 2
  else
    Triple__rp_branch_609232c2 x h_precond
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
    by_cases h : x < 18
    · -- Case: x < 18
      have h₁ : Triple (x) h_precond = (2 * x + 4 * x) / 2 := by
        dsimp [Triple, Triple_precond, h]
        <;> simp_all [Int.add_assoc]
        <;> ring_nf
        <;> norm_num
        <;> linarith
      rw [h₁]
      have h₂ : (2 * x + 4 * x : ℤ) / 2 = 3 * x := by
        have h₃ : 2 * x + 4 * x = 6 * x := by ring
        rw [h₃]
        have h₄ : (6 * x : ℤ) / 2 = 3 * x := by
          have h₅ : (6 * x : ℤ) = 2 * (3 * x) := by ring
          rw [h₅]
          -- Use the property that (2 * y) / 2 = y for any integer y
          have h₆ : (2 * (3 * x : ℤ)) / 2 = 3 * x := by
            apply Int.ediv_eq_of_eq_mul_right (show (2 : ℤ) ≠ 0 by norm_num)
            <;> ring_nf
            <;> linarith
          exact h₆
        exact h₄
      rw [h₂]
    · -- Case: x ≥ 18
      have h₁ : Triple (x) h_precond = x + 2 * x := by
        dsimp [Triple, Triple_precond, h]
        <;> simp_all [Int.add_assoc]
        <;> ring_nf
        <;> norm_num
        <;> linarith
      rw [h₁]
      have h₂ : x + 2 * x = 3 * x := by ring
      rw [h₂]
      <;> simp [h]
      <;> ring_nf
      <;> linarith

  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    rw [h_triple]
    constructor
    · -- Prove that (3 * x) / 3 = x
      have h₁ : (3 * x : ℤ) / 3 = x := by
        have h₂ : (3 * x : ℤ) = 3 * x := by ring
        rw [h₂]
        have h₃ : (3 * x : ℤ) / 3 = x := by
          have h₄ : (3 * x : ℤ) = 3 * x := by ring
          rw [h₄]
          -- Use the property that (3 * y) / 3 = y for any integer y
          have h₅ : (3 * x : ℤ) / 3 = x := by
            apply Int.ediv_eq_of_eq_mul_right (show (3 : ℤ) ≠ 0 by norm_num)
            <;> ring_nf
            <;> linarith
          exact h₅
        exact h₃
      exact h₁
    · -- Prove that ((3 * x) / 3) * 3 = 3 * x
      have h₁ : ((3 * x : ℤ) / 3) * 3 = 3 * x := by
        have h₂ : (3 * x : ℤ) / 3 = x := by
          have h₃ : (3 * x : ℤ) = 3 * x := by ring
          rw [h₃]
          have h₄ : (3 * x : ℤ) / 3 = x := by
            have h₅ : (3 * x : ℤ) = 3 * x := by ring
            rw [h₅]
            -- Use the property that (3 * y) / 3 = y for any integer y
            have h₆ : (3 * x : ℤ) / 3 = x := by
              apply Int.ediv_eq_of_eq_mul_right (show (3 : ℤ) ≠ 0 by norm_num)
              <;> ring_nf
              <;> linarith
            exact h₆
          exact h₄
        rw [h₂]
        <;> ring_nf
        <;> linarith
      exact h₁

  exact h_main
  -- !benchmark @end proof
