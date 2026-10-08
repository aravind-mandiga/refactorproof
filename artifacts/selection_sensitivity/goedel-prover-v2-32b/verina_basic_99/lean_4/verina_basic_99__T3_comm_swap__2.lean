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
    dsimp [Triple]
    split_ifs with h
    · -- Case: x < 18
      have h₁ : (2 * x + 4 * x : ℤ) / 2 = 3 * x := by
        have h₂ : (2 * x + 4 * x : ℤ) = 6 * x := by ring
        rw [h₂]
        have h₃ : (6 * x : ℤ) / 2 = 3 * x := by
          have h₄ : (6 : ℤ) * x = 2 * (3 * x) := by ring
          rw [h₄]
          -- Since 2 * (3 * x) / 2 = 3 * x
          have h₅ : (2 : ℤ) * (3 * x) / 2 = 3 * x := by
            have h₆ : (2 : ℤ) ∣ 2 * (3 * x) := by
              use 3 * x
              <;> ring
            have h₇ : (2 : ℤ) * (3 * x) / 2 = 3 * x := by
              apply Int.ediv_eq_of_eq_mul_right (by norm_num : (2 : ℤ) ≠ 0)
              <;> ring
              <;> norm_num
            exact h₇
          exact h₅
        rw [h₃]
      -- Simplify the expression using the above result
      simp_all [h₁]
      <;> ring_nf at *
      <;> norm_num at *
      <;> linarith
    · -- Case: x ≥ 18
      have h₁ : x + 2 * x = 3 * x := by ring
      simp_all [h₁]
      <;> ring_nf at *
      <;> norm_num at *
      <;> linarith

  have h1 : (Triple x h_precond) / 3 = x := by
    rw [h_main]
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try
      {
        have h₂ : (3 : ℤ) * x / 3 = x := by
          have h₃ : (3 : ℤ) * x = 3 * x := by ring
          have h₄ : (3 : ℤ) * x / 3 = x := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            <;> ring_nf
            <;> norm_num
          exact h₄
        exact h₂
      }) <;>
    (try omega)

  have h2 : (Triple x h_precond / 3) * 3 = Triple x h_precond := by
    have h3 : (Triple x h_precond) / 3 = x := h1
    have h4 : Triple x h_precond = 3 * x := h_main
    have h5 : (Triple x h_precond / 3) * 3 = x * 3 := by
      rw [h3]
      <;> ring
    have h6 : x * 3 = Triple x h_precond := by
      rw [h4]
      <;> ring
    linarith

  have h_final : Triple_postcond x (Triple x h_precond) h_precond := by
    constructor
    · -- Prove the first part of the postcondition: (Triple x h_precond) / 3 = x
      exact h1
    · -- Prove the second part of the postcondition: (Triple x h_precond / 3) * 3 = Triple x h_precond
      exact h2

  exact h_final
  -- !benchmark @end proof
