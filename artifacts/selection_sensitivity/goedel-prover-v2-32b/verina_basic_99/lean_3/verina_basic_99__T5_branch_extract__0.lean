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
  have h_main : Triple (x) h_precond = 3 * x := by
    dsimp only [Triple, Triple_precond] at *
    split_ifs with h
    · -- Case: x < 18
      have h₁ : ((2 * x + 4 * x : ℤ) / 2 : ℤ) = 3 * x := by
        have h₂ : (2 * x + 4 * x : ℤ) = 6 * x := by ring
        rw [h₂]
        have h₃ : (6 * x : ℤ) / 2 = 3 * x := by
          have h₄ : (6 * x : ℤ) = 2 * (3 * x : ℤ) := by ring
          rw [h₄]
          -- Since 2 * (3 * x) is divisible by 2, the division is exact
          <;> simp [Int.mul_ediv_cancel_left]
          <;> norm_num
        rw [h₃]
      -- Simplify the expression using the above result
      simp_all [h₁]
      <;> ring_nf at *
      <;> norm_num at *
      <;> linarith
    · -- Case: x ≥ 18
      have h₁ : (x + 2 * x : ℤ) = 3 * x := by ring
      simp_all [h₁]
      <;> ring_nf at *
      <;> norm_num at *
      <;> linarith

  have h_div : (Triple (x) h_precond) / 3 = x := by
    rw [h_main]
    <;>
    (try omega) <;>
    (try
      {
        have h₁ : (3 : ℤ) ∣ 3 * x := by
          use x
          <;> ring
        have h₂ : (3 * x : ℤ) / 3 = x := by
          have h₃ : (3 * x : ℤ) / 3 = x := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            <;> ring
          exact h₃
        exact h₂
      }) <;>
    (try
      {
        norm_num [Int.mul_emod, Int.add_emod] at *
        <;>
        (try omega)
      })
    <;>
    (try
      {
        ring_nf at *
        <;>
        norm_num at *
        <;>
        omega
      })
    <;>
    (try
      {
        omega
      })

  have h_mul : (Triple (x) h_precond) / 3 * 3 = Triple (x) h_precond := by
    have h₁ : (Triple (x) h_precond) / 3 * 3 = Triple (x) h_precond := by
      have h₂ : (Triple (x) h_precond) = 3 * x := h_main
      rw [h₂]
      have h₃ : (3 * x : ℤ) / 3 = x := by
        have h₄ : (3 : ℤ) ∣ 3 * x := by
          use x
          <;> ring
        have h₅ : (3 * x : ℤ) / 3 = x := by
          have h₆ : (3 * x : ℤ) / 3 = x := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            <;> ring
          exact h₆
        exact h₅
      have h₆ : ((3 * x : ℤ) / 3) * 3 = 3 * x := by
        rw [h₃]
        <;> ring
      linarith
    exact h₁

  exact ⟨h_div, h_mul⟩
  -- !benchmark @end proof
