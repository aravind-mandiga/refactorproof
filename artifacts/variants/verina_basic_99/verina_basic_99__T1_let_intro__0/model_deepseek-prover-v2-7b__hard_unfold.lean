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
  let __rp_tmp_25d1f142 : Int :=
    if x < 18 then
      let a := 2 * x
      let b := 4 * x
      (a + b) / 2
    else
      let y := 2 * x
      x + y
  __rp_tmp_25d1f142
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
  unfold Triple Triple_postcond
  have h_main : Triple_postcond x (Triple x h_precond) h_precond := by
    unfold Triple Triple_postcond
    split_ifs with h
    · -- Case: x < 18
      have h₁ : (2 * x + 4 * x) / 2 = 3 * x := by
        have h₂ : 2 * x + 4 * x = 6 * x := by ring
        rw [h₂]
        <;>
        (try omega) <;>
        (try
          {
            omega
          }) <;>
        (try
          {
            -- We need to show that (6 * x) / 2 = 3 * x
            have h₃ : (6 * x) / 2 = 3 * x := by
              have h₄ : x ≤ 17 := by linarith
              have h₅ : x ≥ -17 := by linarith
              interval_cases x <;> norm_num <;> omega
            exact h₃
          })
        <;>
        omega
      have h₂ : ((2 * x + 4 * x) / 2) / 3 = x := by
        rw [h₁]
        <;>
        (try omega) <;>
        (try
          {
            have h₃ : x ≤ 17 := by linarith
            have h₄ : x ≥ -17 := by linarith
            interval_cases x <;> norm_num <;> omega
          })
        <;>
        omega
      have h₃ : ((2 * x + 4 * x) / 2) / 3 * 3 = (2 * x + 4 * x) / 2 := by
        rw [h₂]
        <;>
        (try
          {
            ring_nf at *
            <;>
            omega
          })
        <;>
        omega
      simp_all [h₁, h₂, h₃]
      <;>
      (try omega) <;>
      (try
        {
          ring_nf at *
          <;>
          simp_all
          <;>
          omega
        })
    · -- Case: x ≥ 18
      have h₁ : x + 2 * x = 3 * x := by ring
      have h₂ : (x + 2 * x) / 3 = x := by
        have h₃ : x ≥ 18 := by linarith
        have h₄ : (x + 2 * x) / 3 = x := by
          have h₅ : x ≥ 18 := by linarith
          have h₆ : (x + 2 * x) / 3 = x := by
            -- Prove that (x + 2 * x) / 3 = x when x ≥ 18
            omega
          exact h₆
        exact h₄
      have h₃ : ((x + 2 * x) / 3) * 3 = x + 2 * x := by
        have h₄ : (x + 2 * x) / 3 = x := by exact h₂
        have h₅ : ((x + 2 * x) / 3) * 3 = x + 2 * x := by
          omega
        exact h₅
      simp_all [h₁, h₂, h₃]
      <;>
      (try omega) <;>
      (try
        {
          ring_nf at *
          <;>
          simp_all
          <;>
          omega
        })
  exact h_main
  -- !benchmark @end proof
