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
  have h_main : (Triple (x) h_precond) / 3 = x := by
    dsimp [Triple]
    split_ifs with h
    · -- Case: x < 18
      have h₁ : ((2 * x + 4 * x) / 2 : ℤ) = 3 * x := by
        have h₂ : (2 * x + 4 * x : ℤ) = 6 * x := by ring
        rw [h₂]
        have h₃ : (6 * x : ℤ) / 2 = 3 * x := by
          have h₄ : (6 * x : ℤ) = 2 * (3 * x) := by ring
          rw [h₄]
          -- Since 2 * (3 * x) is divisible by 2, the division is exact.
          have h₅ : (2 * (3 * x) : ℤ) / 2 = 3 * x := by
            have h₆ : (2 : ℤ) ≠ 0 := by norm_num
            have h₇ : (2 * (3 * x) : ℤ) / 2 = 3 * x := by
              apply Int.ediv_eq_of_eq_mul_right (by norm_num : (2 : ℤ) ≠ 0)
              <;> ring
            exact h₇
          exact h₅
        rw [h₃]
      rw [h₁]
      -- Now we need to show (3 * x) / 3 = x
      have h₂ : (3 * x : ℤ) / 3 = x := by
        have h₃ : (3 : ℤ) ≠ 0 := by norm_num
        have h₄ : (3 * x : ℤ) / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
          <;> ring
        exact h₄
      rw [h₂]
    · -- Case: x ≥ 18
      have h₁ : (x + 2 * x : ℤ) = 3 * x := by ring
      have h₂ : (x + 2 * x : ℤ) = 3 * x := by ring
      have h₃ : (3 * x : ℤ) / 3 = x := by
        have h₄ : (3 : ℤ) ≠ 0 := by norm_num
        have h₅ : (3 * x : ℤ) / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
          <;> ring
        exact h₅
      simp_all [h₁, h₂]
      <;> ring_nf at *
      <;> omega

  have h_main₂ : (Triple (x) h_precond) / 3 * 3 = (Triple (x) h_precond) := by
    have h₁ : (Triple (x) h_precond) / 3 = x := h_main
    have h₂ : (Triple (x) h_precond) / 3 * 3 = x * 3 := by
      rw [h₁]
      <;> ring
    have h₃ : x * 3 = (Triple (x) h_precond) := by
      have h₄ : (Triple (x) h_precond) = 3 * x := by
        dsimp [Triple]
        split_ifs with h
        · -- Case: x < 18
          have h₅ : ((2 * x + 4 * x) / 2 : ℤ) = 3 * x := by
            have h₆ : (2 * x + 4 * x : ℤ) = 6 * x := by ring
            rw [h₆]
            have h₇ : (6 * x : ℤ) / 2 = 3 * x := by
              have h₈ : (6 * x : ℤ) = 2 * (3 * x) := by ring
              rw [h₈]
              -- Since 2 * (3 * x) is divisible by 2, the division is exact.
              have h₉ : (2 * (3 * x) : ℤ) / 2 = 3 * x := by
                have h₁₀ : (2 : ℤ) ≠ 0 := by norm_num
                have h₁₁ : (2 * (3 * x) : ℤ) / 2 = 3 * x := by
                  apply Int.ediv_eq_of_eq_mul_right (by norm_num : (2 : ℤ) ≠ 0)
                  <;> ring
                exact h₁₁
              exact h₉
            rw [h₇]
          rw [h₅]
          <;> ring
        · -- Case: x ≥ 18
          have h₅ : (x + 2 * x : ℤ) = 3 * x := by ring
          simp_all [h₅]
          <;> ring_nf at *
          <;> omega
      rw [h₄]
      <;> ring
      <;> omega
    linarith

  constructor
  · -- Prove the first part: (Triple x) / 3 = x
    exact h_main
  · -- Prove the second part: (Triple x) / 3 * 3 = Triple x
    exact h_main₂
  -- !benchmark @end proof
