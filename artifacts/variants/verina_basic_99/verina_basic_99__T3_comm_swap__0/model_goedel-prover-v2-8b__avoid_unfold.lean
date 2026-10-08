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
    let a := x * 2
    let b := 4 * x
    (a + b) / 2
  else
    let y := 2 * x
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
  by_cases h : x < 18
  · -- Case: x < 18
    have h₁ : Triple (x) h_precond = 3 * x := by
      have h₂ : Triple (x) h_precond = (2 * x + 4 * x) / 2 := by
        rw [Triple]
        <;> simp_all [h, Triple_precond]
        <;> norm_num
        <;> omega
      rw [h₂]
      have h₃ : (2 * x + 4 * x : ℤ) / 2 = 3 * x := by
        have h₄ : (2 * x + 4 * x : ℤ) = 6 * x := by ring
        rw [h₄]
        have h₅ : (6 * x : ℤ) / 2 = 3 * x := by
          have h₆ : (6 : ℤ) * x / 2 = 3 * x := by
            have h₇ : x % 2 = 0 ∨ x % 2 = 1 ∨ x % 2 = -1 := by
              omega
            rcases h₇ with (h₇ | h₇ | h₇)
            · -- Case: x % 2 = 0
              have h₈ : x % 2 = 0 := h₇
              have h₉ : (6 : ℤ) * x / 2 = 3 * x := by
                have h₁₀ : (6 : ℤ) * x = 2 * (3 * x) := by ring
                rw [h₁₀]
                have h₁₁ : (2 : ℤ) * (3 * x) / 2 = 3 * x := by
                  have h₁₂ : (2 : ℤ) * (3 * x) / 2 = 3 * x := by
                    omega
                  exact h₁₂
                exact h₁₁
              exact h₉
            · -- Case: x % 2 = 1
              have h₈ : x % 2 = 1 := h₇
              have h₉ : (6 : ℤ) * x / 2 = 3 * x := by
                have h₁₀ : (6 : ℤ) * x = 2 * (3 * x) + 0 := by
                  omega
                rw [h₁₀]
                have h₁₁ : (2 : ℤ) * (3 * x) / 2 = 3 * x := by
                  omega
                omega
              exact h₉
            · -- Case: x % 2 = -1
              have h₈ : x % 2 = -1 := h₇
              have h₉ : (6 : ℤ) * x / 2 = 3 * x := by
                have h₁₀ : (6 : ℤ) * x = 2 * (3 * x) + 0 := by
                  omega
                rw [h₁₀]
                have h₁₁ : (2 : ℤ) * (3 * x) / 2 = 3 * x := by
                  omega
                omega
              exact h₉
          exact h₆
        exact h₅
      rw [h₃]
    have h₂ : Triple_postcond (x) (3 * x) h_precond := by
      constructor
      · -- Prove (3 * x) / 3 = x
        have h₃ : (3 * x : ℤ) / 3 = x := by
          have h₄ : (3 * x : ℤ) / 3 = x := by
            omega
          exact h₄
        exact h₃
      · -- Prove (3 * x) / 3 * 3 = 3 * x
        have h₃ : (3 * x : ℤ) / 3 * 3 = 3 * x := by
          have h₄ : (3 * x : ℤ) / 3 = x := by
            omega
          rw [h₄]
          <;> ring
          <;> omega
        exact h₃
    rw [h₁] at *
    exact h₂
  · -- Case: x ≥ 18
    have h₁ : Triple (x) h_precond = 3 * x := by
      have h₂ : Triple (x) h_precond = x + 2 * x := by
        rw [Triple]
        <;> simp_all [h, Triple_precond]
        <;> norm_num
        <;> omega
      rw [h₂]
      <;> ring
      <;> omega
    have h₂ : Triple_postcond (x) (3 * x) h_precond := by
      constructor
      · -- Prove (3 * x) / 3 = x
        have h₃ : (3 * x : ℤ) / 3 = x := by
          have h₄ : (3 * x : ℤ) / 3 = x := by
            omega
          exact h₄
        exact h₃
      · -- Prove (3 * x) / 3 * 3 = 3 * x
        have h₃ : (3 * x : ℤ) / 3 * 3 = 3 * x := by
          have h₄ : (3 * x : ℤ) / 3 = x := by
            omega
          rw [h₄]
          <;> ring
          <;> omega
        exact h₃
    rw [h₁] at *
    exact h₂
  -- !benchmark @end proof
