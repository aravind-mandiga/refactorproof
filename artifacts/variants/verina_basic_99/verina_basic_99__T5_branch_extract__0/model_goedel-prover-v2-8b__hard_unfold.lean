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
  unfold Triple Triple_postcond
  have h_main : Triple x h_precond = 3 * x := by
    by_cases hx : x < 18
    · -- Case: x < 18
      have h₁ : Triple x h_precond = (2 * x + 4 * x) / 2 := by
        simp [hx, Triple, Int.mul_add, Int.add_mul]
        <;>
        (try decide) <;>
        (try omega) <;>
        (try ring_nf at * <;> omega)
      rw [h₁]
      have h₂ : (2 * x + 4 * x : ℤ) / 2 = 3 * x := by
        have h₃ : (2 * x + 4 * x : ℤ) = 6 * x := by ring
        rw [h₃]
        have h₄ : (6 * x : ℤ) / 2 = 3 * x := by
          have h₅ : (6 * x : ℤ) = 2 * (3 * x) := by ring
          rw [h₅]
          have h₆ : (2 * (3 * x) : ℤ) / 2 = 3 * x := by
            have h₇ : (2 * (3 * x) : ℤ) = 3 * x * 2 := by ring
            rw [h₇]
            have h₈ : (3 * x * 2 : ℤ) / 2 = 3 * x := by
              have h₉ : (3 * x * 2 : ℤ) = 2 * (3 * x) := by ring
              rw [h₉]
              have h₁₀ : (2 * (3 * x) : ℤ) / 2 = 3 * x := by
                -- Use the fact that 2 * (3 * x) is even
                have h₁₁ : (2 * (3 * x) : ℤ) / 2 = 3 * x := by
                  apply Int.ediv_eq_of_eq_mul_right (by norm_num : (2 : ℤ) ≠ 0)
                  <;> ring_nf <;> omega
                exact h₁₁
              exact h₁₀
            exact h₈
          exact h₆
        exact h₄
      rw [h₂]
    · -- Case: x ≥ 18
      have h₁ : Triple x h_precond = x + 2 * x := by
        have h₂ : ¬x < 18 := hx
        have h₃ : x ≥ 18 := by linarith
        simp [h₂, Triple]
        <;>
        (try decide) <;>
        (try omega) <;>
        (try ring_nf at * <;> omega)
      rw [h₁]
      ring_nf
      <;>
      (try decide) <;>
      (try omega) <;>
      (try ring_nf at * <;> omega)

  have h_final : Triple_postcond x (Triple x h_precond) h_precond := by
    rw [h_main]
    constructor
    · -- Prove that (3 * x) / 3 = x
      have h₁ : (3 * x : ℤ) / 3 = x := by
        have h₂ : (3 * x : ℤ) = 3 * x := by ring
        rw [h₂]
        have h₃ : (3 * x : ℤ) / 3 = x := by
          have h₄ : (3 * x : ℤ) = 3 * x := by ring
          rw [h₄]
          have h₅ : (3 * x : ℤ) / 3 = x := by
            -- Use the fact that 3 * x is divisible by 3
            have h₆ : (3 * x : ℤ) / 3 = x := by
              apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
              <;> ring_nf <;> omega
            exact h₆
          exact h₅
        exact h₃
      exact h₁
    · -- Prove that ((3 * x) / 3) * 3 = 3 * x
      have h₁ : ((3 * x : ℤ) / 3 : ℤ) * 3 = 3 * x := by
        have h₂ : (3 * x : ℤ) / 3 = x := by
          have h₃ : (3 * x : ℤ) = 3 * x := by ring
          rw [h₃]
          have h₄ : (3 * x : ℤ) / 3 = x := by
            -- Use the fact that 3 * x is divisible by 3
            have h₅ : (3 * x : ℤ) / 3 = x := by
              apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
              <;> ring_nf <;> omega
            exact h₅
          exact h₄
        rw [h₂]
        <;> ring_nf
        <;> omega
      exact h₁

  exact h_final
  -- !benchmark @end proof
