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
    have h₁ : Triple (x) h_precond = if x = 0 then 0 else 3 * x := by
      dsimp [Triple]
      split_ifs with h
      · -- Case: x = 0
        simp [h]
      · -- Case: x ≠ 0
        have h₂ : x ≠ 0 := h
        have h₃ : x + 2 * x = 3 * x := by ring
        simp [h₂, h₃]
        <;> ring_nf
        <;> simp_all
    rw [h₁]
    constructor
    · -- Prove (if x = 0 then 0 else 3 * x) / 3 = x
      split_ifs with h
      · -- Case: x = 0
        simp [h]
      · -- Case: x ≠ 0
        have h₂ : x ≠ 0 := h
        have h₃ : (3 * x : ℤ) / 3 = x := by
          have h₄ : (3 * x : ℤ) / 3 = x := by
            have h₅ : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 ∨ x % 3 = -1 ∨ x % 3 = -2 := by
              omega
            rcases h₅ with (h₅ | h₅ | h₅ | h₅ | h₅) <;>
              (try omega) <;>
              (try
                {
                  have h₆ : (3 * x : ℤ) / 3 = x := by
                    omega
                  exact h₆
                })
            <;>
            (try omega)
          exact h₄
        exact h₃
    · -- Prove (if x = 0 then 0 else 3 * x) / 3 * 3 = (if x = 0 then 0 else 3 * x)
      split_ifs with h
      · -- Case: x = 0
        simp [h]
      · -- Case: x ≠ 0
        have h₂ : x ≠ 0 := h
        have h₃ : (3 * x : ℤ) / 3 * 3 = 3 * x := by
          have h₄ : (3 * x : ℤ) / 3 = x := by
            have h₅ : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 ∨ x % 3 = -1 ∨ x % 3 = -2 := by
              omega
            rcases h₅ with (h₅ | h₅ | h₅ | h₅ | h₅) <;>
              (try omega) <;>
              (try
                {
                  have h₆ : (3 * x : ℤ) / 3 = x := by
                    omega
                  exact h₆
                })
            <;>
            (try omega)
          rw [h₄]
          <;> ring
        exact h₃
  exact h_main
  -- !benchmark @end proof
