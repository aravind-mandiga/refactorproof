-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Abs_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Abs (x : Int) (h_precond : Abs_precond (x)) : Int :=
  -- !benchmark @start code
  if ¬ (x < 0) then x
  else -x
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Abs_postcond (x : Int) (result: Int) (h_precond : Abs_precond (x)) :=
  -- !benchmark @start postcond
  (x ≥ 0 → x = result) ∧ (x < 0 → x + result = 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Abs_spec_satisfied (x: Int) (h_precond : Abs_precond (x)) :
    Abs_postcond (x) (Abs (x) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : Abs_postcond (x) (Abs (x) h_precond) h_precond := by
    constructor
    · -- Prove the first part: if x ≥ 0, then x = Abs x
      intro hx
      have h₁ : x = Abs (x) h_precond := by
        by_cases hx' : x < 0
        · -- Case: x < 0
          exfalso
          linarith
        · -- Case: x ≥ 0
          have h₂ : x ≥ 0 := by linarith
          have h₃ : Abs (x) h_precond = x := by
            simp [Abs, h₂]
            <;> omega
          simp_all
          <;> omega
      exact h₁
    · -- Prove the second part: if x < 0, then x + Abs x = 0
      intro hx
      have h₁ : x + Abs (x) h_precond = 0 := by
        by_cases hx' : x < 0
        · -- Case: x < 0
          have h₂ : Abs (x) h_precond = -x := by
            simp [Abs, hx']
            <;> omega
          rw [h₂]
          <;> omega
        · -- Case: x ≥ 0
          exfalso
          linarith
      exact h₁
  exact h_main
  -- !benchmark @end proof
