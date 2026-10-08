-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ComputeAvg_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  -- !benchmark @start code
  (b + a) / 2
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def ComputeAvg_postcond (a : Int) (b : Int) (result: Int) (h_precond : ComputeAvg_precond (a) (b)) :=
  -- !benchmark @start postcond
  2 * result = a + b - ((a + b) % 2)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem ComputeAvg_spec_satisfied (a: Int) (b: Int) (h_precond : ComputeAvg_precond (a) (b)) :
    ComputeAvg_postcond (a) (b) (ComputeAvg (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : 2 * ((a + b) / 2) = (a + b) - ((a + b) % 2) := by
    have h₁ : 2 * ((a + b) / 2) = (a + b) - ((a + b) % 2) := by
      have h₂ : (a + b) % 2 = 0 ∨ (a + b) % 2 = 1 := by
        omega
      rcases h₂ with (h₂ | h₂)
      · -- Case: (a + b) % 2 = 0
        have h₃ : 2 ∣ (a + b) := by
          omega
        have h₄ : 2 * ((a + b) / 2) = a + b := by
          have h₅ := Int.emod_add_ediv (a + b) 2
          omega
        omega
      · -- Case: (a + b) % 2 = 1
        have h₃ : (a + b) % 2 = 1 := by omega
        have h₄ : 2 * ((a + b) / 2) = a + b - 1 := by
          have h₅ := Int.emod_add_ediv (a + b) 2
          omega
        omega
    exact h₁
  simpa [ComputeAvg, ComputeAvg_precond, ComputeAvg_postcond] using h_main
  -- !benchmark @end proof
