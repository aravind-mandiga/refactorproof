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
  have h₁ : 2 * ((a + b) / 2) = (a + b) - ((a + b) % 2) := by
    have h₂ : (a + b) = 2 * ((a + b) / 2) + ((a + b) % 2) := by
      have h₃ : (a + b) % 2 = (a + b) - 2 * ((a + b) / 2) := by
        have h₄ : (a + b) % 2 = (a + b) - 2 * ((a + b) / 2) := by
          have h₅ : (a + b) % 2 = (a + b) - 2 * ((a + b) / 2) := by
            omega
          exact h₅
        exact h₄
      omega
    omega

  have h₂ : ComputeAvg_postcond (a) (b) (ComputeAvg (a) (b) h_precond) h_precond := by
    dsimp [ComputeAvg_postcond, ComputeAvg] at *
    <;>
    (try omega) <;>
    (try ring_nf at *) <;>
    (try omega) <;>
    (try linarith)
    <;>
    (try
      {
        have h₃ : 2 * ((a + b) / 2) = (a + b) - ((a + b) % 2) := h₁
        omega
      })

  exact h₂
  -- !benchmark @end proof
