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

private def ComputeAvg__rp_helper_860051f2 (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  (a + b) / 2
-- !benchmark @end code_aux


def ComputeAvg (a : Int) (b : Int) (h_precond : ComputeAvg_precond (a) (b)) : Int :=
  -- !benchmark @start code
  ComputeAvg__rp_helper_860051f2 a b h_precond
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
    have h₁ : (a + b) = 2 * ((a + b) / 2) + (a + b) % 2 := by
      have h₂ := Int.emod_add_ediv (a + b) 2
      -- Using the property that for any integer n and non-zero integer d, n = d * (n / d) + (n % d)
      -- Here, n = a + b and d = 2
      linarith
    -- Rearranging the equation to get 2 * ((a + b) / 2) = (a + b) - ((a + b) % 2)
    have h₂ : 2 * ((a + b) / 2) = (a + b) - (a + b) % 2 := by
      linarith
    exact h₂

  have h_final : ComputeAvg_postcond (a) (b) (ComputeAvg (a) (b) h_precond) h_precond := by
    simp only [ComputeAvg_postcond, ComputeAvg] at *
    -- Simplify the goal using the definition of ComputeAvg and ComputeAvg_postcond
    -- Now the goal is to prove 2 * ((a + b) / 2) = a + b - (a + b) % 2
    -- This is exactly the statement of h_main
    <;>
    (try omega) <;>
    (try linarith) <;>
    (try ring_nf at h_main ⊢) <;>
    (try omega) <;>
    (try linarith)
    <;>
    (try
      {
        -- Use the fact that h_main already proves the required equality
        have h₃ : 2 * ((a + b) / 2) = (a + b) - (a + b) % 2 := h_main
        linarith
      })
    <;>
    (try
      {
        -- If the above steps don't work, use the fact that h_main is already proven
        have h₃ : 2 * ((a + b) / 2) = (a + b) - (a + b) % 2 := h_main
        linarith
      })

  exact h_final
  -- !benchmark @end proof
