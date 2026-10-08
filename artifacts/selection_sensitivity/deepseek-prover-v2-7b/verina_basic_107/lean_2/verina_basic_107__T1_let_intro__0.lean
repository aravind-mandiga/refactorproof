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
  let __rp_tmp_7bc347ba : Int :=
    (a + b) / 2
  __rp_tmp_7bc347ba
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
  have h_main : 2 * ComputeAvg (a) (b) h_precond = a + b - ((a + b) % 2) := by
    have h₁ : ComputeAvg (a) (b) h_precond = (a + b) / 2 := by
      rfl
    rw [h₁]
    -- We need to prove that 2 * ((a + b) / 2) = a + b - ((a + b) % 2)
    have h₂ : a + b = 2 * ((a + b) / 2) + (a + b) % 2 := by
      have h₃ := Int.emod_add_ediv (a + b) 2
      omega
    have h₃ : 2 * ((a + b) / 2) = a + b - ((a + b) % 2) := by
      omega
    omega

  unfold ComputeAvg_postcond at *
  simp_all [ComputeAvg]
  <;>
  (try omega) <;>
  (try
    {
      have h₁ := h_main
      omega
    }) <;>
  (try
    {
      -- Use the fact that the average is an integer to simplify the modulus
      have h₁ := h_main
      omega
    })
  <;>
  (try
    {
      -- Use the fact that the average is an integer to simplify the modulus
      omega
    })
  -- !benchmark @end proof
