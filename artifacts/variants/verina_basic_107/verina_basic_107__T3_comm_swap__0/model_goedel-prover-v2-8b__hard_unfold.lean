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
  unfold ComputeAvg ComputeAvg_postcond
  have h_main : 2 * ((a + b) / 2 : ℤ) = a + b - ((a + b) % 2 : ℤ) := by
    have h₁ : a + b = 2 * ((a + b) / 2) + ((a + b) % 2) := by
      have h₂ := Int.emod_add_ediv (a + b) 2
      linarith
    have h₂ : 2 * ((a + b) / 2 : ℤ) = a + b - ((a + b) % 2 : ℤ) := by
      linarith
    exact h₂

  simp_all [ComputeAvg, ComputeAvg_precond, ComputeAvg_postcond]
  <;>
  (try omega) <;>
  (try linarith) <;>
  (try
    {
      omega
    }) <;>
  (try
    {
      simp_all [Int.mul_emod, Int.add_emod, Int.sub_emod]
      <;> omega
    }) <;>
  (try
    {
      ring_nf at *
      <;> omega
    }) <;>
  (try
    {
      omega
    })
  <;>
  omega
  -- !benchmark @end proof
