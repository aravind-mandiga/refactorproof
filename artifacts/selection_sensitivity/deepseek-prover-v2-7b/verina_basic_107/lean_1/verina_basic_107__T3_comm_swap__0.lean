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
  have h_main : 2 * (ComputeAvg (a) (b) h_precond : ℤ) = a + b - ((a + b) % 2) := by
    have h₁ : ComputeAvg (a) (b) h_precond = (a + b) / 2 := by rfl
    rw [h₁]
    have h₂ : 2 * ((a + b) / 2 : ℤ) = a + b - ((a + b) % 2) := by
      have h₃ := Int.emod_add_ediv (a + b) 2
      have h₄ : (a + b) % 2 = 0 ∨ (a + b) % 2 = 1 := by omega
      rcases h₄ with (h₄ | h₄) <;> simp [h₄, Int.emod_emod, Int.ediv_eq_zero_of_lt] at h₃ ⊢ <;>
        (try omega) <;>
        (try
          {
            omega
          }) <;>
        (try
          {
            ring_nf at h₃ ⊢ <;> omega
          }) <;>
        (try
          {
            omega
          }) <;>
        (try
          {
            omega
          })
      <;>
      (try omega) <;>
      (try
        {
          omega
        }) <;>
      (try
        {
          omega
        }) <;>
      (try
        {
          omega
        })
    exact h₂

  simp_all [ComputeAvg_postcond, ComputeAvg]
  <;> omega
  -- !benchmark @end proof
