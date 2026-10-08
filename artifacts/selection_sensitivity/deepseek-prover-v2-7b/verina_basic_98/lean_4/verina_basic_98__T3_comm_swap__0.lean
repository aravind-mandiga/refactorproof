-- !benchmark @start import type=solution

import Aesop
import Mathlib
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
  3 * x
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
  have h1 : (Triple (x) h_precond) / 3 = x := by
    have h1 : Triple (x) h_precond = x * 3 := rfl
    rw [h1]
    -- We need to show that (x * 3) / 3 = x
    -- Since x * 3 is divisible by 3, (x * 3) / 3 * 3 = x * 3
    -- Simplifying, we get (x * 3) / 3 = x
    norm_num [Int.mul_emod, Int.emod_eq_of_lt]
    <;>
    (try omega) <;>
    (try
      {
        have h2 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
        rcases h2 with (h2 | h2 | h2) <;> simp [h2, Int.mul_emod, Int.add_emod, Int.emod_emod] <;>
          ring_nf at * <;> omega
      }) <;>
    (try
      {
        have h2 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
        rcases h2 with (h2 | h2 | h2) <;> simp [h2, Int.mul_emod, Int.add_emod, Int.emod_emod] <;>
          ring_nf at * <;> omega
      }) <;>
    (try omega) <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        aesop
      })

  have h2 : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    have h2 : Triple (x) h_precond = x * 3 := rfl
    rw [h2] at *
    <;>
    ring_nf at * <;>
    norm_num at * <;>
    (try omega) <;>
    (try
      {
        have h3 : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
        rcases h3 with (h3 | h3 | h3) <;> simp [h3, Int.mul_emod, Int.add_emod, Int.emod_emod] <;>
          ring_nf at * <;> omega
      }) <;>
    (try
      {
        omega
      })
    <;>
    aesop

  exact ⟨h1, h2⟩
  -- !benchmark @end proof
