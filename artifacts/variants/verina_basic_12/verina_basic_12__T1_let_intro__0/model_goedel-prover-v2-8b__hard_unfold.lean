-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def cubeSurfaceArea_precond (size : Nat) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def cubeSurfaceArea (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) : Nat :=
  -- !benchmark @start code
  let __rp_tmp_3e6b423e : Nat :=
    6 * size * size
  __rp_tmp_3e6b423e
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def cubeSurfaceArea_postcond (size : Nat) (result: Nat) (h_precond : cubeSurfaceArea_precond (size)) :=
  -- !benchmark @start postcond
  result - 6 * size * size = 0 ∧ 6 * size * size - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem cubeSurfaceArea_spec_satisfied (size: Nat) (h_precond : cubeSurfaceArea_precond (size)) :
    cubeSurfaceArea_postcond (size) (cubeSurfaceArea (size) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold cubeSurfaceArea cubeSurfaceArea_postcond
  have h1 : 6 * size * size - (6 * size * size) = 0 := by
    have h₁ : 6 * size * size ≥ 0 := by positivity
    have h₂ : 6 * size * size - (6 * size * size) = 0 := by
      simp [Nat.sub_self]
    exact h₂

  have h2 : 6 * size * size - (6 * size * size) = 0 := by
    have h₂ : 6 * size * size - (6 * size * size) = 0 := by
      simp [Nat.sub_self]
    exact h₂

  simp_all [cubeSurfaceArea, cubeSurfaceArea_postcond, cubeSurfaceArea_precond]
  <;> aesop
  -- !benchmark @end proof
