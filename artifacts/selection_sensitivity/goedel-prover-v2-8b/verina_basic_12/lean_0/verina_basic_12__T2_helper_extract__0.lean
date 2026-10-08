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

private def cubeSurfaceArea__rp_helper_67e54167 (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) : Nat :=
  6 * size * size
-- !benchmark @end code_aux


def cubeSurfaceArea (size : Nat) (h_precond : cubeSurfaceArea_precond (size)) : Nat :=
  -- !benchmark @start code
  cubeSurfaceArea__rp_helper_67e54167 size h_precond
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
  have h₁ : (cubeSurfaceArea (size) h_precond) - 6 * size * size = 0 := by
    have h₂ : cubeSurfaceArea (size) h_precond = 6 * size * size := by
      simp [cubeSurfaceArea, cubeSurfaceArea_precond]
    rw [h₂]
    <;> simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.mul_assoc]
    <;> ring_nf at *
    <;> omega

  have h₂ : 6 * size * size - (cubeSurfaceArea (size) h_precond) = 0 := by
    have h₃ : cubeSurfaceArea (size) h_precond = 6 * size * size := by
      simp [cubeSurfaceArea, cubeSurfaceArea_precond]
    rw [h₃]
    <;> simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.mul_assoc]
    <;> ring_nf at *
    <;> omega

  have h₃ : cubeSurfaceArea_postcond (size) (cubeSurfaceArea (size) h_precond) h_precond := by
    constructor <;> simp_all [cubeSurfaceArea_postcond]
    <;> omega

  exact h₃
  -- !benchmark @end proof
