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
  size * 6 * size
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
      rfl
    rw [h₂]
    <;> simp [Nat.mul_assoc]
    <;> ring_nf
    <;> simp [Nat.sub_self]
    <;> norm_num

  have h₂ : 6 * size * size - (cubeSurfaceArea (size) h_precond) = 0 := by
    have h₃ : cubeSurfaceArea (size) h_precond = 6 * size * size := by
      rfl
    rw [h₃]
    <;> simp [Nat.mul_assoc]
    <;> ring_nf
    <;> simp [Nat.sub_self]
    <;> norm_num

  have h_main : cubeSurfaceArea_postcond (size) (cubeSurfaceArea (size) h_precond) h_precond := by
    constructor
    · -- Prove the first part: (cubeSurfaceArea (size) h_precond) - 6 * size * size = 0
      exact h₁
    · -- Prove the second part: 6 * size * size - (cubeSurfaceArea (size) h_precond) = 0
      exact h₂

  exact h_main
  -- !benchmark @end proof
