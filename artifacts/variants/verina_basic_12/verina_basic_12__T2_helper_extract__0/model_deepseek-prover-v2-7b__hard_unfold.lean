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
  unfold cubeSurfaceArea cubeSurfaceArea_postcond
  have h₁ : (cubeSurfaceArea (size) h_precond) - (6 * size * size) = 0 := by
    unfold cubeSurfaceArea
    <;> simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    <;> induction size <;> simp_all [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    <;> ring_nf at *
    <;> omega

  have h₂ : (6 * size * size) - (cubeSurfaceArea (size) h_precond) = 0 := by
    have h₃ : cubeSurfaceArea (size) h_precond = 6 * size * size := rfl
    rw [h₃]
    <;> simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    <;> induction size <;> simp_all [Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm]
    <;> ring_nf at *
    <;> omega

  have h_main : cubeSurfaceArea_postcond (size) (cubeSurfaceArea (size) h_precond) h_precond := by
    constructor
    · -- Prove (cubeSurfaceArea (size) h_precond) - (6 * size * size) = 0
      exact h₁
    · -- Prove (6 * size * size) - (cubeSurfaceArea (size) h_precond) = 0
      exact h₂

  exact h_main
  -- !benchmark @end proof
