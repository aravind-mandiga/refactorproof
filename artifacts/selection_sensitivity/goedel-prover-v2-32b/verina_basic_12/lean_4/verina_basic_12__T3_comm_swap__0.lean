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
  have h₁ : cubeSurfaceArea size h_precond = 6 * size * size := by
    rfl

  have h₂ : (cubeSurfaceArea size h_precond) - 6 * size * size = 0 := by
    rw [h₁]
    <;> simp [Nat.sub_self]
    <;> ring_nf
    <;> simp [Nat.sub_self]

  have h₃ : 6 * size * size - (cubeSurfaceArea size h_precond) = 0 := by
    rw [h₁]
    <;> simp [Nat.sub_self]
    <;> ring_nf
    <;> simp [Nat.sub_self]

  have h₄ : cubeSurfaceArea_postcond (size) (cubeSurfaceArea (size) h_precond) h_precond := by
    constructor <;>
    (try simp_all [cubeSurfaceArea_postcond, cubeSurfaceArea_precond]) <;>
    (try ring_nf at *) <;>
    (try simp_all [Nat.sub_self]) <;>
    (try omega)
    <;>
    (try
      {
        cases size <;>
        simp_all [cubeSurfaceArea, cubeSurfaceArea_precond, cubeSurfaceArea_postcond, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
        <;>
        ring_nf at * <;>
        simp_all [Nat.sub_self]
        <;>
        omega
      })

  exact h₄
  -- !benchmark @end proof
