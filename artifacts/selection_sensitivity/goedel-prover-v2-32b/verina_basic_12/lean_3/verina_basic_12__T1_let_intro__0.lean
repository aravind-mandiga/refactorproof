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
  have h₁ : cubeSurfaceArea (size) h_precond = 6 * size * size := by
    simp [cubeSurfaceArea]
    <;>
    simp_all [cubeSurfaceArea_precond]
    <;>
    ring_nf
    <;>
    rfl

  have h₂ : cubeSurfaceArea (size) h_precond - 6 * size * size = 0 := by
    rw [h₁]
    <;>
    simp [Nat.sub_self]

  have h₃ : 6 * size * size - cubeSurfaceArea (size) h_precond = 0 := by
    rw [h₁]
    <;>
    simp [Nat.sub_self]

  have h_main : cubeSurfaceArea_postcond (size) (cubeSurfaceArea (size) h_precond) h_precond := by
    dsimp [cubeSurfaceArea_postcond]
    constructor <;>
    (try simp_all) <;>
    (try ring_nf at *) <;>
    (try omega)
    <;>
    (try linarith)
    <;>
    (try nlinarith)
    <;>
    (try
      {
        simp_all [cubeSurfaceArea, cubeSurfaceArea_precond]
        <;>
        ring_nf at *
        <;>
        omega
      })
    <;>
    (try
      {
        simp_all [cubeSurfaceArea, cubeSurfaceArea_precond]
        <;>
        ring_nf at *
        <;>
        linarith
      })

  exact h_main
  -- !benchmark @end proof
