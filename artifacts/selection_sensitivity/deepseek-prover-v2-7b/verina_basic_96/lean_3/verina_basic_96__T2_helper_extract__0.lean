-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SwapSimultaneous_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def SwapSimultaneous__rp_helper_5fb3d255 (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) : Int × Int :=
  (Y, X)
-- !benchmark @end code_aux


def SwapSimultaneous (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) : Int × Int :=
  -- !benchmark @start code
  SwapSimultaneous__rp_helper_5fb3d255 X Y h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SwapSimultaneous_postcond (X : Int) (Y : Int) (result: Int × Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SwapSimultaneous_spec_satisfied (X: Int) (Y: Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :
    SwapSimultaneous_postcond (X) (Y) (SwapSimultaneous (X) (Y) h_precond) h_precond := by
  -- !benchmark @start proof
  have h1 : SwapSimultaneous (X) (Y) h_precond = (Y, X) := by
    rfl

  have h2 : SwapSimultaneous_postcond (X) (Y) (SwapSimultaneous (X) (Y) h_precond) h_precond := by
    rw [h1]
    constructor
    · -- Prove the first part: result.1 = Y
      rfl
    constructor
    · -- Prove the second part: result.2 = X
      rfl
    · -- Prove the third part: X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y
      intro h
      simp_all [SwapSimultaneous_postcond, SwapSimultaneous, Prod.fst, Prod.snd]
      <;>
      (try contradiction) <;>
      (try aesop) <;>
      (try
        {
          simp_all [ne_eq, Prod.fst, Prod.snd]
          <;>
          (try omega)
          <;>
          (try aesop)
        }) <;>
      (try
        {
          aesop
        }) <;>
      (try
        {
          simp_all [Int.mul_eq_mul_left_iff]
          <;>
          aesop
        }) <;>
      (try
        {
          aesop
        })
      <;>
      (try
        {
          simp_all [ne_eq, Prod.fst, Prod.snd]
          <;>
          aesop
        })
      <;>
      (try
        {
          aesop
        })
      <;>
      aesop
  exact h2
  -- !benchmark @end proof
