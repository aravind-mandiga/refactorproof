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
  have h_result : SwapSimultaneous X Y h_precond = (Y, X) := by
    simp [SwapSimultaneous]
    <;> aesop

  have h_main : SwapSimultaneous_postcond X Y (SwapSimultaneous X Y h_precond) h_precond := by
    rw [h_result]
    constructor
    · -- Prove (Y, X).1 = Y
      rfl
    constructor
    · -- Prove (Y, X).2 = X
      rfl
    · -- Prove the implication X ≠ Y → (Y, X).fst ≠ X ∧ (Y, X).snd ≠ Y
      intro h_ne
      constructor
      · -- Prove (Y, X).fst ≠ X
        intro h_eq
        apply h_ne
        linarith
      · -- Prove (Y, X).snd ≠ Y
        intro h_eq
        apply h_ne
        linarith

  exact h_main
  -- !benchmark @end proof
