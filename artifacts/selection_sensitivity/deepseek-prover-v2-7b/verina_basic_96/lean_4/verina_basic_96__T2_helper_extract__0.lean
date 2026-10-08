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
  have h_main : SwapSimultaneous (X) (Y) h_precond = (Y, X) := by
    simp [SwapSimultaneous]
    <;> rfl

  have h_first : (SwapSimultaneous (X) (Y) h_precond).1 = Y := by
    rw [h_main]
    <;> simp [Prod.fst]
    <;> rfl

  have h_second : (SwapSimultaneous (X) (Y) h_precond).2 = X := by
    rw [h_main]
    <;> simp [Prod.snd]
    <;> rfl

  have h_third : X ≠ Y → (SwapSimultaneous (X) (Y) h_precond).1 ≠ X ∧ (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y := by
    intro h_ne
    constructor
    · -- Prove that (SwapSimultaneous (X) (Y) h_precond).1 ≠ X
      rw [h_main]
      -- Since h_main states that SwapSimultaneous (X) (Y) h_precond = (Y, X), we need to show that Y ≠ X
      intro h
      -- Assume for contradiction that Y = X
      have h1 : Y = X := by simpa using h
      -- This implies X = Y, which contradicts the assumption X ≠ Y
      exact h_ne (by linarith)
    · -- Prove that (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y
      rw [h_main]
      -- Since h_main states that SwapSimultaneous (X) (Y) h_precond = (Y, X), we need to show that X ≠ Y
      intro h
      -- Assume for contradiction that X = Y
      have h1 : X = Y := by simpa using h
      -- This contradicts the assumption X ≠ Y
      exact h_ne (by linarith)

  constructor
  · -- Prove that (SwapSimultaneous (X) (Y) h_precond).1 = Y
    exact h_first
  · constructor
    · -- Prove that (SwapSimultaneous (X) (Y) h_precond).2 = X
      exact h_second
    · -- Prove that if X ≠ Y, then (SwapSimultaneous (X) (Y) h_precond).1 ≠ X and (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y
      intro h_ne
      exact h_third h_ne
  -- !benchmark @end proof
