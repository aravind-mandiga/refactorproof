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
  have h₁ : (SwapSimultaneous (X) (Y) h_precond).1 = Y := by
    simp [SwapSimultaneous, Prod.fst]
    <;> aesop

  have h₂ : (SwapSimultaneous (X) (Y) h_precond).2 = X := by
    simp [SwapSimultaneous, Prod.snd]
    <;> aesop

  have h₃ : X ≠ Y → (SwapSimultaneous (X) (Y) h_precond).1 ≠ X ∧ (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y := by
    intro h_ne
    have h₄ : (SwapSimultaneous (X) (Y) h_precond).1 ≠ X := by
      intro h
      apply h_ne
      simp_all [SwapSimultaneous, Prod.fst]
      <;> aesop
    have h₅ : (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y := by
      intro h
      apply h_ne
      simp_all [SwapSimultaneous, Prod.snd]
      <;> aesop
    exact ⟨h₄, h₅⟩

  exact ⟨h₁, h₂, h₃⟩
  -- !benchmark @end proof
