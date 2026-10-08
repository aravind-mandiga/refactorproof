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
  have h_main : (SwapSimultaneous (X) (Y) h_precond).1 = Y ∧ (SwapSimultaneous (X) (Y) h_precond).2 = X := by
    simp [SwapSimultaneous]
    <;>
    (try decide) <;>
    (try ring_nf) <;>
    (try norm_num) <;>
    (try aesop)
    <;>
    simp_all [SwapSimultaneous_precond]
    <;>
    aesop

  have h_implication : X ≠ Y → (SwapSimultaneous (X) (Y) h_precond).fst ≠ X ∧ (SwapSimultaneous (X) (Y) h_precond).snd ≠ Y := by
    intro h_ne
    have h1 : (SwapSimultaneous (X) (Y) h_precond).fst = Y := by
      simp [SwapSimultaneous]
      <;> simp_all [SwapSimultaneous_precond]
    have h2 : (SwapSimultaneous (X) (Y) h_precond).snd = X := by
      simp [SwapSimultaneous]
      <;> simp_all [SwapSimultaneous_precond]
    have h3 : Y ≠ X := by
      intro h_eq
      apply h_ne
      linarith
    have h4 : (SwapSimultaneous (X) (Y) h_precond).fst ≠ X := by
      rw [h1]
      intro h_eq
      apply h3
      linarith
    have h5 : (SwapSimultaneous (X) (Y) h_precond).snd ≠ Y := by
      rw [h2]
      intro h_eq
      apply h_ne
      linarith
    exact ⟨h4, h5⟩

  have h_final : SwapSimultaneous_postcond (X) (Y) (SwapSimultaneous (X) (Y) h_precond) h_precond := by
    have h₁ : (SwapSimultaneous (X) (Y) h_precond).1 = Y := h_main.1
    have h₂ : (SwapSimultaneous (X) (Y) h_precond).2 = X := h_main.2
    have h₃ : X ≠ Y → (SwapSimultaneous (X) (Y) h_precond).fst ≠ X ∧ (SwapSimultaneous (X) (Y) h_precond).snd ≠ Y := h_implication
    constructor
    · -- Prove result.1 = Y
      exact h₁
    constructor
    · -- Prove result.2 = X
      exact h₂
    · -- Prove X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y
      intro h_ne
      exact h₃ h_ne

  exact h_final
  -- !benchmark @end proof
