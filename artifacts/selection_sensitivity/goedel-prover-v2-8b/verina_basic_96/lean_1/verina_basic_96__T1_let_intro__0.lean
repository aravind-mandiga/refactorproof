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

-- !benchmark @end code_aux


def SwapSimultaneous (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) : Int × Int :=
  -- !benchmark @start code
  let __rp_tmp_582430c5 : Int × Int :=
    (Y, X)
  __rp_tmp_582430c5
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
    <;> rfl

  have h₂ : (SwapSimultaneous (X) (Y) h_precond).2 = X := by
    simp [SwapSimultaneous, Prod.snd]
    <;> rfl

  have h₃ : X ≠ Y → (SwapSimultaneous (X) (Y) h_precond).1 ≠ X ∧ (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y := by
    intro h
    have h₄ : (SwapSimultaneous (X) (Y) h_precond).1 = Y := h₁
    have h₅ : (SwapSimultaneous (X) (Y) h_precond).2 = X := h₂
    have h₆ : Y ≠ X := by
      intro h₆
      apply h
      <;> simp_all
    have h₇ : X ≠ Y := h
    constructor
    · -- Prove (SwapSimultaneous (X) (Y) h_precond).1 ≠ X
      rw [h₄]
      <;> intro h₈ <;> apply h₆ <;> simp_all
    · -- Prove (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y
      rw [h₅]
      <;> intro h₈ <;> apply h₇ <;> simp_all

  have h₄ : SwapSimultaneous_postcond (X) (Y) (SwapSimultaneous (X) (Y) h_precond) h_precond := by
    constructor
    · -- Prove the first part of the conjunction: result.1 = Y
      exact h₁
    · constructor
      · -- Prove the second part of the conjunction: result.2 = X
        exact h₂
      · -- Prove the third part of the conjunction: X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y
        intro h_ne
        exact h₃ h_ne

  exact h₄
  -- !benchmark @end proof
