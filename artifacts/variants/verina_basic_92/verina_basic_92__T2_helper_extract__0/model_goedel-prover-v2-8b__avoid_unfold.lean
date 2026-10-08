-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SwapArithmetic_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def SwapArithmetic__rp_helper_2265221a (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  let x1 := X
  let y1 := Y
  let x2 := y1 - x1
  let y2 := y1 - x2
  let x3 := y2 + x2
  (x3, y2)
-- !benchmark @end code_aux


def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  -- !benchmark @start code
  SwapArithmetic__rp_helper_2265221a X Y h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SwapArithmetic_postcond (X : Int) (Y : Int) (result: (Int × Int)) (h_precond : SwapArithmetic_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SwapArithmetic_spec_satisfied (X: Int) (Y: Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : SwapArithmetic (X) (Y) h_precond = (Y, X) := by
    dsimp [SwapArithmetic]
    <;> ring_nf
    <;> simp [h_precond]
    <;> norm_num
    <;> ring_nf
    <;> omega

  have h1 : (SwapArithmetic (X) (Y) h_precond).1 = Y := by
    rw [h_main]
    <;> simp

  have h2 : (SwapArithmetic (X) (Y) h_precond).2 = X := by
    rw [h_main]
    <;> simp

  have h3 : X ≠ Y → (SwapArithmetic (X) (Y) h_precond).1 ≠ X ∧ (SwapArithmetic (X) (Y) h_precond).2 ≠ Y := by
    intro h_ne
    have h4 : (SwapArithmetic (X) (Y) h_precond).1 = Y := h1
    have h5 : (SwapArithmetic (X) (Y) h_precond).2 = X := h2
    have h6 : (SwapArithmetic (X) (Y) h_precond).1 ≠ X := by
      intro h7
      have h8 : Y = X := by linarith
      have h9 : X = Y := by linarith
      contradiction
    have h7 : (SwapArithmetic (X) (Y) h_precond).2 ≠ Y := by
      intro h8
      have h9 : X = Y := by linarith
      contradiction
    exact ⟨h6, h7⟩

  have h_final : SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
    constructor
    · -- Prove the first part of the conjunction: (SwapArithmetic (X) (Y) h_precond).1 = Y
      rw [h1]
    · constructor
      · -- Prove the second part of the conjunction: (SwapArithmetic (X) (Y) h_precond).2 = X
        rw [h2]
      · -- Prove the implication: X ≠ Y → (SwapArithmetic (X) (Y) h_precond).1 ≠ X ∧ (SwapArithmetic (X) (Y) h_precond).2 ≠ Y
        intro h_ne
        exact h3 h_ne

  exact h_final
  -- !benchmark @end proof
