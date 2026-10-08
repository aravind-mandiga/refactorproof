-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Swap_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def Swap__rp_helper_6bee5f12 (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) : Int × Int :=
  let x := X
  let y := Y
  let tmp := x
  let x := y
  let y := tmp
  (x, y)
-- !benchmark @end code_aux


def Swap (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) : Int × Int :=
  -- !benchmark @start code
  Swap__rp_helper_6bee5f12 X Y h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Swap_postcond (X : Int) (Y : Int) (result: Int × Int) (h_precond : Swap_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.fst = Y ∧ result.snd = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Swap_spec_satisfied (X: Int) (Y: Int) (h_precond : Swap_precond (X) (Y)) :
    Swap_postcond (X) (Y) (Swap (X) (Y) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_fst : (Swap (X) (Y) h_precond).fst = Y := by
    simp [Swap, ite_eq_left_iff]
    <;> aesop

  have h_snd : (Swap (X) (Y) h_precond).snd = X := by
    simp [Swap, ite_eq_left_iff]
    <;> aesop

  have h_imp : X ≠ Y → ((Swap (X) (Y) h_precond).fst ≠ X ∧ (Swap (X) (Y) h_precond).snd ≠ Y) := by
    intro h
    constructor
    · -- Prove Y ≠ X
      intro h1
      have h2 : (Swap (X) (Y) h_precond).fst = Y := h_fst
      rw [h2] at h1
      apply h
      linarith
    · -- Prove X ≠ Y
      intro h1
      have h2 : (Swap (X) (Y) h_precond).snd = X := h_snd
      rw [h2] at h1
      apply h
      linarith

  constructor
  · -- Prove the first condition: (Swap (X) (Y) h_precond).fst = Y
    exact h_fst
  constructor
  · -- Prove the second condition: (Swap (X) (Y) h_precond).snd = X
    exact h_snd
  · -- Prove the third condition: X ≠ Y → ((Swap (X) (Y) h_precond).fst ≠ X ∧ (Swap (X) (Y) h_precond).snd ≠ Y)
    intro h
    apply h_imp
    exact h
  -- !benchmark @end proof
