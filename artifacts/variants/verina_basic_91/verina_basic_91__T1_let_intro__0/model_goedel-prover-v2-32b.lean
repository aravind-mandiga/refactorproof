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

-- !benchmark @end code_aux


def Swap (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) : Int × Int :=
  -- !benchmark @start code
  let __rp_tmp_ed7c8607 : Int × Int :=
    let x := X
    let y := Y
    let tmp := x
    let x := y
    let y := tmp
    (x, y)
  __rp_tmp_ed7c8607
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
  have h_swap : Swap X Y h_precond = (Y, X) := by
    dsimp [Swap]
    <;> simp_all [Prod.mk.injEq]
    <;> norm_num
    <;> aesop

  have h_fst : (Swap X Y h_precond).fst = Y := by
    rw [h_swap]
    <;> simp [Prod.fst]

  have h_snd : (Swap X Y h_precond).snd = X := by
    rw [h_swap]
    <;> simp [Prod.snd]

  have h_main : Swap_postcond X Y (Swap X Y h_precond) h_precond := by
    dsimp [Swap_postcond] at *
    constructor
    · -- Prove (Swap X Y h_precond).fst = Y
      exact h_fst
    constructor
    · -- Prove (Swap X Y h_precond).snd = X
      exact h_snd
    · -- Prove X ≠ Y → (Swap X Y h_precond).fst ≠ X ∧ (Swap X Y h_precond).snd ≠ Y
      intro h_ne
      constructor
      · -- Prove (Swap X Y h_precond).fst ≠ X
        have h₁ : (Swap X Y h_precond).fst = Y := h_fst
        have h₂ : Y ≠ X := by
          intro h_eq
          apply h_ne
          linarith
        intro h_contra
        apply h₂
        linarith
      · -- Prove (Swap X Y h_precond).snd ≠ Y
        have h₁ : (Swap X Y h_precond).snd = X := h_snd
        intro h_contra
        apply h_ne
        linarith

  exact h_main
  -- !benchmark @end proof
