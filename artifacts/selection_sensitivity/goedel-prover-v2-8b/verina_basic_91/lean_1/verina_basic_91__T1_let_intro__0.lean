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
  have h₁ : (Swap (X) (Y) h_precond).fst = Y := by
    simp [Swap, Prod.fst]
    <;> rfl

  have h₂ : (Swap (X) (Y) h_precond).snd = X := by
    simp [Swap, Prod.snd]
    <;> rfl

  have h₃ : (X ≠ Y → (Swap (X) (Y) h_precond).fst ≠ X ∧ (Swap (X) (Y) h_precond).snd ≠ Y) := by
    intro h
    have h₄ : (Swap (X) (Y) h_precond).fst ≠ X := by
      have h₅ : (Swap (X) (Y) h_precond).fst = Y := h₁
      have h₆ : Y ≠ X := by
        intro h₇
        apply h
        linarith
      intro h₇
      apply h₆
      linarith
    have h₅ : (Swap (X) (Y) h_precond).snd ≠ Y := by
      have h₆ : (Swap (X) (Y) h_precond).snd = X := h₂
      have h₇ : X ≠ Y := by
        intro h₈
        apply h
        linarith
      intro h₈
      apply h₇
      linarith
    exact ⟨h₄, h₅⟩

  have h₄ : Swap_postcond (X) (Y) (Swap (X) (Y) h_precond) h_precond := by
    refine' ⟨h₁, h₂, _⟩
    exact h₃

  exact h₄
  -- !benchmark @end proof
