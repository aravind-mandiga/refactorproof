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
  have h_main : Swap (X) (Y) h_precond = (Y, X) := by
    dsimp [Swap]
    <;> simp_all
    <;> aesop

  have h_result_fst : (Swap (X) (Y) h_precond).fst = Y := by
    simp_all [Prod.fst]
    <;> aesop

  have h_result_snd : (Swap (X) (Y) h_precond).snd = X := by
    simp_all [Prod.snd]
    <;> aesop

  have h_implication : (X ≠ Y → ((Swap (X) (Y) h_precond).fst ≠ X ∧ (Swap (X) (Y) h_precond).snd ≠ Y)) := by
    intro h
    have h₁ : (Swap (X) (Y) h_precond).fst = Y := h_result_fst
    have h₂ : (Swap (X) (Y) h_precond).snd = X := h_result_snd
    have h₃ : (Swap (X) (Y) h_precond).fst ≠ X := by
      -- Prove that Y ≠ X when X ≠ Y
      intro h₄
      apply h
      simp_all [Prod.fst, Prod.snd]
      <;> aesop
    have h₄ : (Swap (X) (Y) h_precond).snd ≠ Y := by
      -- Prove that X ≠ Y when X ≠ Y
      intro h₅
      apply h
      simp_all [Prod.fst, Prod.snd]
      <;> aesop
    exact ⟨h₃, h₄⟩

  constructor
  · -- Prove (Swap (X) (Y) h_precond).fst = Y
    simp_all [h_result_fst]
  constructor
  · -- Prove (Swap (X) (Y) h_precond).snd = X
    simp_all [h_result_snd]
  · -- Prove (X ≠ Y → (Swap (X) (Y) h_precond).fst ≠ X ∧ (Swap (X) (Y) h_precond).snd ≠ Y)
    simpa [h_result_fst, h_result_snd] using h_implication
  -- !benchmark @end proof
