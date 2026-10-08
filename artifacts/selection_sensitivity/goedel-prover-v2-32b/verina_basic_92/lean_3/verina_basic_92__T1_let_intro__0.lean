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

-- !benchmark @end code_aux


def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  -- !benchmark @start code
  let __rp_tmp_5e3d4b6e : (Int × Int) :=
    let x1 := X
    let y1 := Y
    let x2 := y1 - x1
    let y2 := y1 - x2
    let x3 := y2 + x2
    (x3, y2)
  __rp_tmp_5e3d4b6e
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
  have h_main : SwapArithmetic X Y h_precond = (Y, X) := by
    dsimp [SwapArithmetic]
    have h₁ : (Y - (Y - X) + (Y - X), Y - (Y - X)) = (Y, X) := by
      have h₂ : Y - (Y - X) = X := by
        -- Prove that Y - (Y - X) = X using integer arithmetic properties
        have h₃ : Y - (Y - X) = X := by
          ring_nf
          <;> simp [sub_eq_add_neg]
          <;> ring_nf
          <;> omega
        exact h₃
      rw [h₂]
      <;> simp [Prod.ext_iff]
      <;> ring_nf
      <;> simp [sub_eq_add_neg]
      <;> ring_nf
      <;> omega
    simp_all [Prod.ext_iff]
    <;> ring_nf at *
    <;> simp_all [sub_eq_add_neg]
    <;> ring_nf at *
    <;> omega

  have h_result : SwapArithmetic_postcond X Y (SwapArithmetic X Y h_precond) h_precond := by
    rw [h_main]
    constructor
    · -- Prove that (Y, X).1 = Y
      rfl
    constructor
    · -- Prove that (Y, X).2 = X
      rfl
    · -- Prove that X ≠ Y → (Y ≠ X ∧ X ≠ Y)
      intro h_ne
      constructor
      · -- Prove Y ≠ X
        intro h_eq
        apply h_ne
        linarith
      · -- Prove X ≠ Y
        intro h_eq
        apply h_ne
        linarith

  exact h_result
  -- !benchmark @end proof
