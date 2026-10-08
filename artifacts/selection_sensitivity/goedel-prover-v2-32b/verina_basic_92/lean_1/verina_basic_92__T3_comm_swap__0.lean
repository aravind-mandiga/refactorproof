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
  let x1 := X
  let y1 := Y
  let x2 := y1 - x1
  let y2 := y1 - x2
  let x3 := x2 + y2
  (x3, y2)
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
  have h_main : (SwapArithmetic X Y h_precond).1 = Y ∧ (SwapArithmetic X Y h_precond).2 = X := by
    dsimp only [SwapArithmetic]
    have h1 : (Y - (Y - X)) = X := by
      -- Prove that Y - (Y - X) = X using algebraic manipulation
      have h1 : Y - (Y - X) = X := by
        -- Use the property of subtraction to simplify the expression
        ring_nf
        <;> simp [Int.sub_eq_add_neg]
        <;> ring_nf
        <;> omega
      exact h1
    have h2 : (Y - (Y - X)) + (Y - X) = Y := by
      -- Prove that (Y - (Y - X)) + (Y - X) = Y using the property of subtraction
      have h2 : (Y - (Y - X)) + (Y - X) = Y := by
        -- Use the property that (a - b) + b = a
        have h3 : (Y - (Y - X)) + (Y - X) = Y := by
          -- Simplify using the fact that subtraction is addition of the negation
          ring_nf
          <;> simp [Int.sub_eq_add_neg]
          <;> ring_nf
          <;> omega
        exact h3
      exact h2
    constructor
    · -- Prove that the first element is Y
      simp_all [Prod.fst]
      <;> ring_nf at *
      <;> omega
    · -- Prove that the second element is X
      simp_all [Prod.snd]
      <;> ring_nf at *
      <;> omega

  have h_final : SwapArithmetic_postcond X Y (SwapArithmetic X Y h_precond) h_precond := by
    have h1 : (SwapArithmetic X Y h_precond).1 = Y := h_main.1
    have h2 : (SwapArithmetic X Y h_precond).2 = X := h_main.2
    have h3 : X ≠ Y → (SwapArithmetic X Y h_precond).1 ≠ X ∧ (SwapArithmetic X Y h_precond).2 ≠ Y := by
      intro h
      constructor
      · -- Prove that (SwapArithmetic X Y h_precond).1 ≠ X
        intro h4
        have h5 : (SwapArithmetic X Y h_precond).1 = Y := h_main.1
        have h6 : Y = X := by linarith
        exact h (by linarith)
      · -- Prove that (SwapArithmetic X Y h_precond).2 ≠ Y
        intro h4
        have h5 : (SwapArithmetic X Y h_precond).2 = X := h_main.2
        have h6 : X = Y := by linarith
        exact h (by linarith)
    exact ⟨h1, h2, h3⟩

  exact h_final
  -- !benchmark @end proof
