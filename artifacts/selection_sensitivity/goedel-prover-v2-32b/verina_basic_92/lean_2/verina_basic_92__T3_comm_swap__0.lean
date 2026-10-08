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
  have h_main : SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
    dsimp [SwapArithmetic, SwapArithmetic_postcond] at *
    -- Simplify the expressions for x2, y2, x3
    have h₁ : (Y - X : ℤ) = Y - X := by rfl
    have h₂ : (Y - (Y - X) : ℤ) = X := by
      ring
    have h₃ : (X + (Y - X) : ℤ) = Y := by
      ring
    -- Simplify the tuple (x3, y2) to (Y, X)
    simp [h₁, h₂, h₃]
    <;>
    (try
      {
        intros h
        -- Prove the implication X ≠ Y → Y ≠ X ∧ X ≠ Y
        constructor <;>
        (try { intro h₄ }) <;>
        (try { simp_all }) <;>
        (try { omega }) <;>
        (try { linarith })
      }) <;>
    (try
      {
        -- Trivial cases for the first two conditions
        simp_all
      }) <;>
    (try
      {
        -- Use arithmetic to verify the conditions
        ring_nf at *
        <;>
        omega
      })
    <;>
    (try
      {
        -- Use linear arithmetic to verify the conditions
        linarith
      })
  exact h_main
  -- !benchmark @end proof
