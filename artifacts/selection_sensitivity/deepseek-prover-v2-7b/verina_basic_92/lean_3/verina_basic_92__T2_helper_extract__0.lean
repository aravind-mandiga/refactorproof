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
  have h1 : SwapArithmetic X Y h_precond = (Y, X) := by
    dsimp [SwapArithmetic]
    <;> simp [h_precond]
    <;> aesop

  have h2 : (SwapArithmetic X Y h_precond).1 = Y := by
    simp_all [Prod.fst]

  have h3 : (SwapArithmetic X Y h_precond).2 = X := by
    simp_all [Prod.snd]

  have h4 : X ≠ Y → ((SwapArithmetic X Y h_precond).1 ≠ X ∧ (SwapArithmetic X Y h_precond).2 ≠ Y) := by
    intro h_xy
    simp_all [h1, h2, h3]
    <;>
    (try aesop) <;>
    (try
      {
        intro h
        aesop
      }) <;>
    (try
      {
        simp_all
        <;> omega
      }) <;>
    (try
      {
        cases h_xy
        <;> aesop
      }) <;>
    (try
      {
        aesop
      })
    <;>
    aesop

  constructor
  · -- Prove (SwapArithmetic X Y h_precond).1 = Y
    simp_all [h1, h2]
  · constructor
    · -- Prove (SwapArithmetic X Y h_precond).2 = X
      simp_all [h1, h3]
    · -- Prove X ≠ Y → ((SwapArithmetic X Y h_precond).1 ≠ X ∧ (SwapArithmetic X Y h_precond).2 ≠ Y)
      exact h4
  -- !benchmark @end proof
