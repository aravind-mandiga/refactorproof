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
  have h_main : SwapArithmetic X Y h_precond = (Y, X) := by
    dsimp [SwapArithmetic, SwapArithmetic__rp_helper_2265221a]
    <;>
    (try ring_nf) <;>
    (try simp_all [Prod.ext_iff]) <;>
    (try norm_num) <;>
    (try ring_nf at *) <;>
    (try omega)
    <;>
    (try
      {
        norm_num at *
        <;>
        ring_nf at *
        <;>
        omega
      })

  have h1 : (SwapArithmetic X Y h_precond).1 = Y := by
    rw [h_main]
    <;> simp [Prod.fst]

  have h2 : (SwapArithmetic X Y h_precond).2 = X := by
    rw [h_main]
    <;> simp [Prod.snd]

  have h3 : X ≠ Y → (SwapArithmetic X Y h_precond).1 ≠ X ∧ (SwapArithmetic X Y h_precond).2 ≠ Y := by
    intro h_ne
    have h4 : (SwapArithmetic X Y h_precond).1 = Y := h1
    have h5 : (SwapArithmetic X Y h_precond).2 = X := h2
    constructor
    · -- Prove (SwapArithmetic X Y h_precond).1 ≠ X
      intro h_contra
      apply h_ne
      linarith
    · -- Prove (SwapArithmetic X Y h_precond).2 ≠ Y
      intro h_contra
      apply h_ne
      linarith

  constructor
  · exact h1
  constructor
  · exact h2
  · exact h3
  -- !benchmark @end proof
