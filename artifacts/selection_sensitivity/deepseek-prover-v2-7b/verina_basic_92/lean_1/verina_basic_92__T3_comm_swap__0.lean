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
  have h_main : SwapArithmetic (X) (Y) h_precond = (Y, X) := by
    dsimp [SwapArithmetic, SwapArithmetic_precond]
    <;> simp [Prod.mk.injEq]
    <;>
    (try decide)
    <;>
    (try
      {
        cases X <;> cases Y <;> simp_all [Int.sub_eq_add_neg, Int.add_assoc]
        <;> omega
      })
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        aesop
      })

  have h_post_cond : SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
    rw [h_main]
    constructor <;> simp (config := { contextual := true }) [SwapArithmetic_postcond, SwapArithmetic, SwapArithmetic_precond]
    <;>
    (try
      { aesop }) <;>
    (try
      {
        by_cases h : X = Y <;> simp_all
        <;>
        aesop
      }) <;>
    (try
      {
        cases X <;> cases Y <;> simp_all [Int.sub_eq_add_neg, Int.add_assoc]
        <;> omega
      })
    <;>
    aesop

  exact h_post_cond
  -- !benchmark @end proof
