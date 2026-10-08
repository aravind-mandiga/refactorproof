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
  unfold SwapArithmetic SwapArithmetic_postcond
  have h_main : SwapArithmetic (X) (Y) h_precond = (Y, X) := by
    simp [SwapArithmetic, Prod.ext_iff]
    <;>
    (try omega) <;>
    (try
      {
        cases' h_precond with h₁ h₂ <;>
        simp_all [SwapArithmetic_precond] <;>
        omega
      }) <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        ring_nf
        <;>
        omega
      })
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        omega
      })

  have h_final : SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
    rw [h_main]
    simp [SwapArithmetic_postcond]
    <;>
    (try omega) <;>
    (try
      {
        cases' h_precond with h₁ h₂ <;>
        simp_all [SwapArithmetic_precond] <;>
        aesop
      }) <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        omega
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

  apply h_final
  -- !benchmark @end proof
