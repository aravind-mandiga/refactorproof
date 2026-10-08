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

private def Swap__rp_helper_6bee5f12 (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) : Int × Int :=
  let x := X
  let y := Y
  let tmp := x
  let x := y
  let y := tmp
  (x, y)
-- !benchmark @end code_aux


def Swap (X : Int) (Y : Int) (h_precond : Swap_precond (X) (Y)) : Int × Int :=
  -- !benchmark @start code
  Swap__rp_helper_6bee5f12 X Y h_precond
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
  unfold Swap Swap_postcond
  have h_main : Swap (X) (Y) h_precond = (Y, X) := by
    simp [Swap, Swap_precond]
    <;> aesop

  have h_final : Swap_postcond (X) (Y) (Swap (X) (Y) h_precond) h_precond := by
    rw [h_main]
    simp [Swap_postcond, Swap_precond]
    <;>
    (try aesop) <;>
    (try
      {
        intro h
        cases h <;> simp_all
      }) <;>
    (try
      {
        cases Int.emod_two_eq_zero_or_one X <;> cases Int.emod_two_eq_zero_or_one Y <;>
          (try omega) <;> (try aesop) <;> (try simp_all) <;> (try omega)
      }) <;>
    (try
      {
        aesop
      }) <;>
    (try
      {
        omega
      }) <;>
    (try
      {
        simp_all [Swap_precond]
        <;> aesop
      })
    <;> aesop

  exact h_final
  -- !benchmark @end proof
