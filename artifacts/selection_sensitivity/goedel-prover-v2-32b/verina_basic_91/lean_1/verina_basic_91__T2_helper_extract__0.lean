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
  have h_main : Swap_postcond (X) (Y) (Swap (X) (Y) h_precond) h_precond := by
    dsimp [Swap, Swap_precond, Swap_postcond]
    <;>
    (try constructor) <;>
    (try simp_all) <;>
    (try
      {
        intro h_ne
        constructor <;>
        (try intro h_eq) <;>
        (try apply h_ne) <;>
        (try simp_all [h_eq]) <;>
        (try { contradiction }) <;>
        (try { linarith })
      }) <;>
    (try
      {
        intro h_eq
        simp_all [h_eq]
        <;>
        (try { contradiction })
      }) <;>
    (try { aesop })
    <;>
    (try { tauto })
  exact h_main
  -- !benchmark @end proof
