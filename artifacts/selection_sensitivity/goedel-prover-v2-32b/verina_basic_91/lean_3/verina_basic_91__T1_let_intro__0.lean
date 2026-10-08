-- !benchmark @start import type=solution

import Aesop
import Mathlib.Tactic
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
  have h_swap_eq : Swap X Y h_precond = (Y, X) := by
    dsimp [Swap]
    <;> simp [Prod.mk.injEq]
    <;> aesop

  have h_main : Swap_postcond X Y (Swap X Y h_precond) h_precond := by
    rw [h_swap_eq]
    simp [Swap_postcond]
    <;>
    (try decide) <;>
    (try
      {
        intro h
        constructor <;>
        (try { intro h₁; apply h; linarith }) <;>
        (try { intro h₁; apply h; linarith })
      }) <;>
    (try
      {
        intro h
        constructor <;>
        (try { intro h₁; apply h; linarith }) <;>
        (try { intro h₁; apply h; linarith })
      }) <;>
    (try
      {
        intro h
        constructor <;>
        (try { intro h₁; apply h; linarith }) <;>
        (try { intro h₁; apply h; linarith })
      })

  exact h_main
  -- !benchmark @end proof
