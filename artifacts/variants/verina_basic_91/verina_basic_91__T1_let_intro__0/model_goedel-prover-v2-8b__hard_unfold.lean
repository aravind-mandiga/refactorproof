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
  unfold Swap Swap_postcond
  have h_main : Swap_postcond (X) (Y) (Swap (X) (Y) h_precond) h_precond := by
    dsimp [Swap, Swap_postcond] at *
    <;>
    (try aesop) <;>
    (try
      {
        by_cases h : X = Y <;> simp_all [Prod.fst, Prod.snd] <;>
        (try omega) <;>
        (try aesop)
      }) <;>
    (try
      {
        simp_all [Prod.fst, Prod.snd] <;>
        aesop
      }) <;>
    (try
      {
        by_cases h : X = Y <;> simp_all [Prod.fst, Prod.snd] <;>
        (try omega) <;>
        (try aesop)
      }) <;>
    (try
      {
        aesop
      }) <;>
    (try
      {
        simp_all [Prod.fst, Prod.snd] <;>
        aesop
      }) <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        simp_all [Prod.fst, Prod.snd] <;>
        aesop
      })
  exact h_main
  -- !benchmark @end proof
