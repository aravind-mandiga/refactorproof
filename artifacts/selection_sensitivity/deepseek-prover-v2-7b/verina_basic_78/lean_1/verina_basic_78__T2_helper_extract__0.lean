-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def MultipleReturns_precond (x : Int) (y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def MultipleReturns__rp_helper_39d93fc9 (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) : (Int × Int) :=
  let more := x + y
  let less := x - y
  (more, less)
-- !benchmark @end code_aux


def MultipleReturns (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) : (Int × Int) :=
  -- !benchmark @start code
  MultipleReturns__rp_helper_39d93fc9 x y h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def MultipleReturns_postcond (x : Int) (y : Int) (result: (Int × Int)) (h_precond : MultipleReturns_precond (x) (y)) :=
  -- !benchmark @start postcond
  result.1 = x + y ∧ result.2 + y = x
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem MultipleReturns_spec_satisfied (x: Int) (y: Int) (h_precond : MultipleReturns_precond (x) (y)) :
    MultipleReturns_postcond (x) (y) (MultipleReturns (x) (y) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main₁ : (MultipleReturns x y h_precond).1 = x + y := by
    simp [MultipleReturns, Prod.fst]
    <;>
    aesop
    <;>
    simp_all [MultipleReturns_precond, MultipleReturns, Prod.fst]
    <;>
    aesop

  have h_main₂ : (MultipleReturns x y h_precond).2 + y = x := by
    simp [MultipleReturns, Prod.snd]
    <;> ring
    <;> omega

  have h_main : MultipleReturns_postcond x y (MultipleReturns x y h_precond) h_precond := by
    constructor
    · -- Prove the first part of the conjunction: (x + y = x + y)
      exact h_main₁
    · -- Prove the second part of the conjunction: (x - y + y = x)
      exact h_main₂

  exact h_main
  -- !benchmark @end proof
