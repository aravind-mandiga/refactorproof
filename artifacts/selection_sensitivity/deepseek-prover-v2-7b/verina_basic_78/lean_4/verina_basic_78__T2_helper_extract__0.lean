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
  have h_main : MultipleReturns (x) (y) h_precond = (x + y, x - y) := by
    simp [MultipleReturns, MultipleReturns_precond]
    <;>
    aesop

  have h_goal₁ : (MultipleReturns (x) (y) h_precond).1 = x + y := by
    rw [h_main]
    <;> simp [Prod.fst]
    <;> ring
    <;> aesop

  have h_goal₂ : (MultipleReturns (x) (y) h_precond).2 + y = x := by
    rw [h_main]
    <;> simp [Prod.snd]
    <;> ring
    <;> aesop

  simp_all [MultipleReturns_postcond]
  <;> aesop
  -- !benchmark @end proof
