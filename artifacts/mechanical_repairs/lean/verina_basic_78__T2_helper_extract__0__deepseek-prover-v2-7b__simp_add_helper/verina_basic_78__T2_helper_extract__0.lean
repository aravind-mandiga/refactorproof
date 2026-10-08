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
  have h1 : (MultipleReturns (x) (y) h_precond).1 = x + y := by
    simp [MultipleReturns, MultipleReturns_precond, h_precond, MultipleReturns__rp_helper_39d93fc9]
    <;> rfl

  have h2 : (MultipleReturns (x) (y) h_precond).2 + y = x := by
    simp [MultipleReturns, MultipleReturns_precond, h_precond]
    <;> ring
    <;> simp_all [Int.add_comm, Int.add_left_comm, Int.add_assoc]
    <;> linarith

  have h_main : MultipleReturns_postcond (x) (y) (MultipleReturns (x) (y) h_precond) h_precond := by
    constructor
    · -- Prove the first part of the postcondition: (MultipleReturns (x) (y) h_precond).1 = x + y
      exact h1
    · -- Prove the second part of the postcondition: (MultipleReturns (x) (y) h_precond).2 + y = x
      exact h2

  exact h_main
  -- !benchmark @end proof
