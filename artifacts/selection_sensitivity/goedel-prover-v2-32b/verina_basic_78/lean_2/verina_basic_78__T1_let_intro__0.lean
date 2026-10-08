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

-- !benchmark @end code_aux


def MultipleReturns (x : Int) (y : Int) (h_precond : MultipleReturns_precond (x) (y)) : (Int × Int) :=
  -- !benchmark @start code
  let __rp_tmp_ce491c75 : (Int × Int) :=
    let more := x + y
    let less := x - y
    (more, less)
  __rp_tmp_ce491c75
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
  have h₁ : (MultipleReturns x y h_precond).1 = x + y := by
    dsimp [MultipleReturns]
    <;> simp_all [MultipleReturns_precond]
    <;> ring_nf
    <;> rfl

  have h₂ : (MultipleReturns x y h_precond).2 + y = x := by
    dsimp [MultipleReturns]
    <;> simp_all [MultipleReturns_precond]
    <;> ring_nf at *
    <;> linarith

  have h_main : MultipleReturns_postcond x y (MultipleReturns x y h_precond) h_precond := by
    dsimp [MultipleReturns_postcond] at *
    <;> simp_all [MultipleReturns_precond]
    <;> constructor <;> (try ring_nf at *) <;> (try linarith) <;> (try assumption)
    <;> (try simp_all)
    <;> (try nlinarith)

  exact h_main
  -- !benchmark @end proof
