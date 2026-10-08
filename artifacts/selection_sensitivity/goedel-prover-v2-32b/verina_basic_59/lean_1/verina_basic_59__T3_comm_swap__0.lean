-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def DoubleQuadruple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  -- !benchmark @start code
  let a := x * 2
  let b := 2 * a
  (a, b)
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def DoubleQuadruple_postcond (x : Int) (result: (Int × Int)) (h_precond : DoubleQuadruple_precond (x)) :=
  -- !benchmark @start postcond
  result.fst = 2 * x ∧ result.snd = 2 * result.fst
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem DoubleQuadruple_spec_satisfied (x: Int) (h_precond : DoubleQuadruple_precond (x)) :
    DoubleQuadruple_postcond (x) (DoubleQuadruple (x) h_precond) h_precond := by
  -- !benchmark @start proof
  have h₁ : (DoubleQuadruple x h_precond).fst = 2 * x := by
    dsimp [DoubleQuadruple]
    <;> ring_nf
    <;> simp_all [DoubleQuadruple_precond]
    <;> norm_num
    <;> aesop

  have h₂ : (DoubleQuadruple x h_precond).snd = 2 * (DoubleQuadruple x h_precond).fst := by
    dsimp [DoubleQuadruple] at *
    <;> ring_nf at *
    <;> simp_all [DoubleQuadruple_precond]
    <;> norm_num at *
    <;> linarith

  have h_main : DoubleQuadruple_postcond x (DoubleQuadruple x h_precond) h_precond := by
    dsimp [DoubleQuadruple_postcond]
    constructor
    · -- Prove the first part: (DoubleQuadruple x h_precond).fst = 2 * x
      exact h₁
    · -- Prove the second part: (DoubleQuadruple x h_precond).snd = 2 * (DoubleQuadruple x h_precond).fst
      exact h₂

  exact h_main
  -- !benchmark @end proof
