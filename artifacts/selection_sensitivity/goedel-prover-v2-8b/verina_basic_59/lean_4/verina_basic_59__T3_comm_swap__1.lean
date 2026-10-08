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
  let a := 2 * x
  let b := a * 2
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
  have h1 : (DoubleQuadruple (x) h_precond).fst = 2 * x := by
    simp [DoubleQuadruple, Int.mul_assoc]
    <;> ring_nf
    <;> norm_num
    <;> simp_all

  have h2 : (DoubleQuadruple (x) h_precond).snd = 2 * (DoubleQuadruple (x) h_precond).fst := by
    simp [DoubleQuadruple, Int.mul_assoc] at h1 ⊢
    <;> ring_nf at h1 ⊢
    <;> norm_num at h1 ⊢
    <;> simp_all
    <;> linarith

  have h_main : DoubleQuadruple_postcond x (DoubleQuadruple x h_precond) h_precond := by
    have h3 : (DoubleQuadruple (x) h_precond).fst = 2 * x := h1
    have h4 : (DoubleQuadruple (x) h_precond).snd = 2 * (DoubleQuadruple (x) h_precond).fst := h2
    simp_all [DoubleQuadruple_postcond]
    <;> aesop

  exact h_main
  -- !benchmark @end proof
