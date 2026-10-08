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

private def DoubleQuadruple__rp_helper_8062be2e (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  let a := 2 * x
  let b := 2 * a
  (a, b)
-- !benchmark @end code_aux


def DoubleQuadruple (x : Int) (h_precond : DoubleQuadruple_precond (x)) : (Int × Int) :=
  -- !benchmark @start code
  DoubleQuadruple__rp_helper_8062be2e x h_precond
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
  have h_main : DoubleQuadruple_postcond (x) (DoubleQuadruple (x) h_precond) h_precond := by
    dsimp [DoubleQuadruple, DoubleQuadruple_postcond, DoubleQuadruple__rp_helper_8062be2e] at *
    <;>
    (try simp_all) <;>
    (try ring_nf) <;>
    (try norm_num) <;>
    (try constructor <;> ring_nf <;> norm_num) <;>
    (try simp_all [Prod.fst, Prod.snd]) <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try linarith)
    <;>
    (try
      {
        constructor <;>
        simp_all [Prod.fst, Prod.snd] <;>
        ring_nf <;>
        norm_num <;>
        linarith
      })
    <;>
    (try
      {
        simp_all [Prod.fst, Prod.snd]
        <;>
        ring_nf
        <;>
        norm_num
        <;>
        linarith
      })
  exact h_main
  -- !benchmark @end proof
