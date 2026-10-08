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
  let __rp_tmp_883fb5c3 : (Int × Int) :=
    let a := 2 * x
    let b := 2 * a
    (a, b)
  __rp_tmp_883fb5c3
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
    simp [DoubleQuadruple, DoubleQuadruple_postcond, DoubleQuadruple_precond]
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try omega) <;>
    (try aesop)
    <;>
    (try
      {
        simp_all [Prod.ext_iff]
        <;>
        norm_num
        <;>
        ring_nf
        <;>
        omega
      })
  exact h_main
  -- !benchmark @end proof
