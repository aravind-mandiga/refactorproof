-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def multiply_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def multiply (a : Int) (b : Int) (h_precond : multiply_precond (a) (b)) : Int :=
  -- !benchmark @start code
  let __rp_tmp_aec1bda6 : Int :=
    a * b
  __rp_tmp_aec1bda6
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def multiply_postcond (a : Int) (b : Int) (result: Int) (h_precond : multiply_precond (a) (b)) :=
  -- !benchmark @start postcond
  result - a * b = 0 ∧ a * b - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem multiply_spec_satisfied (a: Int) (b: Int) (h_precond : multiply_precond (a) (b)) :
    multiply_postcond (a) (b) (multiply (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold multiply multiply_postcond
  have h_main : multiply_postcond (a) (b) (multiply (a) (b) h_precond) h_precond := by
    unfold multiply_postcond
    simp [multiply, multiply_precond] at *
    <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try simp_all [Int.sub_self]) <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try simp_all [Int.sub_self]) <;>
    (try aesop)
    <;>
    (try omega)
    <;>
    (try ring_nf at *) <;>
    (try aesop)
    <;>
    (try
      {
        simp_all [Int.sub_self]
        <;>
        aesop
      })
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        ring_nf at *
        <;>
        aesop
      })
  exact h_main
  -- !benchmark @end proof
