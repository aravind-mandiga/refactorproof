-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isGreater_precond (n : Int) (a : Array Int) : Prop :=
  -- !benchmark @start precond
  a.size > 0
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isGreater (n : Int) (a : Array Int) (h_precond : isGreater_precond (n) (a)) : Bool :=
  -- !benchmark @start code
  let __rp_tmp_f0724323 : Bool :=
    a.all fun x => n > x
  __rp_tmp_f0724323
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isGreater_postcond (n : Int) (a : Array Int) (result: Bool) (h_precond : isGreater_precond (n) (a)) :=
  -- !benchmark @start postcond
  (∀ i, (hi : i < a.size) → n > a[i]) ↔ result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isGreater_spec_satisfied (n: Int) (a: Array Int) (h_precond : isGreater_precond (n) (a)) :
    isGreater_postcond (n) (a) (isGreater (n) (a) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : isGreater_postcond (n) (a) (isGreater (n) (a) h_precond) h_precond := by
    simp [isGreater_postcond, isGreater, isGreater_precond, h_precond]
    <;>
    (try decide) <;>
    (try ring_nf) <;>
    (try simp_all [Array.all, Int.lt_iff_add_one_le]) <;>
    (try omega) <;>
    (try aesop) <;>
    (try norm_num) <;>
    (try ring_nf) <;>
    (try omega)
    <;>
    (try aesop)
    <;>
    (try norm_num)
    <;>
    (try ring_nf)
    <;>
    (try omega)
    <;>
    (try aesop)
    <;>
    (try norm_num)
    <;>
    (try ring_nf)
    <;>
    (try omega)
    <;>
    (try aesop)
    <;>
    (try norm_num)
    <;>
    (try ring_nf)
    <;>
    (try omega)
    <;>
    (try aesop)
    <;>
    (try norm_num)
    <;>
    (try ring_nf)
    <;>
    (try omega)
    <;>
    (try aesop)
  exact h_main
  -- !benchmark @end proof
