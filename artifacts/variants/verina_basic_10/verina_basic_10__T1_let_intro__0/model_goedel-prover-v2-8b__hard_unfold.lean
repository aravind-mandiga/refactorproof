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
  unfold isGreater isGreater_postcond
  have h_main : (∀ i, (hi : i < a.size) → n > a[i]) ↔ a.all (fun x => n > x) := by
    rw [Array.all_eq]
    <;> simp_all [isGreater_precond]
    <;>
    aesop

  have h_final : isGreater_postcond (n) (a) (isGreater (n) (a) h_precond) h_precond := by
    dsimp only [isGreater_postcond, isGreater, isGreater_precond] at *
    rw [h_main]
    <;> simp_all [isGreater_precond]
    <;>
    aesop

  apply h_final
  -- !benchmark @end proof
