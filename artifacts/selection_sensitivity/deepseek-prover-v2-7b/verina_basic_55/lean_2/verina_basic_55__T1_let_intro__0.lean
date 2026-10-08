-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Compare_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  -- !benchmark @start code
  let __rp_tmp_ddcd7819 : Bool :=
    if a = b then true else false
  __rp_tmp_ddcd7819
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Compare_postcond (a : Int) (b : Int) (result: Bool) (h_precond : Compare_precond (a) (b)) :=
  -- !benchmark @start postcond
  (a = b → result = true) ∧ (a ≠ b → result = false)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Compare_spec_satisfied (a: Int) (b: Int) (h_precond : Compare_precond (a) (b)) :
    Compare_postcond (a) (b) (Compare (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  have h1 : (a = b → Compare a b h_precond = true) := by
    intro h
    simp [Compare, h]
    <;> aesop

  have h2 : (a ≠ b → Compare a b h_precond = false) := by
    intro h
    simp [Compare, h]
    <;> aesop

  have h_main : Compare_postcond a b (Compare a b h_precond) h_precond := by
    constructor
    · -- Prove the first part of the conjunction: if a = b, then result = true
      intro h_eq
      have h3 : Compare a b h_precond = true := by
        have h4 : a = b := h_eq
        simpa [Compare, h4] using h1 h_eq
      simpa [Compare_postcond, h3] using h3
    · -- Prove the second part of the conjunction: if a ≠ b, then result = false
      intro h_ne
      have h3 : Compare a b h_precond = false := by
        have h4 : a ≠ b := h_ne
        simpa [Compare, h4] using h2 h_ne
      simpa [Compare_postcond, h3] using h3

  exact h_main
  -- !benchmark @end proof
