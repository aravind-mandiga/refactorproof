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
  unfold Compare Compare_postcond
  have h_main : (a = b → (Compare (a) (b) h_precond) = true) ∧ (a ≠ b → (Compare (a) (b) h_precond) = false) := by
    constructor
    · -- Prove the first part: a = b → Compare (a) (b) h_precond = true
      intro h_eq
      -- If a = b, then Compare (a) (b) h_precond = true
      simp [h_eq, Compare]
      <;> aesop
    · -- Prove the second part: a ≠ b → Compare (a) (b) h_precond = false
      intro h_ne
      -- If a ≠ b, then Compare (a) (b) h_precond = false
      simp [h_ne, Compare]
      <;> aesop

  exact h_main
  -- !benchmark @end proof
