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
  if ¬ (a = b) then false
  else true
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
  have h_main : (a = b → Compare (a) (b) h_precond = true) ∧ (a ≠ b → Compare (a) (b) h_precond = false) := by
    constructor
    · -- Prove the first part: a = b → Compare a b h_precond = true
      intro h_ab
      have h₁ : Compare (a) (b) h_precond = true := by
        dsimp [Compare]
        simp [h_ab]
      exact h₁
    · -- Prove the second part: a ≠ b → Compare a b h_precond = false
      intro h_ab_ne
      have h₁ : Compare (a) (b) h_precond = false := by
        dsimp [Compare]
        split_ifs <;> simp_all
        <;> try contradiction
      exact h₁

  -- Since Compare_postcond is exactly h_main, we can directly use it
  exact h_main
  -- !benchmark @end proof
