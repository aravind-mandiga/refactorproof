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
  have h₁ : (a = b → (Compare (a) (b) h_precond) = true) := by
    intro h
    have h₂ : (Compare (a) (b) h_precond) = true := by
      dsimp [Compare]
      split_ifs <;> simp_all
      <;> contradiction
    exact h₂

  have h₂ : (a ≠ b → (Compare (a) (b) h_precond) = false) := by
    intro h
    have h₃ : (Compare (a) (b) h_precond) = false := by
      dsimp [Compare]
      split_ifs <;> simp_all
      <;> contradiction
    exact h₃

  have h_main : Compare_postcond (a) (b) (Compare (a) (b) h_precond) h_precond := by
    refine' ⟨h₁, h₂⟩

  exact h_main
  -- !benchmark @end proof
