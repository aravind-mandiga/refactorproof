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

private def Compare__rp_helper_56630b5e (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  if a = b then true else false
-- !benchmark @end code_aux


def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  -- !benchmark @start code
  Compare__rp_helper_56630b5e a b h_precond
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
  have h₁ : a = b → Compare (a) (b) h_precond = true := by
    intro h
    have h₂ : a = b := h
    have h₃ : Compare (a) (b) h_precond = true := by
      rw [Compare]
      split_ifs <;> simp_all
    exact h₃

  have h₂ : a ≠ b → Compare (a) (b) h_precond = false := by
    intro h
    have h₃ : a ≠ b := h
    have h₄ : Compare (a) (b) h_precond = false := by
      rw [Compare]
      split_ifs <;> simp_all
    exact h₄

  have h₃ : (a = b → Compare (a) (b) h_precond = true) ∧ (a ≠ b → Compare (a) (b) h_precond = false) := by
    exact ⟨h₁, h₂⟩

  exact h₃
  -- !benchmark @end proof
