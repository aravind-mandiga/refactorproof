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

private def Compare__rp_branch_e4570326 (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  false
-- !benchmark @end code_aux


def Compare (a : Int) (b : Int) (h_precond : Compare_precond (a) (b)) : Bool :=
  -- !benchmark @start code
  if a = b then true else
    Compare__rp_branch_e4570326 a b h_precond
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
  have h_main : (a = b → Compare a b h_precond = true) ∧ (a ≠ b → Compare a b h_precond = false) := by
    constructor
    · -- Prove that if a = b, then Compare a b h_precond = true
      intro h
      simp [h, Compare, h_precond]
      <;> aesop
    · -- Prove that if a ≠ b, then Compare a b h_precond = false
      intro h
      simp [h, Compare, h_precond]
      <;> aesop
  -- Extract the two implications from h_main
  have h₁ : a = b → Compare a b h_precond = true := h_main.1
  have h₂ : a ≠ b → Compare a b h_precond = false := h_main.2
  -- Prove the final goal using the two implications
  constructor
  · -- Prove a = b → Compare a b h_precond = true
    intro h₃
    have h₄ : Compare a b h_precond = true := h₁ h₃
    simp_all [Compare_postcond]
    <;> aesop
  · -- Prove a ≠ b → Compare a b h_precond = false
    intro h₃
    have h₄ : Compare a b h_precond = false := h₂ h₃
    simp_all [Compare_postcond]
    <;> aesop
  -- !benchmark @end proof
