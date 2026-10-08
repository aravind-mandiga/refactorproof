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
  have h_main : (a = b → (Compare (a) (b) h_precond) = true) ∧ (a ≠ b → (Compare (a) (b) h_precond) = false) := by
    by_cases h : a = b
    · -- Case: a = b
      have h₁ : Compare (a) (b) h_precond = true := by
        -- Since a = b, the if condition in Compare evaluates to true
        simp [Compare, h]
        <;> simp_all [Compare_precond]
        <;> aesop
      -- Prove the two implications in this case
      have h₂ : (a = b → (Compare (a) (b) h_precond) = true) := by
        intro h'
        rw [h₁]
      have h₃ : (a ≠ b → (Compare (a) (b) h_precond) = false) := by
        intro h'
        exfalso
        -- Since a = b, a ≠ b leads to a contradiction
        apply h'
        exact h
      exact ⟨h₂, h₃⟩
    · -- Case: a ≠ b
      have h₁ : Compare (a) (b) h_precond = false := by
        -- Since a ≠ b, the if condition in Compare evaluates to false
        simp [Compare, h]
        <;> simp_all [Compare_precond]
        <;> aesop
      -- Prove the two implications in this case
      have h₂ : (a = b → (Compare (a) (b) h_precond) = true) := by
        intro h'
        exfalso
        -- Since a ≠ b, a = b leads to a contradiction
        apply h
        exact h'
      have h₃ : (a ≠ b → (Compare (a) (b) h_precond) = false) := by
        intro h'
        rw [h₁]
      exact ⟨h₂, h₃⟩

  -- Simplify the goal using the definition of Compare_postcond and the result from h_main
  simp_all [Compare_postcond]
  <;> aesop
  -- !benchmark @end proof
