-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux
def isDigit (c : Char) : Bool :=
  '0' ≤ c ∧ c ≤ '9'
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def countDigits_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def countDigits (s : String) (h_precond : countDigits_precond (s)) : Nat :=
  -- !benchmark @start code
  let __rp_tmp_82b48cb8 : Nat :=
    List.length (List.filter isDigit s.toList)
  __rp_tmp_82b48cb8
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def countDigits_postcond (s : String) (result: Nat) (h_precond : countDigits_precond (s)) :=
  -- !benchmark @start postcond
  result - List.length (List.filter isDigit s.toList) = 0 ∧
  List.length (List.filter isDigit s.toList) - result = 0
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem countDigits_spec_satisfied (s: String) (h_precond : countDigits_precond (s)) :
    countDigits_postcond (s) (countDigits (s) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : countDigits_postcond s (countDigits s h_precond) h_precond := by
    have h₁ : countDigits s h_precond = List.length (List.filter isDigit s.toList) := by
      rfl
    have h₂ : countDigits_postcond s (countDigits s h_precond) h_precond := by
      rw [countDigits_postcond, h₁]
      constructor
      · -- Prove the first condition: (countDigits s h_precond) - length (filter isDigit s.toList) = 0
        simp [Nat.sub_self]
      · -- Prove the second condition: length (filter isDigit s.toList) - (countDigits s h_precond) = 0
        simp [Nat.sub_self]
    exact h₂
  exact h_main
  -- !benchmark @end proof
