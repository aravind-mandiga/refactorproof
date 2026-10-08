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
  dsimp [countDigits, countDigits_precond, countDigits_postcond] at *
  have h₁ : (List.length (List.filter isDigit s.toList)) - (List.length (List.filter isDigit s.toList)) = 0 := by
    simp [Nat.sub_self]

  have h₂ : (List.length (List.filter isDigit s.toList)) - (List.length (List.filter isDigit s.toList)) = 0 := by
    simp [Nat.sub_self]

  constructor <;> simp_all [Nat.sub_self]
  <;> try omega
  <;> try simp_all
  <;> try ring_nf at *
  <;> try omega
  -- !benchmark @end proof
