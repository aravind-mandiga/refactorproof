-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux
def isUpperCase (c : Char) : Bool :=
  'A' ≤ c ∧ c ≤ 'Z'

def shift32 (c : Char) : Char :=
  Char.ofNat (c.toNat + 32)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def toLowercase_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def toLowercase__rp_helper_b6759a4e (s : String) (h_precond : toLowercase_precond (s)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if isUpperCase c then shift32 c else c)
  String.mk cs'
-- !benchmark @end code_aux


def toLowercase (s : String) (h_precond : toLowercase_precond (s)) : String :=
  -- !benchmark @start code
  toLowercase__rp_helper_b6759a4e s h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def toLowercase_postcond (s : String) (result: String) (h_precond : toLowercase_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i : Nat, i < s.length →
    (isUpperCase cs[i]! → cs'[i]! = shift32 cs[i]!) ∧
    (¬isUpperCase cs[i]! → cs'[i]! = cs[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem toLowercase_spec_satisfied (s: String) (h_precond : toLowercase_precond (s)) :
    toLowercase_postcond (s) (toLowercase (s) h_precond) h_precond := by
  -- !benchmark @start proof
  have h₁ : (toLowercase (s) h_precond).length = s.length := by
    simp [toLowercase, toLowercase_precond, List.length_map]
    <;>
    simp_all [String.toList_eq_nil]
    <;>
    rfl

  have h₂ : ∀ (i : Nat), i < s.length → (isUpperCase (s.toList[i]!) → (toLowercase (s) h_precond).toList[i]! = shift32 (s.toList[i]!)) ∧ (¬isUpperCase (s.toList[i]!) → (toLowercase (s) h_precond).toList[i]! = s.toList[i]!) := by
    intro i hi
    have h₃ : (isUpperCase (s.toList[i]!) → (toLowercase (s) h_precond).toList[i]! = shift32 (s.toList[i]!)) ∧ (¬isUpperCase (s.toList[i]!) → (toLowercase (s) h_precond).toList[i]! = s.toList[i]!) := by
      have h₄ : (toLowercase (s) h_precond).toList = (s.toList).map (fun c => if isUpperCase c then shift32 c else c) := by
        simp [toLowercase, toLowercase_precond, List.map_map]
        <;>
        simp_all [String.toList_eq_nil]
        <;>
        rfl
      have h₅ : (toLowercase (s) h_precond).toList[i]! = (if isUpperCase (s.toList[i]!) then shift32 (s.toList[i]!) else (s.toList[i]!)) := by
        rw [h₄]
        <;>
        simp [List.get]
        <;>
        aesop
      constructor
      · intro h₆
        rw [h₅]
        <;>
        simp [h₆]
        <;>
        aesop
      · intro h₆
        rw [h₅]
        <;>
        simp [h₆]
        <;>
        aesop
    exact h₃

  have h₃ : toLowercase_postcond (s) (toLowercase (s) h_precond) h_precond := by
    constructor
    · -- Prove that the length of the result is the same as the input string
      exact h₁
    · -- Prove that for every index i < s.length, the result satisfies the required properties
      intro i hi
      exact h₂ i hi

  exact h₃
  -- !benchmark @end proof
