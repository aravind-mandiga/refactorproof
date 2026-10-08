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

-- !benchmark @end code_aux


def toLowercase (s : String) (h_precond : toLowercase_precond (s)) : String :=
  -- !benchmark @start code
  let __rp_tmp_313f5bc2 : String :=
    let cs := s.toList
    let cs' := cs.map (fun c => if isUpperCase c then shift32 c else c)
    String.mk cs'
  __rp_tmp_313f5bc2
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
  have h_length : (toLowercase (s) h_precond).length = s.length := by
    simp [toLowercase, List.length_map]
    <;> rfl

  have h_main : ∀ (i : Nat), i < s.length →
    (isUpperCase (s.toList.get! i) → (toLowercase (s) h_precond).toList.get! i = shift32 (s.toList.get! i)) ∧
    (¬isUpperCase (s.toList.get! i) → (toLowercase (s) h_precond).toList.get! i = s.toList.get! i) := by
    intro i h_i
    constructor
    · -- Prove the first condition: if isUpperCase, then shift32
      intro h_up
      have h1 : (toLowercase (s) h_precond).toList.get! i = shift32 (s.toList.get! i) := by
        have h2 : (toLowercase (s) h_precond).toList = (s.toList.map (fun c => if isUpperCase c then shift32 c else c)) := by
          simp [toLowercase]
          <;> congr <;> funext c <;> simp [shift32]
          <;> split <;> simp_all [List.get] <;> aesop
        rw [h2]
        have h3 : i < s.length := by simpa using h_i
        have h4 : i < s.toList.length := by simpa [List.length_map] using h3
        simp_all [List.get]
        <;> aesop
      exact h1
    · -- Prove the second condition: if not isUpperCase, then same character
      intro h_not_up
      have h1 : (toLowercase (s) h_precond).toList.get! i = s.toList.get! i := by
        have h2 : (toLowercase (s) h_precond).toList = (s.toList.map (fun c => if isUpperCase c then shift32 c else c)) := by
          simp [toLowercase]
          <;> congr <;> funext c <;> simp [shift32]
          <;> split <;> simp_all [List.get] <;> aesop
        rw [h2]
        have h3 : i < s.length := by simpa using h_i
        have h4 : i < s.toList.length := by simpa [List.length_map] using h3
        simp_all [List.get]
        <;> aesop
      exact h1

  constructor
  · -- Prove that the length of the result string is the same as the original string
    exact h_length
  · -- Prove that for all i < s.length, the i-th character of the result string is correctly transformed
    intro i h_i
    have h := h_main i h_i
    cases h with
    | intro h1 h2 =>
      have h3 : (isUpperCase (s.toList.get! i) → (toLowercase (s) h_precond).toList.get! i = shift32 (s.toList.get! i)) := h1
      have h4 : (¬isUpperCase (s.toList.get! i) → (toLowercase (s) h_precond).toList.get! i = s.toList.get! i) := h2
      simp_all [toLowercase_postcond]
      <;> aesop
  -- !benchmark @end proof
