-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux
def isLowerCase (c : Char) : Bool :=
  'a' ≤ c ∧ c ≤ 'z'

def shiftMinus32 (c : Char) : Char :=
  Char.ofNat ((c.toNat - 32) % 128)
-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def toUppercase_precond (s : String) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def toUppercase__rp_helper_8bd90157 (s : String) (h_precond : toUppercase_precond (s)) : String :=
  let cs := s.toList
  let cs' := cs.map (fun c => if isLowerCase c then shiftMinus32 c else c)
  String.mk cs'
-- !benchmark @end code_aux


def toUppercase (s : String) (h_precond : toUppercase_precond (s)) : String :=
  -- !benchmark @start code
  toUppercase__rp_helper_8bd90157 s h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def toUppercase_postcond (s : String) (result: String) (h_precond : toUppercase_precond (s)) :=
  -- !benchmark @start postcond
  let cs := s.toList
  let cs' := result.toList
  (result.length = s.length) ∧
  (∀ i, i < s.length →
    (isLowerCase cs[i]! → cs'[i]! = shiftMinus32 cs[i]!) ∧
    (¬isLowerCase cs[i]! → cs'[i]! = cs[i]!))
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem toUppercase_spec_satisfied (s: String) (h_precond : toUppercase_precond (s)) :
    toUppercase_postcond (s) (toUppercase (s) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : toUppercase_postcond (s) (toUppercase (s) h_precond) h_precond := by
    dsimp [toUppercase_precond, toUppercase_postcond]
    have h₁ : (toUppercase (s) h_precond).length = s.length := by
      simp [toUppercase, List.length_map, List.length_cons, List.length_nil]
      <;>
      induction s <;> simp_all [String.toList_cons, Char.toNat_add, List.map_cons, List.map_nil,
        List.length_map, List.length_cons, List.length_nil]
      <;>
      rfl
    have h₂ : ∀ i, i < s.length → (isLowerCase (s.toList[i]!) → (toUppercase (s) h_precond).toList[i]! = shiftMinus32 (s.toList[i]!)) ∧ (¬isLowerCase (s.toList[i]!) → (toUppercase (s) h_precond).toList[i]! = s.toList[i]!) := by
      intro i hi
      have h₃ : isLowerCase (s.toList[i]!) → (toUppercase (s) h_precond).toList[i]! = shiftMinus32 (s.toList[i]!) := by
        intro h
        have h₄ : (toUppercase (s) h_precond).toList[i]! = shiftMinus32 (s.toList[i]!) := by
          simp_all [toUppercase, List.map]
          <;> aesop
        exact h₄
      have h₅ : ¬isLowerCase (s.toList[i]!) → (toUppercase (s) h_precond).toList[i]! = s.toList[i]! := by
        intro h
        have h₆ : (toUppercase (s) h_precond).toList[i]! = s.toList[i]! := by
          simp_all [toUppercase, List.map]
          <;> aesop
        exact h₆
      exact ⟨h₃, h₅⟩
    exact ⟨h₁, h₂⟩
  exact h_main
  -- !benchmark @end proof
