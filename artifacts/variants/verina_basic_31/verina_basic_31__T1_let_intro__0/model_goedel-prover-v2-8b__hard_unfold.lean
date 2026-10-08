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

-- !benchmark @end code_aux


def toUppercase (s : String) (h_precond : toUppercase_precond (s)) : String :=
  -- !benchmark @start code
  let __rp_tmp_fdcf2c41 : String :=
    let cs := s.toList
    let cs' := cs.map (fun c => if isLowerCase c then shiftMinus32 c else c)
    String.mk cs'
  __rp_tmp_fdcf2c41
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
  unfold toUppercase toUppercase_postcond
  have h_main : toUppercase_postcond (s) (toUppercase (s) h_precond) h_precond := by
    unfold toUppercase toUppercase_postcond
    dsimp only [List.length, List.map, List.map_append, List.map_nil, List.append]
    <;>
    (try simp_all) <;>
    (try aesop) <;>
    (try
      {
        ext i
        by_cases h : isLowerCase (s[i]!)
        <;> simp_all [isLowerCase, shiftMinus32, Char.ofNat]
        <;> omega
      }) <;>
    (try
      {
        cases s <;> simp_all [String.toList, List.map, List.map, List.length, List.append, List.nil]
        <;> aesop
      }) <;>
    (try
      {
        cases i <;> simp_all [String.toList, List.map, List.map, List.length, List.append, List.nil]
        <;> aesop
      }) <;>
    (try
      {
        omega
      }) <;>
    (try
      {
        aesop
      })
  exact h_main
  -- !benchmark @end proof
