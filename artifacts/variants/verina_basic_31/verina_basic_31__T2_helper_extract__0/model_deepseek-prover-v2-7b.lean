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
    dsimp [toUppercase, toUppercase_postcond, isLowerCase, shiftMinus32]
    constructor
    · -- Prove that the lengths are the same
      simp [List.length_map]
    · -- Prove the condition for each index i
      intro i h₁
      have h₂ : i < s.length := h₁
      -- We need to consider the i-th character of the list
      simp [List.get]
      <;>
      (try
        {
          split <;> simp_all [List.get] <;>
          (try omega) <;>
          (try
            {
              simp_all [List.get]
              <;>
              (try
                {
                  simp_all [List.get]
                  <;>
                  (try
                    {
                      omega
                    })
                })
            })
        })
      <;>
      (try
        {
          -- If the character is lowercase, the mapping works
          simp_all [List.get]
          <;>
          (try
            {
              simp_all [List.get]
              <;>
              (try
                {
                  omega
                })
            })
        })
      <;>
      (try
        {
          -- If the character is not lowercase, the mapping works
          simp_all [List.get]
          <;>
          (try
            {
              simp_all [List.get]
              <;>
              (try
                {
                  omega
                })
            })
        })
      <;>
      (try
        {
          -- If the character is lowercase, show that the shift is correct
          split_ifs <;> simp_all [List.get, Char.ofNat_le] <;>
          (try
            {
              norm_num at *
              <;>
              omega
            })
          <;>
          (try
            {
              simp_all [List.get]
              <;>
              omega
            })
        })
      <;>
      (try
        {
          -- If the character is not lowercase, the mapping works
          split_ifs <;> simp_all [List.get, Char.ofNat_le] <;>
          (try omega) <;> (try omega) <;>
          (try
            {
              simp_all [List.get]
              <;>
              omega
            })
        })
  exact h_main
  -- !benchmark @end proof
