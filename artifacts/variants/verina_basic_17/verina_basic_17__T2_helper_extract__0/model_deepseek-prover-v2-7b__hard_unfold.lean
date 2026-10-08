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
  unfold toLowercase toLowercase_postcond
  have h_len : (toLowercase (s) h_precond).length = s.length := by
    simp [toLowercase, List.length_map]
    <;>
    rfl

  have h_main : ∀ (i : Nat), i < s.length → (isUpperCase (s.toList[i]!) → (toLowercase (s) h_precond).toList[i]! = shift32 (s.toList[i]!)) ∧ (¬isUpperCase (s.toList[i]!) → (toLowercase (s) h_precond).toList[i]! = s.toList[i]!) := by
    intro i hi
    constructor
    · -- Prove the first implication: if c is uppercase, then toLowercase_postcond holds
      intro h
      simp_all [toLowercase, List.get]
      <;>
      (try aesop) <;>
      (try {
        simp_all [isUpperCase, shift32, List.get]
        <;>
        (try
          {
            split_ifs <;>
            simp_all [List.get] <;>
            (try omega) <;>
            (try aesop) <;>
            (try contradiction)
          })
        <;>
        (try omega)
        <;>
        (try aesop)
        <;>
        (try contradiction)
      }) <;>
      (try {
        cases s with
        | mk s' =>
          cases s' with
          | nil => contradiction
          | cons s0 ss =>
            simp_all [List.get]
            <;>
            aesop
      })
    · -- Prove the second implication: if c is not uppercase, then toLowercase_postcond holds
      intro h
      simp_all [toLowercase, List.get]
      <;>
      (try aesop) <;>
      (try {
        simp_all [isUpperCase, shift32, List.get]
        <;>
        (try
          {
            split_ifs <;>
            simp_all [List.get] <;>
            (try omega) <;>
            (try aesop) <;>
            (try contradiction)
          })
        <;>
        (try omega)
        <;>
        (try aesop)
        <;>
        (try contradiction)
      }) <;>
      (try {
        cases s with
        | mk s' =>
          cases s' with
          | nil => contradiction
          | cons s0 ss =>
            simp_all [List.get]
            <;>
            aesop
      })

  constructor
  · exact h_len
  · intro i hi
    have h := h_main i hi
    aesop
  -- !benchmark @end proof
