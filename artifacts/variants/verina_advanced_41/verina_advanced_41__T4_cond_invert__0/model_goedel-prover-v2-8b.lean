-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  if ¬ (a >= b && a >= c) then if b >= a && b >= c then b
  else c
  else a
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  -- !benchmark @start postcond
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem maxOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    maxOfThree_postcond (a) (b) (c) (maxOfThree (a) (b) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : maxOfThree_postcond (a) (b) (c) (maxOfThree (a) (b) (c) h_precond) h_precond := by
    constructor
    · -- Prove that the result is >= a, >= b, >= c
      have h₁ : maxOfThree (a) (b) (c) h_precond = if a >= b && a >= c then a else if b >= a && b >= c then b else c := by
        rfl
      rw [h₁]
      split_ifs with h₂ h₃
      · -- Case 1: a >= b && a >= c
        constructor <;>
        (try constructor) <;>
        (try simp_all) <;>
        (try omega) <;>
        (try
          {
            cases' le_total a b with hab hab <;> cases' le_total a c with hac hac <;>
            cases' le_total b c with hbc hbc <;>
            simp_all [max_eq_left, max_eq_right, le_refl, le_of_lt, le_trans] <;>
            omega
          }) <;>
        omega
      · -- Case 2: b >= a && b >= c
        constructor <;>
        (try constructor) <;>
        (try simp_all) <;>
        (try omega) <;>
        (try
          {
            cases' le_total a b with hab hab <;> cases' le_total a c with hac hac <;>
            cases' le_total b c with hbc hbc <;>
            simp_all [max_eq_left, max_eq_right, le_refl, le_of_lt, le_trans] <;>
            omega
          }) <;>
        omega
      · -- Case 3: c >= a && c >= b
        constructor <;>
        (try constructor) <;>
        (try simp_all) <;>
        (try omega) <;>
        (try
          {
            cases' le_total a b with hab hab <;> cases' le_total a c with hac hac <;>
            cases' le_total b c with hbc hbc <;>
            simp_all [max_eq_left, max_eq_right, le_refl, le_of_lt, le_trans] <;>
            omega
          }) <;>
        omega
    · -- Prove that the result is one of a, b, or c
      have h₁ : maxOfThree (a) (b) (c) h_precond = if a >= b && a >= c then a else if b >= a && b >= c then b else c := by
        rfl
      rw [h₁]
      split_ifs with h₂ h₃
      · -- Case 1: a >= b && a >= c
        simp_all [maxOfThree_postcond]
        <;>
        (try omega) <;>
        (try aesop) <;>
        (try
          {
            cases' le_total a b with hab hab <;> cases' le_total a c with hac hac <;>
            cases' le_total b c with hbc hbc <;>
            simp_all [max_eq_left, max_eq_right, le_refl, le_of_lt, le_trans] <;>
            omega
          })
      · -- Case 2: b >= a && b >= c
        simp_all [maxOfThree_postcond]
        <;>
        (try omega) <;>
        (try aesop) <;>
        (try
          {
            cases' le_total a b with hab hab <;> cases' le_total a c with hac hac <;>
            cases' le_total b c with hbc hbc <;>
            simp_all [max_eq_left, max_eq_right, le_refl, le_of_lt, le_trans] <;>
            omega
          })
      · -- Case 3: c >= a && c >= b
        simp_all [maxOfThree_postcond]
        <;>
        (try omega) <;>
        (try aesop) <;>
        (try
          {
            cases' le_total a b with hab hab <;> cases' le_total a c with hac hac <;>
            cases' le_total b c with hbc hbc <;>
            simp_all [max_eq_left, max_eq_right, le_refl, le_of_lt, le_trans] <;>
            omega
          })
  exact h_main
  -- !benchmark @end proof


