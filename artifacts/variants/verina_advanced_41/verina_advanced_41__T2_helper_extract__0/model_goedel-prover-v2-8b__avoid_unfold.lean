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

private def maxOfThree__rp_helper_7c6c6d3d (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  if a >= b && a >= c then a
  else if b >= a && b >= c then b
  else c
-- !benchmark @end code_aux


def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  maxOfThree__rp_helper_7c6c6d3d a b c h_precond
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
    simp only [maxOfThree_postcond, maxOfThree_precond, maxOfThree, maxOfThree_precond] at *
    split_ifs <;> simp_all [le_refl, le_of_lt]
    <;> norm_num <;>
    (try omega) <;>
    (try
      {
        by_cases h : a ≥ b <;> by_cases h' : a ≥ c <;> by_cases h'' : b ≥ c <;>
          by_cases h''' : b ≥ a <;> by_cases h'''' : c ≥ a <;> by_cases h''''' : c ≥ b <;>
            simp_all [max_eq_left, max_eq_right, le_refl, le_of_lt] <;>
            (try omega) <;>
            (try { aesop }) <;>
            (try {
              cases' le_total a b with hab hab <;> cases' le_total b c with hbc hbc <;> cases' le_total c a with hac hac <;>
                simp_all [max_eq_left, max_eq_right, le_refl, le_of_lt] <;>
                (try omega) <;>
                (try { aesop })
            })
      }) <;>
    (try {
      omega
    }) <;>
    (try {
      aesop
    }) <;>
    (try {
      norm_num
      <;> omega
    }) <;>
    (try {
      norm_num
      <;> omega
    }) <;>
    (try {
      omega
    })
    <;>
    (try {
      aesop
    })
    <;>
    (try {
      norm_num
      <;> omega
    })
    <;>
    (try {
      omega
    })
  exact h_main
  -- !benchmark @end proof


