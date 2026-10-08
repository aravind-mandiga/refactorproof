-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def minOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  if ¬ (a <= b && a <= c) then if b <= a && b <= c then b
  else c
  else a
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def minOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : minOfThree_precond (a) (b) (c)) :=
  -- !benchmark @start postcond
  (result <= a ∧ result <= b ∧ result <= c) ∧
  (result = a ∨ result = b ∨ result = c)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem minOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : minOfThree_precond (a) (b) (c)) :
    minOfThree_postcond (a) (b) (c) (minOfThree (a) (b) (c) h_precond) h_precond := by
  -- !benchmark @start proof
  unfold minOfThree minOfThree_postcond
  have h_main : (minOfThree a b c h_precond) ≤ a ∧ (minOfThree a b c h_precond) ≤ b ∧ (minOfThree a b c h_precond) ≤ c ∧ ((minOfThree a b c h_precond) = a ∨ (minOfThree a b c h_precond) = b ∨ (minOfThree a b c h_precond) = c) := by
    dsimp only [minOfThree_postcond, minOfThree, minOfThree_precond] at *
    split_ifs with h₁ h₂ h₃ <;> simp_all [minOfThree_postcond, minOfThree, minOfThree_precond]
    <;> (try omega) <;> (try {
      aesop
    }) <;> (try {
      norm_num at * <;>
      omega
    }) <;> (try {
      aesop
    }) <;> (try {
      norm_num at * <;>
      omega
    }) <;> (try {
      aesop
    })
    <;> (try {
      norm_num at * <;>
      omega
    })
    <;> omega
    <;> aesop
    <;> aesop
    <;> aesop

  simp_all [minOfThree_postcond]
  <;> aesop
  -- !benchmark @end proof
