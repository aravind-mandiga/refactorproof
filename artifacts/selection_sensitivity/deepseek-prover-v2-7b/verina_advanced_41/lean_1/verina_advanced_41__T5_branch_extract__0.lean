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

private def maxOfThree__rp_branch_81742a90 (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  if b >= a && b >= c then b
   else c
-- !benchmark @end code_aux


def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  if a >= b && a >= c then a
  else
    maxOfThree__rp_branch_81742a90 a b c h_precond
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
    simp only [maxOfThree, maxOfThree_postcond, maxOfThree_precond] at *
    split_ifs <;>
    (try omega) <;>
    (try
      {
        simp_all [maxOfThree, maxOfThree_postcond, maxOfThree_precond]
        <;>
        (try omega) <;>
        (try
          {
            omega
          }) <;>
        (try
          {
            exact ⟨by linarith, by linarith, by linarith⟩
          }) <;>
        (try
          {
            aesop
          })
      }) <;>
    (try
      {
        cases' le_total a b with h h <;>
        cases' le_total a c with h₂ h₂ <;>
        cases' le_total b c with h₃ h₃ <;>
        simp_all [maxOfThree, maxOfThree_postcond, maxOfThree_precond] <;>
        (try omega) <;>
        (try
          {
            aesop
          }) <;>
        (try
          {
            exact ⟨by linarith, by linarith, by linarith⟩
          })
      }) <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        exact ⟨by linarith, by linarith, by linarith⟩
      })
  exact h_main
  -- !benchmark @end proof


