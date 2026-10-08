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

private def minOfThree__rp_helper_d6baf0a7 (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  if a <= b && a <= c then a
  else if b <= a && b <= c then b
  else c
-- !benchmark @end code_aux


def minOfThree (a : Int) (b : Int) (c : Int) (h_precond : minOfThree_precond (a) (b) (c)) : Int :=
  -- !benchmark @start code
  minOfThree__rp_helper_d6baf0a7 a b c h_precond
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
  have h_main : ((minOfThree a b c h_precond) ≤ a ∧ (minOfThree a b c h_precond) ≤ b ∧ (minOfThree a b c h_precond) ≤ c) ∧ ((minOfThree a b c h_precond) = a ∨ (minOfThree a b c h_precond) = b ∨ (minOfThree a b c h_precond) = c) := by
    dsimp only [minOfThree_postcond, minOfThree, minOfThree_precond]
    split_ifs <;>
    (try {
      simp_all [Int.le_refl, Int.le_of_lt]
      <;>
      (try omega) <;>
      (try exact ⟨by omega, by omega, by omega⟩) <;>
      (try exact Or.inl (by omega)) <;>
      (try exact Or.inr (Or.inl (by omega))) <;>
      (try exact Or.inr (Or.inr (by omega)))
    }) <;>
    (try {
      exact ⟨⟨by omega, by omega, by omega⟩, Or.inr (Or.inr (by omega))⟩
    }) <;>
    (try {
      exact ⟨⟨by omega, by omega, by omega⟩, Or.inr (Or.inl (by omega))⟩
    }) <;>
    (try {
      exact ⟨⟨by omega, by omega, by omega⟩, Or.inl (by omega)⟩
    })
  exact h_main
  -- !benchmark @end proof
