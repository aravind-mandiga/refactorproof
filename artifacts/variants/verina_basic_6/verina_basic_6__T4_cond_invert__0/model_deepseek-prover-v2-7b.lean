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
  have h₁ : ((minOfThree (a) (b) (c) h_precond : Int) ≤ a ∧ (minOfThree (a) (b) (c) h_precond : Int) ≤ b ∧ (minOfThree (a) (b) (c) h_precond : Int) ≤ c) ∧ ((minOfThree (a) (b) (c) h_precond : Int) = a ∨ (minOfThree (a) (b) (c) h_precond : Int) = b ∨ (minOfThree (a) (b) (c) h_precond : Int) = c) := by
    dsimp only [minOfThree, minOfThree_postcond, minOfThree_precond]
    -- Consider the cases based on the comparisons between a, b, and c
    split_ifs with h₁ h₂ h₃ <;> simp_all [and_imp, Prod.exists, exists_and_right, exists_prop]
    <;>
    (try {
      aesop
    }) <;>
    (try {
      omega
    }) <;>
    (try {
      exact ⟨by omega, by omega, by omega⟩
    }) <;>
    (try {
      exact Or.inl (by omega)
    }) <;>
    (try {
      exact Or.inr (Or.inl (by omega))
    }) <;>
    (try {
      exact Or.inr (Or.inr (by omega))
    })
    <;>
    (try {
      aesop
    })
    <;>
    (try {
      omega
    })
    <;>
    (try {
      exact ⟨by omega, by omega, by omega⟩
    })
    <;>
    (try {
      exact Or.inl (by omega)
    })
    <;>
    (try {
      exact Or.inr (Or.inl (by omega))
    })
    <;>
    (try {
      exact Or.inr (Or.inr (by omega))
    })

  exact h₁
  -- !benchmark @end proof
