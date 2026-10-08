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
  have h_main : (minOfThree (a) (b) (c) h_precond ≤ a ∧ minOfThree (a) (b) (c) h_precond ≤ b ∧ minOfThree (a) (b) (c) h_precond ≤ c) ∧ (minOfThree (a) (b) (c) h_precond = a ∨ minOfThree (a) (b) (c) h_precond = b ∨ minOfThree (a) (b) (c) h_precond = c) := by
    have h₁ : minOfThree (a) (b) (c) h_precond ≤ a ∧ minOfThree (a) (b) (c) h_precond ≤ b ∧ minOfThree (a) (b) (c) h_precond ≤ c := by
      dsimp [minOfThree, minOfThree_precond, Int.le_of_lt_add_one, Int.le_of_lt_add_one] at h_precond ⊢
      split_ifs at * <;>
      (try omega) <;>
      (try {
        by_cases h : a ≤ b <;> by_cases h' : a ≤ c <;> by_cases h'' : b ≤ a <;> by_cases h''' : b ≤ c <;> simp_all [Int.le_of_lt_add_one, Int.le_of_lt_add_one] <;>
          (try omega) <;>
          (try {
            omega
          })
      }) <;>
      (try {
        omega
      }) <;>
      (try {
        linarith
      }) <;>
      (try {
        nlinarith
      })
    have h₂ : minOfThree (a) (b) (c) h_precond = a ∨ minOfThree (a) (b) (c) h_precond = b ∨ minOfThree (a) (b) (c) h_precond = c := by
      dsimp [minOfThree, minOfThree_precond, Int.le_of_lt_add_one, Int.le_of_lt_add_one] at h_precond ⊢
      split_ifs at * <;>
      (try omega) <;>
      (try {
        by_cases h : a ≤ b <;> by_cases h' : a ≤ c <;> by_cases h'' : b ≤ a <;> by_cases h''' : b ≤ c <;> simp_all [Int.le_of_lt_add_one, Int.le_of_lt_add_one] <;>
          (try omega) <;>
          (try {
            omega
          })
      }) <;>
      (try {
        omega
      }) <;>
      (try {
        linarith
      }) <;>
      (try {
        nlinarith
      })
    exact ⟨h₁, h₂⟩

  simpa [minOfThree_postcond] using h_main
  -- !benchmark @end proof
