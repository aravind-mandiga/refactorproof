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
  have h_main : minOfThree_postcond (a) (b) (c) (minOfThree (a) (b) (c) h_precond) h_precond := by
    constructor
    · -- Prove that the result is less than or equal to a, b, and c
      by_cases h₁ : a ≤ b ∧ a ≤ c
      · -- Case 1: a ≤ b and a ≤ c
        have h₂ : minOfThree (a) (b) (c) h_precond = a := by
          rw [minOfThree]
          <;> simp_all
        rw [h₂]
        constructor <;> simp_all
        <;> omega
      · by_cases h₂ : b ≤ a ∧ b ≤ c
        · -- Case 2: b ≤ a and b ≤ c
          have h₃ : minOfThree (a) (b) (c) h_precond = b := by
            rw [minOfThree]
            <;> simp_all
            <;> omega
          rw [h₃]
          constructor <;> simp_all
          <;> omega
        · -- Case 3: Neither a ≤ b ∧ a ≤ c nor b ≤ a ∧ b ≤ c
          have h₃ : minOfThree (a) (b) (c) h_precond = c := by
            rw [minOfThree]
            <;> simp_all
            <;> omega
          rw [h₃]
          have h₄ : c ≤ a := by
            by_contra h₄
            have h₅ : a < c := by linarith
            have h₆ : a ≤ b := by
              by_contra h₆
              have h₇ : b < a := by linarith
              have h₈ : b ≤ a ∧ b ≤ c := by
                constructor <;> (try omega) <;> (try
                  {
                    by_contra h₉
                    have h₁₀ : a ≤ c := by
                      omega
                    have h₁₁ : a ≤ b ∧ a ≤ c := by
                      exact ⟨by omega, h₁₀⟩
                    contradiction
                  })
              contradiction
            have h₇ : a ≤ c := by
              by_contra h₇
              have h₈ : c < a := by linarith
              have h₉ : a ≤ b ∧ a ≤ c := by
                exact ⟨h₆, by omega⟩
              contradiction
            have h₈ : a ≤ b ∧ a ≤ c := by
              exact ⟨h₆, h₇⟩
            contradiction
          have h₅ : c ≤ b := by
            by_contra h₅
            have h₆ : b < c := by linarith
            have h₇ : b ≤ a := by
              by_contra h₇
              have h₈ : a < b := by linarith
              have h₉ : b ≤ a ∧ b ≤ c := by
                constructor <;> (try omega) <;> (try
                  {
                    by_contra h₁₀
                    have h₁₁ : b ≤ a := by
                      omega
                    have h₁₂ : b ≤ a ∧ b ≤ c := by
                      exact ⟨h₁₁, by omega⟩
                    contradiction
                  })
              contradiction
            have h₈ : b ≤ c := by
              by_contra h₈
              have h₉ : c < b := by linarith
              have h₁₀ : b ≤ a ∧ b ≤ c := by
                exact ⟨h₇, by omega⟩
              contradiction
            have h₉ : b ≤ a ∧ b ≤ c := by
              exact ⟨h₇, h₈⟩
            contradiction
          constructor <;> simp_all
          <;> omega
    · -- Prove that the result is equal to a, b, or c
      by_cases h₁ : a ≤ b ∧ a ≤ c
      · -- Case 1: a ≤ b and a ≤ c
        have h₂ : minOfThree (a) (b) (c) h_precond = a := by
          rw [minOfThree]
          <;> simp_all
        rw [h₂]
        simp_all
        <;> tauto
      · by_cases h₂ : b ≤ a ∧ b ≤ c
        · -- Case 2: b ≤ a and b ≤ c
          have h₃ : minOfThree (a) (b) (c) h_precond = b := by
            rw [minOfThree]
            <;> simp_all
            <;> omega
          rw [h₃]
          simp_all
          <;> tauto
        · -- Case 3: Neither a ≤ b ∧ a ≤ c nor b ≤ a ∧ b ≤ c
          have h₃ : minOfThree (a) (b) (c) h_precond = c := by
            rw [minOfThree]
            <;> simp_all
            <;> omega
          rw [h₃]
          simp_all
          <;> tauto
  exact h_main
  -- !benchmark @end proof
