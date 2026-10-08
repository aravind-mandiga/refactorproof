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
    dsimp only [maxOfThree_precond, maxOfThree_postcond, maxOfThree] at *
    split_ifs <;>
    (try { contradiction }) <;>
    (try {
      -- Case 1: a ≥ b ∧ a ≥ c
      constructor
      · -- Prove result ≥ a, result ≥ b, result ≥ c
        constructor <;>
        (try { linarith }) <;>
        (try { omega }) <;>
        (try {
          simp_all [Int.le_of_lt]
          <;> omega
        })
      · -- Prove result = a ∨ result = b ∨ result = c
        simp_all [Int.le_of_lt]
        <;> omega
    }) <;>
    (try {
      -- Case 2: ¬(a ≥ b ∧ a ≥ c) ∧ (b ≥ a ∧ b ≥ c)
      constructor
      · -- Prove result ≥ a, result ≥ b, result ≥ c
        constructor <;>
        (try { linarith }) <;>
        (try { omega }) <;>
        (try {
          simp_all [Int.le_of_lt]
          <;> omega
        })
      · -- Prove result = a ∨ result = b ∨ result = c
        simp_all [Int.le_of_lt]
        <;> omega
    }) <;>
    (try {
      -- Case 3: ¬(a ≥ b ∧ a ≥ c) ∧ ¬(b ≥ a ∧ b ≥ c)
      have h₁ : c ≥ a := by
        by_contra h
        have h₂ : c < a := by linarith
        have h₃ : a < b := by
          by_cases h₄ : a ≥ b
          · -- Subcase: a ≥ b
            have h₅ : ¬(a ≥ b ∧ a ≥ c) := by tauto
            have h₆ : a ≥ c := by
              by_contra h₇
              have h₈ : a < c := by linarith
              have h₉ : a ≥ b := h₄
              have h₁₀ : a ≥ c := by
                by_contra h₁₁
                have h₁₂ : a < c := by linarith
                simp_all [Int.le_of_lt]
                <;> omega
              simp_all [Int.le_of_lt]
              <;> omega
            simp_all [Int.le_of_lt]
            <;> omega
          · -- Subcase: a < b
            linarith
        have h₅ : b ≥ a := by linarith
        have h₆ : b ≥ c := by
          have h₇ : c < a := h₂
          have h₈ : a < b := h₃
          linarith
        simp_all [Int.le_of_lt]
        <;> omega
      have h₂ : c ≥ b := by
        by_contra h
        have h₃ : c < b := by linarith
        have h₄ : b < a := by
          by_cases h₅ : b ≥ a
          · -- Subcase: b ≥ a
            have h₆ : ¬(b ≥ a ∧ b ≥ c) := by tauto
            have h₇ : b ≥ c := by
              by_contra h₈
              have h₉ : b < c := by linarith
              have h₁₀ : b ≥ a := h₅
              have h₁₁ : b ≥ c := by
                by_contra h₁₂
                have h₁₃ : b < c := by linarith
                simp_all [Int.le_of_lt]
                <;> omega
              simp_all [Int.le_of_lt]
              <;> omega
            simp_all [Int.le_of_lt]
            <;> omega
          · -- Subcase: b < a
            linarith
        have h₅ : a ≥ b := by linarith
        have h₆ : a ≥ c := by
          have h₇ : c < b := h₃
          have h₈ : b < a := h₄
          linarith
        simp_all [Int.le_of_lt]
        <;> omega
      constructor
      · -- Prove result ≥ a, result ≥ b, result ≥ c
        constructor <;>
        (try { linarith }) <;>
        (try { omega }) <;>
        (try {
          simp_all [Int.le_of_lt]
          <;> omega
        })
      · -- Prove result = a ∨ result = b ∨ result = c
        simp_all [Int.le_of_lt]
        <;> omega
    })
  exact h_main
  -- !benchmark @end proof


