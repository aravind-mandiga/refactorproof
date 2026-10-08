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
  dsimp only [maxOfThree_precond, maxOfThree_postcond] at *
  have h_main : (maxOfThree a b c h_precond ≥ a ∧ maxOfThree a b c h_precond ≥ b ∧ maxOfThree a b c h_precond ≥ c) ∧ (maxOfThree a b c h_precond = a ∨ maxOfThree a b c h_precond = b ∨ maxOfThree a b c h_precond = c) := by
    have h₁ : maxOfThree a b c h_precond = if a >= b && a >= c then a else if b >= a && b >= c then b else c := by
      rfl
    rw [h₁]
    split_ifs <;>
    (try { contradiction }) <;>
    (try {
      -- Case: a ≥ b ∧ a ≥ c
      constructor
      · -- Prove a ≥ a, a ≥ b, a ≥ c
        constructor <;>
        (try { nlinarith }) <;>
        (try {
          norm_num at *
          <;>
          (try omega)
          <;>
          (try nlinarith)
        }) <;>
        (try {
          simp_all [Int.and_eq_max]
          <;>
          omega
        })
      · -- Prove a is one of a, b, c
        simp
    }) <;>
    (try {
      -- Case: ¬(a ≥ b ∧ a ≥ c) and b ≥ a ∧ b ≥ c
      constructor
      · -- Prove b ≥ a, b ≥ b, b ≥ c
        constructor <;>
        (try { nlinarith }) <;>
        (try {
          norm_num at *
          <;>
          (try omega)
          <;>
          (try nlinarith)
        }) <;>
        (try {
          simp_all [Int.and_eq_max]
          <;>
          omega
        })
      · -- Prove b is one of a, b, c
        simp
    }) <;>
    (try {
      -- Case: ¬(a ≥ b ∧ a ≥ c) and ¬(b ≥ a ∧ b ≥ c)
      have h₂ : (if a >= b && a >= c then a else if b >= a && b >= c then b else c) = c := by
        simp_all [Int.and_eq_max]
        <;>
        (try omega)
        <;>
        (try norm_num)
        <;>
        (try simp_all [Int.and_eq_max])
        <;>
        (try omega)
      have h₃ : c ≥ a := by
        by_cases h₄ : a < c
        · -- Subcase: a < c
          linarith
        · -- Subcase: a ≥ c
          have h₅ : a < b := by
            by_contra h₅
            -- If a ≥ b, then a ≥ b ∧ a ≥ c (since a ≥ c)
            have h₆ : a ≥ b := by linarith
            have h₇ : a >= b && a >= c := by
              simp_all [Int.and_eq_max]
              <;>
              (try omega)
              <;>
              (try norm_num)
              <;>
              (try simp_all [Int.and_eq_max])
              <;>
              (try omega)
            simp_all [Int.and_eq_max]
            <;>
            (try omega)
            <;>
            (try norm_num)
            <;>
            (try simp_all [Int.and_eq_max])
            <;>
            (try omega)
          have h₆ : b < c := by
            by_contra h₆
            -- If b ≥ c, then since a < b, we have b ≥ a ∧ b ≥ c
            have h₇ : b ≥ c := by linarith
            have h₈ : b >= a && b >= c := by
              simp_all [Int.and_eq_max]
              <;>
              (try omega)
              <;>
              (try norm_num)
              <;>
              (try simp_all [Int.and_eq_max])
              <;>
              (try omega)
            simp_all [Int.and_eq_max]
            <;>
            (try omega)
            <;>
            (try norm_num)
            <;>
            (try simp_all [Int.and_eq_max])
            <;>
            (try omega)
          linarith
      have h₄ : c ≥ b := by
        by_cases h₅ : b < c
        · -- Subcase: b < c
          linarith
        · -- Subcase: b ≥ c
          have h₆ : b < a := by
            by_contra h₆
            -- If b ≥ a, then since b ≥ c, we have b ≥ a ∧ b ≥ c
            have h₇ : b ≥ a := by linarith
            have h₈ : b >= a && b >= c := by
              simp_all [Int.and_eq_max]
              <;>
              (try omega)
              <;>
              (try norm_num)
              <;>
              (try simp_all [Int.and_eq_max])
              <;>
              (try omega)
            simp_all [Int.and_eq_max]
            <;>
            (try omega)
            <;>
            (try norm_num)
            <;>
            (try simp_all [Int.and_eq_max])
            <;>
            (try omega)
          have h₇ : a < c := by
            by_contra h₇
            -- If a ≥ c, then since a > b, we have a ≥ b ∧ a ≥ c
            have h₈ : a ≥ c := by linarith
            have h₉ : a >= b && a >= c := by
              have h₁₀ : a ≥ b := by linarith
              simp_all [Int.and_eq_max]
              <;>
              (try omega)
              <;>
              (try norm_num)
              <;>
              (try simp_all [Int.and_eq_max])
              <;>
              (try omega)
            simp_all [Int.and_eq_max]
            <;>
            (try omega)
            <;>
            (try norm_num)
            <;>
            (try simp_all [Int.and_eq_max])
            <;>
            (try omega)
          linarith
      -- Prove c ≥ a, c ≥ b, c ≥ c and c is one of a, b, c
      constructor
      · -- Prove c ≥ a, c ≥ b, c ≥ c
        constructor <;>
        (try { nlinarith }) <;>
        (try {
          norm_num at *
          <;>
          (try omega)
          <;>
          (try nlinarith)
        }) <;>
        (try {
          simp_all [Int.and_eq_max]
          <;>
          omega
        })
      · -- Prove c is one of a, b, c
        simp
    })
  exact h_main
  -- !benchmark @end proof


