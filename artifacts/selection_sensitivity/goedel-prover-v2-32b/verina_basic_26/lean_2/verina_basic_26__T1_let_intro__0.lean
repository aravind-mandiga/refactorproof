-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def isEven_precond (n : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def isEven (n : Int) (h_precond : isEven_precond (n)) : Bool :=
  -- !benchmark @start code
  let __rp_tmp_a74ca03e : Bool :=
    n % 2 == 0
  __rp_tmp_a74ca03e
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def isEven_postcond (n : Int) (result: Bool) (h_precond : isEven_precond (n)) :=
  -- !benchmark @start postcond
  (result → n % 2 = 0) ∧ (¬ result → n % 2 ≠ 0)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem isEven_spec_satisfied (n: Int) (h_precond : isEven_precond (n)) :
    isEven_postcond (n) (isEven (n) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : isEven_postcond (n) (isEven (n) h_precond) h_precond := by
    by_cases h : n % 2 = 0
    · -- Case: n % 2 = 0
      have h₁ : isEven n h_precond = true := by
        -- Prove that isEven n h_precond = true when n % 2 = 0
        simp [isEven, h]
        <;> simp_all [Int.emod_eq_of_lt]
        <;> norm_num
        <;> rfl
      -- Substitute isEven n h_precond = true into the goal
      rw [h₁]
      -- Simplify the goal using the fact that n % 2 = 0
      constructor <;> simp_all [h]
      <;> norm_num
      <;> aesop
    · -- Case: n % 2 ≠ 0
      have h₁ : isEven n h_precond = false := by
        -- Prove that isEven n h_precond = false when n % 2 ≠ 0
        simp [isEven]
        <;>
        (try decide) <;>
        (try
          {
            cases' eq_or_ne (n % 2) 0 with h₂ h₂ <;>
            simp_all [h₂]
            <;>
            (try contradiction)
            <;>
            (try omega)
          }) <;>
        (try omega) <;>
        (try
          {
            simp_all [Int.emod_eq_of_lt]
            <;>
            norm_num at *
            <;>
            (try omega)
          })
        <;>
        (try
          {
            simp_all [Int.emod_eq_of_lt]
            <;>
            norm_num at *
            <;>
            (try omega)
            <;>
            (try
              {
                cases' n with n
                <;>
                simp_all [Int.emod_eq_of_lt]
                <;>
                norm_num at *
                <;>
                omega
              })
          })
      -- Substitute isEven n h_precond = false into the goal
      rw [h₁]
      -- Simplify the goal using the fact that n % 2 ≠ 0
      constructor <;> simp_all
      <;>
      (try
        {
          intro h₂
          apply h
          omega
        })
      <;>
      (try
        {
          intro h₂
          apply h
          omega
        })
      <;>
      (try omega)
  exact h_main
  -- !benchmark @end proof
