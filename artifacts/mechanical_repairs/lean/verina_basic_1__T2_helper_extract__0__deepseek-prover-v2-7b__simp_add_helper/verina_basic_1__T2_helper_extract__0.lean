-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux

@[reducible, simp]
def hasOppositeSign_precond (a : Int) (b : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

private def hasOppositeSign__rp_helper_5272bffb (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  a * b < 0
-- !benchmark @end code_aux


def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  -- !benchmark @start code
  hasOppositeSign__rp_helper_5272bffb a b h_precond
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def hasOppositeSign_postcond (a : Int) (b : Int) (result: Bool) (h_precond : hasOppositeSign_precond (a) (b)) :=
  -- !benchmark @start postcond
  (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → result) ∧
  (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬result)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem hasOppositeSign_spec_satisfied (a: Int) (b: Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    hasOppositeSign_postcond (a) (b) (hasOppositeSign (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main₁ : (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → hasOppositeSign a b h_precond = true) := by
    intro h
    have h₁ : hasOppositeSign a b h_precond = true := by
      cases h with
      | inl h =>
        -- Case: a < 0 and b > 0
        have h₂ : a * b < 0 := by
          nlinarith
        simp_all [hasOppositeSign, h_precond, hasOppositeSign__rp_helper_5272bffb]
        <;> norm_num at * <;>
        (try omega) <;>
        (try omega) <;>
        aesop
      | inr h =>
        -- Case: a > 0 and b < 0
        have h₂ : a * b < 0 := by
          nlinarith
        simp_all [hasOppositeSign, h_precond]
        <;> norm_num at * <;>
        (try omega) <;>
        (try omega) <;>
        aesop
    exact h₁
  have h_main₂ : (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → hasOppositeSign a b h_precond = false) := by
    intro h
    have h₁ : hasOppositeSign a b h_precond = false := by
      have h₂ : hasOppositeSign a b h_precond = false := by
        by_cases h₃ : a < 0 <;> by_cases h₄ : b > 0 <;> by_cases h₅ : a > 0 <;> by_cases h₆ : b < 0 <;>
          simp_all [hasOppositeSign, h_precond, Int.mul_emod]
          <;>
          (try omega) <;>
          (try {
            aesop
          }) <;>
          (try {
            norm_num at *
            <;>
            (try omega) <;>
            (try nlinarith)
          })
        <;>
        (try {
          simp_all
          <;> norm_num <;> nlinarith
        })
        <;>
        (try {
          exfalso
          aesop
        })
        <;>
        (try {
          aesop
        })
        <;>
        (try {
          norm_num at *
          <;> nlinarith
        })
        <;>
        (try {
          aesop
        })
        <;>
        (try {
          omega
        })
      exact h₂
    exact h₁
  constructor
  · -- First condition: if the condition holds, then the result is true
    intro h
    simpa [hasOppositeSign, h_precond] using h_main₁ h
  · -- Second condition: if the condition does not hold, then the result is false
    intro h
    simpa [hasOppositeSign, h_precond] using h_main₂ h
  -- !benchmark @end proof
