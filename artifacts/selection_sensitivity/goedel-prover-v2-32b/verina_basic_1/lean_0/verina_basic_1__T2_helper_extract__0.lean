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
  have h_main : (((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → (a * b < 0)) ∧ (¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) → ¬(a * b < 0)) := by
    constructor
    · -- Prove the first direction: if (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0), then a * b < 0
      intro h
      cases h with
      | inl h =>
        -- Case: a < 0 ∧ b > 0
        have h₁ : a < 0 := h.1
        have h₂ : b > 0 := h.2
        have h₃ : a * b < 0 := by
          nlinarith
        exact h₃
      | inr h =>
        -- Case: a > 0 ∧ b < 0
        have h₁ : a > 0 := h.1
        have h₂ : b < 0 := h.2
        have h₃ : a * b < 0 := by
          nlinarith
        exact h₃
    · -- Prove the second direction: if ¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)), then ¬(a * b < 0)
      intro h
      by_contra h₁
      -- Assume a * b < 0 and derive a contradiction
      have h₂ : a * b < 0 := by
        exact h₁
      -- Since a * b < 0, one of a or b is positive and the other is negative
      have h₃ : (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0) := by
        by_cases h₄ : a > 0
        · -- Case: a > 0
          have h₅ : b < 0 := by
            by_contra h₅
            -- If b ≥ 0, then a * b ≥ 0, contradicting a * b < 0
            have h₆ : b ≥ 0 := by linarith
            have h₇ : a * b ≥ 0 := by nlinarith
            linarith
          exact Or.inr ⟨h₄, h₅⟩
        · -- Case: a ≤ 0
          by_cases h₅ : a < 0
          · -- Subcase: a < 0
            have h₆ : b > 0 := by
              by_contra h₆
              -- If b ≤ 0, then a * b ≥ 0, contradicting a * b < 0
              have h₇ : b ≤ 0 := by linarith
              have h₈ : a * b ≥ 0 := by nlinarith
              linarith
            exact Or.inl ⟨h₅, h₆⟩
          · -- Subcase: a = 0
            have h₆ : a = 0 := by
              linarith
            rw [h₆] at h₂
            norm_num at h₂ ⊢
            <;> simp_all
            <;> linarith
      -- Contradiction with the assumption ¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0))
      exact h h₃
  -- Simplify the goal using the main result and definitions
  simp_all [hasOppositeSign_precond, hasOppositeSign, hasOppositeSign_postcond]
  <;>
  (try tauto) <;>
  (try norm_num) <;>
  (try aesop)
  -- !benchmark @end proof
