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

-- !benchmark @end code_aux


def hasOppositeSign (a : Int) (b : Int) (h_precond : hasOppositeSign_precond (a) (b)) : Bool :=
  -- !benchmark @start code
  b * a < 0
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
  unfold hasOppositeSign hasOppositeSign_postcond
  have h_main : hasOppositeSign_postcond a b (hasOppositeSign a b h_precond) h_precond := by
    constructor
    · -- First implication: if (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0), then a * b < 0
      intro h
      -- Consider the two cases of h
      cases h with
      | inl h =>
        -- Case: a < 0 ∧ b > 0
        have h₁ : a < 0 := h.1
        have h₂ : b > 0 := h.2
        have h₃ : a * b < 0 := by
          -- Since a < 0 and b > 0, a * b < 0
          nlinarith [mul_self_nonneg a, mul_self_nonneg b]
        simpa [hasOppositeSign] using h₃
      | inr h =>
        -- Case: a > 0 ∧ b < 0
        have h₁ : a > 0 := h.1
        have h₂ : b < 0 := h.2
        have h₃ : a * b < 0 := by
          -- Since a > 0 and b < 0, a * b < 0
          nlinarith [mul_self_nonneg a, mul_self_nonneg b]
        simpa [hasOppositeSign] using h₃
    · -- Second implication: if ¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)), then not (a * b < 0)
      intro h
      -- Simplify the negation using classical reasoning
      have h₁ : ¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) := h
      have h₂ : ¬(a * b < 0) := by
        intro h₃
        apply h₁
        -- If a * b < 0, then a and b have opposite signs
        have h₄ : (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0) := by
          by_cases h₅ : a > 0
          · -- Case a > 0
            have h₆ : b < 0 := by
              by_contra h₆
              -- If b ≥ 0, then a * b ≥ 0, which contradicts a * b < 0
              have h₇ : b ≥ 0 := by linarith
              have h₈ : a * b ≥ 0 := by nlinarith
              nlinarith
            exact Or.inr ⟨h₅, h₆⟩
          · -- Case a ≤ 0
            have h₅ : a ≤ 0 := by nlinarith
            by_cases h₆ : a < 0
            · -- Case a < 0
              have h₇ : b > 0 := by
                by_contra h₇
                have h₈ : b ≤ 0 := by nlinarith
                have h₉ : a * b ≥ 0 := by
                  have h₁₀ : a * b ≤ 0 := by nlinarith
                  nlinarith
                nlinarith
              exact Or.inl ⟨h₆, h₇⟩
            · -- Case a = 0
              have h₆ : a = 0 := by nlinarith
              rw [h₆] at h₃
              have h₇ : (0 : ℤ) * b < 0 := by simpa [h₆] using h₃
              norm_num at h₇
              <;> simp_all
        exact h₄
      simpa [hasOppositeSign] using h₂
  exact h_main
  -- !benchmark @end proof
