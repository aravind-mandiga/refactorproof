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
  let __rp_tmp_8c14b1b6 : Bool :=
    a * b < 0
  __rp_tmp_8c14b1b6
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
lemma product_neg_iff_opp_signs {a b : Int} : a * b < 0 → (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0) := by
  intro h
  have h₁ : a ≠ 0 := by
    by_contra h₁
    rw [h₁] at h
    norm_num at h ⊢
    <;> linarith
  have h₂ : b ≠ 0 := by
    by_contra h₂
    rw [h₂] at h
    norm_num at h ⊢
    <;> linarith
  -- Now we know a and b are non-zero, so we can check their signs
  have h₃ : a > 0 ∨ a < 0 := by
    cases' lt_or_gt_of_ne h₁ with h₃ h₃
    · exact Or.inr h₃
    · exact Or.inl h₃
  cases' h₃ with h₃ h₃
  · -- Case: a > 0
    have h₄ : b < 0 := by
      by_contra h₄
      -- If b ≥ 0, then a * b ≥ 0, contradicting h
      have h₅ : b ≥ 0 := by linarith
      have h₆ : a * b ≥ 0 := by
        nlinarith
      linarith
    exact Or.inr ⟨h₃, h₄⟩
  · -- Case: a < 0
    have h₄ : b > 0 := by
      by_contra h₄
      -- If b ≤ 0, then a * b ≥ 0, contradicting h
      have h₅ : b ≤ 0 := by linarith
      have h₆ : a * b ≥ 0 := by
        nlinarith
      linarith
    exact Or.inl ⟨h₃, h₄⟩
-- !benchmark @end proof_aux


theorem hasOppositeSign_spec_satisfied (a: Int) (b: Int) (h_precond : hasOppositeSign_precond (a) (b)) :
    hasOppositeSign_postcond (a) (b) (hasOppositeSign (a) (b) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : hasOppositeSign_postcond (a) (b) (hasOppositeSign (a) (b) h_precond) h_precond := by
    dsimp [hasOppositeSign, hasOppositeSign_postcond]
    constructor
    · -- Prove the first part: if (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0), then a * b < 0
      intro h
      cases' h with h h
      · -- Case: a < 0 ∧ b > 0
        have h₁ : a < 0 := h.1
        have h₂ : b > 0 := h.2
        have h₃ : a * b < 0 := by
          nlinarith
        exact by
          simp_all [h_precond]
          <;>
          (try decide) <;>
          (try omega) <;>
          (try nlinarith)
      · -- Case: a > 0 ∧ b < 0
        have h₁ : a > 0 := h.1
        have h₂ : b < 0 := h.2
        have h₃ : a * b < 0 := by
          nlinarith
        exact by
          simp_all [h_precond]
          <;>
          (try decide) <;>
          (try omega) <;>
          (try nlinarith)
    · -- Prove the second part: if ¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)), then ¬(a * b < 0)
      intro h
      have h₁ : ¬((a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0)) := h
      have h₂ : ¬(a * b < 0) := by
        by_contra h₃
        -- If a * b < 0, then (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0), which contradicts h₁
        have h₄ : (a < 0 ∧ b > 0) ∨ (a > 0 ∧ b < 0) := product_neg_iff_opp_signs h₃
        contradiction
      simp_all [h_precond]
      <;>
      (try decide) <;>
      (try omega) <;>
      (try nlinarith)
  exact h_main
  -- !benchmark @end proof
