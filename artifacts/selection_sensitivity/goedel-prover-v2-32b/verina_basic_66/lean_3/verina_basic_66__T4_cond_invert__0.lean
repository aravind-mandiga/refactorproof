-- !benchmark @start import type=solution
import Mathlib
import Aesop
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def ComputeIsEven_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  -- !benchmark @start code
  if ¬ (x % 2 = 0) then false
  else true
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def ComputeIsEven_postcond (x : Int) (result: Bool) (h_precond : ComputeIsEven_precond (x)) :=
  -- !benchmark @start postcond
  result = true ↔ ∃ k : Int, x = 2 * k
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem ComputeIsEven_spec_satisfied (x: Int) (h_precond : ComputeIsEven_precond (x)) :
    ComputeIsEven_postcond (x) (ComputeIsEven (x) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : (ComputeIsEven (x) h_precond = true ↔ ∃ k : Int, x = 2 * k) := by
    dsimp [ComputeIsEven, ComputeIsEven_precond] at *
    split_ifs with h
    · -- Case: x % 2 = 0
      constructor
      · -- Prove the forward direction: true = true → ∃ k, x = 2 * k
        intro _
        have h₁ : x % 2 = 0 := h
        have h₂ : ∃ (k : ℤ), x = 2 * k := by
          use x / 2
          have h₃ : x % 2 = 0 := h₁
          have h₄ : x = 2 * (x / 2) := by
            have h₅ := Int.emod_add_ediv x 2
            have h₆ : x % 2 = 0 := h₁
            have h₇ : x = 2 * (x / 2) + (x % 2) := by
              linarith
            rw [h₆] at h₇
            linarith
          linarith
        exact h₂
      · -- Prove the reverse direction: ∃ k, x = 2 * k → true = true
        intro h₁
        simp
    · -- Case: x % 2 ≠ 0
      have h₁ : x % 2 ≠ 0 := by
        intro h₂
        apply h
        <;> simp_all
      have h₂ : x % 2 = 1 := by
        have h₃ : x % 2 = 1 ∨ x % 2 = -1 := by
          have h₄ : x % 2 = 0 ∨ x % 2 = 1 ∨ x % 2 = -1 := by
            have : x % 2 = 0 ∨ x % 2 = 1 ∨ x % 2 = -1 := by
              have h₅ : x % 2 = 0 ∨ x % 2 = 1 ∨ x % 2 = -1 := by
                omega
              exact h₅
            exact this
          rcases h₄ with (h₄ | h₄ | h₄)
          · exfalso
            apply h₁
            <;> simp_all
          · exact Or.inl h₄
          · exact Or.inr h₄
        rcases h₃ with (h₃ | h₃)
        · exact h₃
        · -- If x % 2 = -1, adjust it to 1
          have h₄ : x % 2 = 1 := by
            have h₅ : x % 2 = -1 := h₃
            have h₆ : x % 2 = 1 := by
              omega
            exact h₆
          exact h₄
      constructor
      · -- Prove the forward direction: false = true → ∃ k, x = 2 * k (vacuously true)
        intro h₃
        exfalso
        simp_all
      · -- Prove the reverse direction: ∃ k, x = 2 * k → false = true
        intro h₃
        rcases h₃ with ⟨k, h₃⟩
        have h₄ : x % 2 = 0 := by
          have h₅ : x = 2 * k := h₃
          have h₆ : x % 2 = (2 * k) % 2 := by rw [h₅]
          have h₇ : (2 * k : ℤ) % 2 = 0 := by
            have h₈ : (2 * k : ℤ) % 2 = 0 := by
              omega
            exact h₈
          omega
        omega

  simpa [ComputeIsEven_postcond, ComputeIsEven_precond] using h_main
  -- !benchmark @end proof
