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

private def ComputeIsEven__rp_helper_c370e361 (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  if x % 2 = 0 then true else false
-- !benchmark @end code_aux


def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  -- !benchmark @start code
  ComputeIsEven__rp_helper_c370e361 x h_precond
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
  have h_main : (ComputeIsEven (x) h_precond = true) ↔ ∃ (k : ℤ), x = 2 * k := by
    constructor
    · -- Prove the forward direction: if ComputeIsEven (x) h_precond = true, then ∃ k : ℤ, x = 2 * k
      intro h
      have h₁ : x % 2 = 0 := by
        -- Since ComputeIsEven (x) h_precond = true, we have x % 2 = 0
        have h₂ : ComputeIsEven (x) h_precond = true := h
        have h₃ : ComputeIsEven (x) h_precond = if x % 2 = 0 then true else false := rfl
        rw [h₃] at h₂
        split_ifs at h₂ <;> simp_all (config := {decide := true})
      -- Now we have x % 2 = 0, so we can find an integer k such that x = 2 * k
      have h₂ : ∃ (k : ℤ), x = 2 * k := by
        use x / 2
        have h₃ : x % 2 = 0 := h₁
        have h₄ : x = 2 * (x / 2) := by
          have h₅ : x = 2 * (x / 2) + (x % 2) := by
            omega
          rw [h₃] at h₅
          linarith
        exact h₄
      exact h₂
    · -- Prove the reverse direction: if ∃ k : ℤ, x = 2 * k, then ComputeIsEven (x) h_precond = true
      intro h
      have h₁ : x % 2 = 0 := by
        -- Since x = 2 * k for some integer k, we have x % 2 = 0
        obtain ⟨k, hk⟩ := h
        have h₂ : x = 2 * k := hk
        rw [h₂]
        have h₃ : (2 * k : ℤ) % 2 = 0 := by
          omega
        exact h₃
      -- Now we have x % 2 = 0, so ComputeIsEven (x) h_precond = true
      have h₂ : ComputeIsEven (x) h_precond = true := by
        have h₃ : ComputeIsEven (x) h_precond = if x % 2 = 0 then true else false := rfl
        rw [h₃]
        split_ifs <;> simp_all (config := {decide := true})
      exact h₂
  -- Now we can conclude the proof
  simpa [ComputeIsEven_postcond, h_main] using h_main
  -- !benchmark @end proof
