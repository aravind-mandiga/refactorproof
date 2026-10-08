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

private def ComputeIsEven__rp_branch_87fb4e70 (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  false
-- !benchmark @end code_aux


def ComputeIsEven (x : Int) (h_precond : ComputeIsEven_precond (x)) : Bool :=
  -- !benchmark @start code
  if x % 2 = 0 then true else
    ComputeIsEven__rp_branch_87fb4e70 x h_precond
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
  have h_main : (ComputeIsEven x h_precond = true ↔ ∃ (k : ℤ), x = 2 * k) := by
    dsimp [ComputeIsEven, ComputeIsEven_precond] at *
    constructor
    · -- Prove the forward direction: if ComputeIsEven x _ = true, then ∃ k, x = 2 * k
      intro h
      have h₁ : x % 2 = 0 := by
        simp_all [if_pos, if_neg]
        <;> omega
      -- Since x % 2 = 0, we can write x as 2 * k where k = x / 2
      have h₂ : ∃ (k : ℤ), x = 2 * k := by
        use x / 2
        have h₃ : x % 2 = 0 := h₁
        have h₄ : x = 2 * (x / 2) + (x % 2) := by
          have h₅ := Int.emod_add_ediv x 2
          linarith
        rw [h₃] at h₄
        linarith
      exact h₂
    · -- Prove the backward direction: if ∃ k, x = 2 * k, then ComputeIsEven x _ = true
      intro h
      have h₁ : ∃ (k : ℤ), x = 2 * k := h
      -- If x = 2 * k, then x % 2 = 0
      have h₂ : x % 2 = 0 := by
        obtain ⟨k, hk⟩ := h₁
        have h₃ : x = 2 * k := hk
        have h₄ : x % 2 = 0 := by
          rw [h₃]
          simp [Int.mul_emod, Int.emod_emod]
        exact h₄
      -- Since x % 2 = 0, ComputeIsEven x _ = true
      simp_all [if_pos, if_neg]
      <;> omega

  dsimp [ComputeIsEven_postcond] at *
  exact h_main
  -- !benchmark @end proof
