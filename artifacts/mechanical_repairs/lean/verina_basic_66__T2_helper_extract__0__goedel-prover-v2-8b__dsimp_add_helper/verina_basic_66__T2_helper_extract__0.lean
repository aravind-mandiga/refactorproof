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
  have h_main : ((ComputeIsEven (x) h_precond) = true ↔ ∃ (k : Int), x = 2 * k) := by
    dsimp [ComputeIsEven, ComputeIsEven__rp_helper_c370e361]
    constructor
    · -- Prove the forward direction: if x % 2 = 0, then ∃ k, x = 2 * k
      intro h
      have h₁ : x % 2 = 0 := by simpa using h
      have h₂ : ∃ (k : Int), x = 2 * k := by
        use x / 2
        have h₃ : x = 2 * (x / 2) := by
          have h₄ : x % 2 = 0 := h₁
          have h₅ : x = 2 * (x / 2) + (x % 2) := by omega
          rw [h₄] at h₅
          omega
        linarith
      simpa using h₂
    · -- Prove the backward direction: if ∃ k, x = 2 * k, then x % 2 = 0
      intro h
      rcases h with ⟨k, rfl⟩
      have h₁ : (2 * k : ℤ) % 2 = 0 := by
        norm_num [Int.mul_emod]
      simpa [h₁] using h₁

  simpa [ComputeIsEven_postcond] using h_main
  -- !benchmark @end proof
