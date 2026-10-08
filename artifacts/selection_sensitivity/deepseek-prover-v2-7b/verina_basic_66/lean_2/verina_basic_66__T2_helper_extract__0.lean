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
  have h_main : (ComputeIsEven x h_precond = true) ↔ ∃ (k : Int), x = 2 * k := by
    dsimp only [ComputeIsEven, ComputeIsEven_precond, ComputeIsEven_postcond]
    constructor
    · -- Forward direction: if ComputeIsEven x h_precond = true, then ∃ (k : ℤ), x = 2 * k
      intro h
      have h₁ : x % 2 = 0 := by
        simp_all [Bool.and_comm]
        <;> split <;> simp_all (config := { contextual := true }) [Int.emod_eq_emod_iff_emod_sub_eq_zero]
        <;> omega
      -- Since x % 2 = 0, x is even, so x = 2 * k for some integer k
      use x / 2
      have h₂ : x % 2 = 0 := h₁
      omega
    · -- Reverse direction: if ∃ (k : ℤ), x = 2 * k, then ComputeIsEven x h_precond = true
      rintro ⟨k, hk⟩
      have h₁ : x % 2 = 0 := by
        rw [hk]
        simp [Int.mul_emod, Int.emod_emod]
        <;> omega
      -- If x % 2 = 0, then ComputeIsEven x h_precond = true
      simp_all [Bool.and_comm]
      <;> split <;> simp_all (config := { contextual := true }) [Int.emod_eq_emod_iff_emod_sub_eq_zero]
      <;> omega
  -- Apply the main result to complete the proof
  simpa [h_main] using h_main
  -- !benchmark @end proof
