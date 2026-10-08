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
  have h_main : (ComputeIsEven x h_precond = true) ↔ (∃ (k : Int), x = 2 * k) := by
    simp only [ComputeIsEven, ComputeIsEven_precond, true_and]
    constructor
    · -- Prove the forward direction: if ComputeIsEven x h_precond = true, then ∃ k : ℤ, x = 2 * k
      intro h
      have h₁ : x % 2 = 0 := by
        by_cases h₂ : x % 2 = 0 <;> simp_all [if_pos, if_neg] <;> omega
      -- Since x % 2 = 0, x is even
      have h₂ : ∃ (k : Int), x = 2 * k := by
        use x / 2
        have h₃ : x % 2 = 0 := h₁
        have h₄ : x = 2 * (x / 2) := by
          have h₅ := Int.emod_add_ediv x 2
          omega
        omega
      exact h₂
    · -- Prove the backward direction: if ∃ k : ℤ, x = 2 * k, then ComputeIsEven x h_precond = true
      rintro ⟨k, hk⟩
      have h₁ : x % 2 = 0 := by
        have h₂ : x = 2 * k := hk
        rw [h₂]
        simp [Int.mul_emod, Int.emod_emod]
        <;> ring_nf <;> omega
      -- Since x % 2 = 0, ComputeIsEven x h_precond = true
      simp_all [if_pos, if_neg]
      <;> omega
  -- Use the main result to prove the postcondition
  simp_all [ComputeIsEven_postcond]
  <;> aesop
  -- !benchmark @end proof
