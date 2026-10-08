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
  let __rp_tmp_6cb292eb : Bool :=
    if x % 2 = 0 then true else false
  __rp_tmp_6cb292eb
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
  unfold ComputeIsEven ComputeIsEven_postcond
  have h_main : (if x % 2 = 0 then true else false) = true ↔ ∃ k : Int, x = 2 * k := by
    constructor
    · -- Prove the forward direction: if (if x % 2 = 0 then true else false) = true, then ∃ k : Int, x = 2 * k
      intro h
      have h₁ : x % 2 = 0 := by
        by_contra h₁
        -- If x % 2 ≠ 0, then (if x % 2 = 0 then true else false) = false
        simp [h₁] at h
        <;> simp_all (config := {decide := true})
        <;> aesop
      -- Since x % 2 = 0, x is even
      use x / 2
      have h₂ : x = 2 * (x / 2) := by
        have h₃ := Int.emod_add_ediv x 2
        omega
      linarith
    · -- Prove the backward direction: if ∃ k : Int, x = 2 * k, then (if x % 2 = 0 then true else false) = true
      rintro ⟨k, hk⟩
      have h₁ : x % 2 = 0 := by
        have h₂ : x = 2 * k := by omega
        rw [h₂]
        simp [Int.mul_emod, Int.emod_emod]
        <;> omega
      -- Since x % 2 = 0, the condition (if x % 2 = 0 then true else false) = true
      simp [h₁]
      <;> aesop
  -- Use the main equivalence to complete the proof
  simp_all [ComputeIsEven, ComputeIsEven_precond, ComputeIsEven_postcond]
  <;> aesop
  -- !benchmark @end proof
