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
  have h_main : (ComputeIsEven x h_precond = true) ↔ ∃ (k : Int), x = 2 * k := by
    unfold ComputeIsEven
    simp [h_precond]
    constructor
    · -- Prove the forward direction: (x % 2 = 0) → ∃ k, x = 2 * k
      intro h
      use x / 2
      have h₁ : x % 2 = 0 := by simpa using h
      have h₂ : x = 2 * (x / 2) := by
        have h₃ := Int.emod_add_ediv x 2
        omega
      linarith
    · -- Prove the backward direction: (∃ k, x = 2 * k) → (x % 2 = 0)
      rintro ⟨k, hk⟩
      have h₁ : x % 2 = 0 := by
        rw [hk]
        norm_num
        <;>
        (try omega) <;>
        (try simp [Int.mul_emod, Int.add_emod, Int.emod_emod]) <;>
        omega
      simp_all
      <;>
      omega

  simp_all [ComputeIsEven_postcond]
  <;>
  aesop
  -- !benchmark @end proof
