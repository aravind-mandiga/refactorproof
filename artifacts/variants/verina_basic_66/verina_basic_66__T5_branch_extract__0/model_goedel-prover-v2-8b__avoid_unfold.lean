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
  have h_main : ((if x % 2 = 0 then true else false) = true) ↔ (∃ (k : Int), x = 2 * k) := by
    constructor
    · -- Prove the forward direction: if (if x % 2 = 0 then true else false) = true, then ∃ k : Int, x = 2 * k
      intro h
      have h₁ : x % 2 = 0 := by
        by_contra h₂
        -- If x % 2 ≠ 0, then (if x % 2 = 0 then true else false) = false, contradicting h
        have h₃ : x % 2 ≠ 0 := h₂
        have h₄ : (if x % 2 = 0 then true else false) = false := by
          simp [h₃, Bool.eq_false_iff]
        rw [h₄] at h
        contradiction
      -- Now we know x % 2 = 0, so we can find k such that x = 2 * k
      have h₂ : ∃ (k : Int), x = 2 * k := by
        use x / 2
        have h₃ : x = 2 * (x / 2) + x % 2 := by
          have h₄ := Int.emod_add_ediv x 2
          omega
        rw [h₁] at h₃
        omega
      exact h₂
    · -- Prove the backward direction: if ∃ k : Int, x = 2 * k, then (if x % 2 = 0 then true else false) = true
      intro h
      have h₁ : x % 2 = 0 := by
        obtain ⟨k, hk⟩ := h
        have h₂ : x = 2 * k := hk
        have h₃ : x % 2 = 0 := by
          rw [h₂]
          have h₄ : (2 * k : ℤ) % 2 = 0 := by
            simp [Int.mul_emod, Int.emod_emod]
          exact h₄
        exact h₃
      have h₂ : (if x % 2 = 0 then true else false) = true := by
        simp [h₁]
      exact h₂

  have h_final : ComputeIsEven_postcond (x) (ComputeIsEven (x) h_precond) h_precond := by
    dsimp [ComputeIsEven_postcond] at *
    have h₁ : ComputeIsEven (x) h_precond = (if x % 2 = 0 then true else false) := rfl
    rw [h₁]
    have h₂ : ((if x % 2 = 0 then true else false) = true) ↔ (∃ (k : Int), x = 2 * k) := h_main
    have h₃ : ((if x % 2 = 0 then true else false) = true) ↔ ((if x % 2 = 0 then true else false) = true) := by simp
    simp_all [h_main]
    <;>
    (try omega) <;>
    (try ring_nf at *) <;>
    (try norm_num) <;>
    (try aesop) <;>
    (try omega)
    <;>
    (try
      {
        aesop
      })
    <;>
    (try
      {
        omega
      })

  exact h_final
  -- !benchmark @end proof
