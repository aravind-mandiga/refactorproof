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
  have h_main : (if x % 2 = 0 then true else false : Bool) = true ↔ ∃ (k : ℤ), x = 2 * k := by
    constructor
    · -- Prove the forward direction: if the boolean is true, then there exists a k such that x = 2 * k
      intro h
      have h₁ : x % 2 = 0 := by
        split_ifs at h <;> simp_all (config := {decide := true})
        <;> try contradiction
        <;> try decide
      -- Use the fact that x % 2 = 0 to find k such that x = 2 * k
      have h₂ : ∃ (k : ℤ), x = 2 * k := by
        use x / 2
        have h₃ : x % 2 = 0 := h₁
        have h₄ : x = 2 * (x / 2) := by
          have h₅ : x % 2 = x - 2 * (x / 2) := by
            have h₆ := Int.emod_add_ediv x 2
            ring_nf at h₆ ⊢
            <;> omega
          omega
        linarith
      exact h₂
    · -- Prove the reverse direction: if there exists a k such that x = 2 * k, then the boolean is true
      intro h
      have h₁ : ∃ (k : ℤ), x = 2 * k := h
      have h₂ : x % 2 = 0 := by
        obtain ⟨k, hk⟩ := h₁
        have h₃ : x = 2 * k := hk
        have h₄ : x % 2 = 0 := by
          rw [h₃]
          simp [Int.mul_emod]
        exact h₄
      -- Since x % 2 = 0, the boolean is true
      split_ifs <;> simp_all (config := {decide := true})
      <;> try contradiction
      <;> try decide

  have h_final : ComputeIsEven_postcond (x) (ComputeIsEven (x) h_precond) h_precond := by
    simp only [ComputeIsEven_postcond, ComputeIsEven] at h_main ⊢
    <;> simp_all [h_precond]
    <;> aesop

  exact h_final
  -- !benchmark @end proof
