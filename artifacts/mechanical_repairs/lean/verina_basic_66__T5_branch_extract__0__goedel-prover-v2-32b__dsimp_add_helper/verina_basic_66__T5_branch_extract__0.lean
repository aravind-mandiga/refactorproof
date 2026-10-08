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
  have h_main : (if x % 2 = 0 then true else false : Bool) = true ↔ ∃ k : Int, x = 2 * k := by
    constructor
    · -- Prove the forward direction: if the if-then-else evaluates to true, then x is even.
      intro h
      have h₁ : x % 2 = 0 := by
        split_ifs at h <;> simp_all [Bool.not_eq_true]
        <;> norm_num at h ⊢
        <;> omega
      -- Since x % 2 = 0, we can write x = 2 * k for some integer k.
      have h₂ : ∃ k : Int, x = 2 * k := by
        use x / 2
        have h₃ : x % 2 = 0 := h₁
        have h₄ : x = 2 * (x / 2) := by
          have h₅ : x % 2 = 0 := h₁
          have h₆ : x = 2 * (x / 2) + x % 2 := by
            have h₇ := Int.emod_add_ediv x 2
            omega
          rw [h₅] at h₆
          omega
        exact h₄
      exact h₂
    · -- Prove the backward direction: if x is even, then the if-then-else evaluates to true.
      intro h
      have h₁ : ∃ k : Int, x = 2 * k := h
      -- Since x is even, x % 2 = 0.
      have h₂ : x % 2 = 0 := by
        obtain ⟨k, hk⟩ := h₁
        have h₃ : x = 2 * k := hk
        rw [h₃]
        have h₄ : (2 * k : Int) % 2 = 0 := by
          have h₅ : (2 * k : Int) % 2 = 0 := by
            simp [Int.mul_emod, Int.emod_emod]
          exact h₅
        exact h₄
      -- Therefore, the if-then-else evaluates to true.
      have h₃ : (if x % 2 = 0 then true else false : Bool) = true := by
        split_ifs <;> simp_all
        <;> norm_num
        <;> omega
      exact h₃

  -- Simplify the goal using the main lemma and the definition of ComputeIsEven.
  dsimp [ComputeIsEven_postcond, ComputeIsEven, ComputeIsEven__rp_branch_87fb4e70] at *
  <;> simp_all
  <;> aesop
  -- !benchmark @end proof
