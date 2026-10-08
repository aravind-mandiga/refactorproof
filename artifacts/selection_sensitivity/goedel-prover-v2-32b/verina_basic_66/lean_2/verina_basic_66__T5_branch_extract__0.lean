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
  have h_main : (x % 2 = 0) ↔ (∃ (k : Int), x = 2 * k) := by
    constructor
    · -- Prove the forward direction: if x % 2 = 0, then there exists k such that x = 2 * k
      intro h
      have h₁ : x % 2 = 0 := h
      have h₂ : x = 2 * (x / 2) := by
        have h₃ := Int.emod_add_ediv x 2
        have h₄ : x % 2 = 0 := h₁
        omega
      refine' ⟨x / 2, _⟩
      linarith
    · -- Prove the backward direction: if there exists k such that x = 2 * k, then x % 2 = 0
      intro h
      obtain ⟨k, hk⟩ := h
      have h₁ : x % 2 = 0 := by
        have h₂ : x = 2 * k := hk
        rw [h₂]
        have h₃ : (2 * k : Int) % 2 = 0 := by
          have h₄ : (2 : Int) % 2 = 0 := by norm_num
          have h₅ : (2 * k : Int) % 2 = 0 := by
            simp [Int.mul_emod, h₄]
          exact h₅
        exact h₃
      exact h₁

  have h_final : ComputeIsEven_postcond x (ComputeIsEven x h_precond) h_precond := by
    dsimp only [ComputeIsEven_postcond, ComputeIsEven, ComputeIsEven_precond] at *
    split_ifs at * <;> simp_all (config := {decide := true})
    <;>
    (try omega) <;>
    (try {
      constructor <;> intro h <;>
      (try {
        simp_all [h_main]
        <;>
        (try omega)
      }) <;>
      (try {
        aesop
      })
    }) <;>
    (try {
      cases' h_main with h_main_left h_main_right
      <;>
      (try {
        simp_all
        <;>
        (try omega)
      })
    })

  exact h_final
  -- !benchmark @end proof
