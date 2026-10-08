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
  unfold ComputeIsEven ComputeIsEven_postcond
  have h_main : ComputeIsEven x h_precond = true ↔ ∃ (k : Int), x = 2 * k := by
    dsimp [ComputeIsEven, ComputeIsEven_precond]
    constructor
    · -- Prove the forward direction: if x % 2 = 0, then ∃ k, x = 2 * k
      intro h
      have h1 : x % 2 = 0 := by simpa using h
      have h2 : ∃ (k : Int), x = 2 * k := by
        use x / 2
        have h3 : x % 2 = 0 := h1
        have h4 : x = 2 * (x / 2) := by
          have h5 := Int.emod_add_ediv x 2
          omega
        linarith
      exact h2
    · -- Prove the backward direction: if ∃ k, x = 2 * k, then x % 2 = 0
      intro h
      rcases h with ⟨k, hk⟩
      have h1 : x % 2 = 0 := by
        have h2 : x = 2 * k := hk
        rw [h2]
        simp [Int.mul_emod]
        <;> norm_num
        <;> omega
      simpa [h1] using h1

  simp_all [ComputeIsEven_postcond]
  <;> aesop
  -- !benchmark @end proof
