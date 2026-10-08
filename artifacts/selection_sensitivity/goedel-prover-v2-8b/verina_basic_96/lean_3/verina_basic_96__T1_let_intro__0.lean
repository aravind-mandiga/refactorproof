-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SwapSimultaneous_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def SwapSimultaneous (X : Int) (Y : Int) (h_precond : SwapSimultaneous_precond (X) (Y)) : Int × Int :=
  -- !benchmark @start code
  let __rp_tmp_582430c5 : Int × Int :=
    (Y, X)
  __rp_tmp_582430c5
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SwapSimultaneous_postcond (X : Int) (Y : Int) (result: Int × Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SwapSimultaneous_spec_satisfied (X: Int) (Y: Int) (h_precond : SwapSimultaneous_precond (X) (Y)) :
    SwapSimultaneous_postcond (X) (Y) (SwapSimultaneous (X) (Y) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : SwapSimultaneous_postcond (X) (Y) (SwapSimultaneous (X) (Y) h_precond) h_precond := by
    have h₁ : SwapSimultaneous (X) (Y) h_precond = (Y, X) := by
      rfl
    rw [h₁]
    have h₂ : SwapSimultaneous_postcond (X) (Y) ((Y, X)) h_precond := by
      constructor
      · -- Prove that (Y, X).1 = Y
        rfl
      constructor
      · -- Prove that (Y, X).2 = X
        rfl
      · -- Prove that if X ≠ Y, then (Y, X).1 ≠ X and (Y, X).2 ≠ Y
        intro h
        constructor
        · -- Prove that (Y, X).1 ≠ X
          intro h₃
          have h₄ : Y = X := by simp_all [Prod.fst]
          have h₅ : X ≠ Y := by tauto
          tauto
        · -- Prove that (Y, X).2 ≠ Y
          intro h₃
          have h₄ : X = Y := by simp_all [Prod.snd]
          have h₅ : X ≠ Y := by tauto
          tauto
    exact h₂
  exact h_main
  -- !benchmark @end proof
