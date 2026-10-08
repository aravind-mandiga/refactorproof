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
  have h_result_def : SwapSimultaneous X Y h_precond = (Y, X) := by
    rfl

  have h_main : SwapSimultaneous_postcond X Y (SwapSimultaneous X Y h_precond) h_precond := by
    rw [h_result_def]
    constructor
    · -- Prove (Y, X).1 = Y
      simp
    constructor
    · -- Prove (Y, X).2 = X
      simp
    · -- Prove the implication X ≠ Y → (Y, X).fst ≠ X ∧ (Y, X).snd ≠ Y
      intro h_ne
      constructor
      · -- Prove (Y, X).fst ≠ X
        intro h_eq
        apply h_ne
        -- Since (Y, X).fst = Y, we have Y = X, which contradicts X ≠ Y
        simp_all [Prod.fst]
        <;>
        (try contradiction) <;>
        (try linarith)
      · -- Prove (Y, X).snd ≠ Y
        intro h_eq
        apply h_ne
        -- Since (Y, X).snd = X, we have X = Y, which contradicts X ≠ Y
        simp_all [Prod.snd]
        <;>
        (try contradiction) <;>
        (try linarith)

  exact h_main
  -- !benchmark @end proof
