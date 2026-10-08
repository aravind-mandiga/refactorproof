-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def SwapArithmetic_precond (X : Int) (Y : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def SwapArithmetic (X : Int) (Y : Int) (h_precond : SwapArithmetic_precond (X) (Y)) : (Int × Int) :=
  -- !benchmark @start code
  let __rp_tmp_5e3d4b6e : (Int × Int) :=
    let x1 := X
    let y1 := Y
    let x2 := y1 - x1
    let y2 := y1 - x2
    let x3 := y2 + x2
    (x3, y2)
  __rp_tmp_5e3d4b6e
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def SwapArithmetic_postcond (X : Int) (Y : Int) (result: (Int × Int)) (h_precond : SwapArithmetic_precond (X) (Y)) :=
  -- !benchmark @start postcond
  result.1 = Y ∧ result.2 = X ∧
  (X ≠ Y → result.fst ≠ X ∧ result.snd ≠ Y)
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem SwapArithmetic_spec_satisfied (X: Int) (Y: Int) (h_precond : SwapArithmetic_precond (X) (Y)) :
    SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
  -- !benchmark @start proof
  have h1 : (SwapArithmetic (X) (Y) h_precond) = (Y, X) := by
    dsimp [SwapArithmetic, Prod.mk.injEq]
    <;>
    (try decide) <;>
    (try ring_nf) <;>
    (try simp_all [SwapArithmetic_precond]) <;>
    (try norm_num) <;>
    (try ring_nf at *) <;>
    (try omega)
    <;>
    (try
      {
        constructor <;>
        (try decide) <;>
        (try ring_nf) <;>
        (try simp_all [SwapArithmetic_precond]) <;>
        (try norm_num) <;>
        (try ring_nf at *) <;>
        (try omega)
      })

  have h2 : SwapArithmetic_postcond (X) (Y) (SwapArithmetic (X) (Y) h_precond) h_precond := by
    rw [h1]
    constructor
    · -- Prove that the first element of the pair is Y
      rfl
    constructor
    · -- Prove that the second element of the pair is X
      rfl
    · -- Prove the implication about X ≠ Y
      intro h
      constructor
      · -- Prove that the first element of the pair is not X when X ≠ Y
        intro h₁
        apply h
        linarith
      · -- Prove that the second element of the pair is not Y when X ≠ Y
        intro h₁
        apply h
        linarith

  exact h2
  -- !benchmark @end proof
