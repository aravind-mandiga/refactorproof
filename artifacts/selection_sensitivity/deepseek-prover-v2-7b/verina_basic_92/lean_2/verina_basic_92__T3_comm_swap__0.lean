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
  let x1 := X
  let y1 := Y
  let x2 := y1 - x1
  let y2 := y1 - x2
  let x3 := x2 + y2
  (x3, y2)
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
  have h_main : SwapArithmetic (X) (Y) h_precond = (Y, X) := by
    simp [SwapArithmetic, h_precond]
    <;>
    (try simp_all [SwapArithmetic, SwapArithmetic_precond])
    <;>
    (try aesop)
    <;>
    (try ring_nf)
    <;>
    (try simp_all [Int.add_comm, Int.add_left_comm, Int.add_assoc])
    <;>
    (try aesop)
    <;>
    (try norm_num)
    <;>
    (try omega)
    <;>
    (try rfl)

  have h1 : (SwapArithmetic (X) (Y) h_precond).fst = Y := by
    rw [h_main]
    <;> rfl

  have h2 : (SwapArithmetic (X) (Y) h_precond).snd = X := by
    rw [h_main]
    <;> rfl

  have h3 : X ≠ Y → (SwapArithmetic (X) (Y) h_precond).fst ≠ X ∧ (SwapArithmetic (X) (Y) h_precond).snd ≠ Y := by
    intro h_ne
    have h4 : (SwapArithmetic (X) (Y) h_precond).fst ≠ X := by
      rw [h_main]
      intro h
      apply h_ne
      linarith
    have h5 : (SwapArithmetic (X) (Y) h_precond).snd ≠ Y := by
      rw [h_main]
      intro h
      apply h_ne
      linarith
    exact ⟨h4, h5⟩

  constructor
  · -- Prove (SwapArithmetic (X) (Y) h_precond).fst = Y
    exact h1
  constructor
  · -- Prove (SwapArithmetic (X) (Y) h_precond).snd = X
    exact h2
  · -- Prove X ≠ Y → (SwapArithmetic (X) (Y) h_precond).fst ≠ X ∧ (SwapArithmetic (X) (Y) h_precond).snd ≠ Y
    exact h3
  -- !benchmark @end proof
