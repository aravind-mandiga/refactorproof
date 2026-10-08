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
  have h_main : SwapSimultaneous (X) (Y) h_precond = (Y, X) := by
    simp [SwapSimultaneous, SwapSimultaneous_precond]
    <;> aesop

  have h_cond₁ : (SwapSimultaneous (X) (Y) h_precond).1 = Y := by
    simp [h_main]
    <;> aesop

  have h_cond₂ : (SwapSimultaneous (X) (Y) h_precond).2 = X := by
    simp [h_main]
    <;> aesop

  have h_cond₃ : X ≠ Y → ((SwapSimultaneous (X) (Y) h_precond).1 ≠ X ∧ (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y) := by
    intro h_xy
    have h₁ : (SwapSimultaneous (X) (Y) h_precond).1 = Y := h_cond₁
    have h₂ : (SwapSimultaneous (X) (Y) h_precond).2 = X := h_cond₂
    constructor
    · -- Prove (SwapSimultaneous (X) (Y) h_precond).1 ≠ X
      simp_all [h_main]
      <;>
      (try omega) <;>
      (try aesop) <;>
      (try
        {
          intro h
          apply h_xy
          omega
        }) <;>
      aesop
    · -- Prove (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y
      simp_all [h_main]
      <;>
      (try omega) <;>
      (try aesop) <;>
      (try
        {
          intro h
          apply h_xy
          omega
        }) <;>
      aesop

  have h_final : SwapSimultaneous_postcond (X) (Y) (SwapSimultaneous (X) (Y) h_precond) h_precond := by
    have h₁ : (SwapSimultaneous (X) (Y) h_precond).1 = Y := h_cond₁
    have h₂ : (SwapSimultaneous (X) (Y) h_precond).2 = X := h_cond₂
    have h₃ : X ≠ Y → ((SwapSimultaneous (X) (Y) h_precond).1 ≠ X ∧ (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y) := h_cond₃
    constructor
    · -- Prove that (SwapSimultaneous (X) (Y) h_precond).1 = Y
      simp_all [SwapSimultaneous_postcond]
      <;> aesop
    constructor
    · -- Prove that (SwapSimultaneous (X) (Y) h_precond).2 = X
      simp_all [SwapSimultaneous_postcond]
      <;> aesop
    · -- Prove that if X ≠ Y, then (SwapSimultaneous (X) (Y) h_precond).1 ≠ X and (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y
      intro h_xy
      have h₄ : (SwapSimultaneous (X) (Y) h_precond).1 ≠ X ∧ (SwapSimultaneous (X) (Y) h_precond).2 ≠ Y := h₃ h_xy
      simp_all [SwapSimultaneous_postcond]
      <;> aesop

  exact h_final
  -- !benchmark @end proof
