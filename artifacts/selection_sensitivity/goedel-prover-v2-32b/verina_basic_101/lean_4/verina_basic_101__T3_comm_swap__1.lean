-- !benchmark @start import type=solution

import Aesop
import Mathlib
-- !benchmark @end import

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def Triple_precond (x : Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  let y := x * 2
  x + y
  -- !benchmark @end code


-- !benchmark @start postcond_aux

-- !benchmark @end postcond_aux


@[reducible, simp]
def Triple_postcond (x : Int) (result: Int) (h_precond : Triple_precond (x)) :=
  -- !benchmark @start postcond
  result / 3 = x ∧ result / 3 * 3 = result
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem Triple_spec_satisfied (x: Int) (h_precond : Triple_precond (x)) :
    Triple_postcond (x) (Triple (x) h_precond) h_precond := by
  -- !benchmark @start proof
  have h_main : Triple (x) h_precond = 3 * x := by
    dsimp [Triple]
    <;> ring_nf
    <;> simp_all
    <;> linarith

  have h_div : (3 * x : Int) / 3 = x := by
    have h₁ : (3 : Int) * x / 3 = x := by
      apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : Int) ≠ 0)
      <;> ring_nf
      <;> norm_num
      <;> linarith
    exact h₁

  have h_mul : ((3 * x : Int) / 3) * 3 = 3 * x := by
    have h₁ : (3 * x : Int) / 3 = x := h_div
    rw [h₁]
    <;> ring_nf
    <;> simp_all
    <;> linarith

  have h_final : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    have h₁ : Triple (x) h_precond = 3 * x := h_main
    have h₂ : (3 * x : Int) / 3 = x := h_div
    have h₃ : ((3 * x : Int) / 3) * 3 = 3 * x := h_mul
    dsimp [Triple_postcond] at *
    constructor
    · -- Prove that (Triple x) / 3 = x
      have h₄ : (Triple (x) h_precond : Int) / 3 = x := by
        rw [h₁]
        <;>
        (try norm_num) <;>
        (try ring_nf at *) <;>
        (try simp_all) <;>
        (try omega)
        <;>
        (try
          {
            have h₅ : (3 * x : Int) / 3 = x := h_div
            omega
          })
      exact h₄
    · -- Prove that ((Triple x) / 3) * 3 = Triple x
      have h₄ : ((Triple (x) h_precond : Int) / 3) * 3 = Triple (x) h_precond := by
        rw [h₁]
        <;>
        (try norm_num) <;>
        (try ring_nf at *) <;>
        (try simp_all) <;>
        (try omega)
        <;>
        (try
          {
            have h₅ : ((3 * x : Int) / 3) * 3 = 3 * x := h_mul
            omega
          })
      exact h₄

  exact h_final
  -- !benchmark @end proof
