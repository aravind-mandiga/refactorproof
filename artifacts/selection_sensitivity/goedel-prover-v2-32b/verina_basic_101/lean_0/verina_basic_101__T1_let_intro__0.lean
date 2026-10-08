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
  let __rp_tmp_1171a237 : Int :=
    let y := x * 2
    y + x
  __rp_tmp_1171a237
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
  have h_triple : Triple x h_precond = 3 * x := by
    dsimp [Triple]
    <;> ring_nf
    <;> simp_all
    <;> linarith

  have h_div : (3 * x) / 3 = x := by
    have h₁ : (3 : ℤ) ≠ 0 := by norm_num
    have h₂ : (3 * x : ℤ) = 3 * x := by ring
    have h₃ : (3 * x : ℤ) / 3 = x := by
      apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
      <;> ring_nf
      <;> linarith
    exact h₃

  have h_main : Triple_postcond x (Triple x h_precond) h_precond := by
    have h₁ : (Triple x h_precond) / 3 = x := by
      rw [h_triple]
      <;>
      (try norm_num) <;>
      (try ring_nf at h_div ⊢) <;>
      (try simp_all [Int.mul_ediv_cancel_left]) <;>
      (try omega) <;>
      (try linarith)
      <;>
      (try
        {
          have h₂ : (3 : ℤ) ≠ 0 := by norm_num
          have h₃ : (3 * x : ℤ) = 3 * x := by ring
          have h₄ : (3 * x : ℤ) / 3 = x := by
            apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
            <;> ring_nf
            <;> linarith
          simp_all
        })
      <;>
      (try
        {
          simp_all [Int.mul_emod, Int.add_emod]
          <;>
          omega
        })
    have h₂ : (Triple x h_precond) / 3 * 3 = Triple x h_precond := by
      rw [h_triple]
      have h₃ : (3 * x : ℤ) / 3 = x := by
        have h₄ : (3 : ℤ) ≠ 0 := by norm_num
        have h₅ : (3 * x : ℤ) = 3 * x := by ring
        have h₆ : (3 * x : ℤ) / 3 = x := by
          apply Int.ediv_eq_of_eq_mul_right (by norm_num : (3 : ℤ) ≠ 0)
          <;> ring_nf
          <;> linarith
        exact h₆
      have h₄ : ((3 * x : ℤ) / 3) * 3 = 3 * x := by
        rw [h₃]
        <;> ring
        <;> linarith
      linarith
    exact ⟨h₁, h₂⟩

  exact h_main
  -- !benchmark @end proof
