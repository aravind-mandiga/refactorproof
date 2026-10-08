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
  let __rp_tmp_d53b48dc : Int :=
    x * 3
  __rp_tmp_d53b48dc
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
  unfold Triple Triple_postcond
  have h_main₁ : (Triple (x) h_precond) / 3 = x := by
    simp [Triple]
    <;> ring_nf
    <;> norm_num
    <;> omega

  have h_main₂ : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    have h₁ : (Triple (x) h_precond) / 3 = x := h_main₁
    have h₂ : ((Triple (x) h_precond) / 3) * 3 = x * 3 := by
      rw [h₁]
      <;> ring
    simp [Triple] at h₂ ⊢
    <;>
    (try omega) <;>
    (try ring_nf at * <;> omega) <;>
    (try
      {
        omega
      }) <;>
    (try
      {
        linarith
      })
    <;>
    omega

  simp_all [Triple_precond, Triple, Triple_postcond]
  <;>
  (try omega) <;>
  (try ring_nf at * <;> omega) <;>
  (try
    {
      aesop
    }) <;>
  (try
    {
      omega
    }) <;>
  (try
    {
      simp_all [Int.mul_emod, Int.add_emod, Int.emod_emod]
      <;> omega
    })
  <;>
  aesop
  -- !benchmark @end proof
