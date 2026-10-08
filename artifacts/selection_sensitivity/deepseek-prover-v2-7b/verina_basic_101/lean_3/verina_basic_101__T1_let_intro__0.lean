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
  have h_main : Triple (x) h_precond = 3 * x := by
    have h₁ : Triple (x) h_precond = (x * 2) + x := by
      rfl
    rw [h₁]
    <;> ring
    <;> simp_all [Triple_precond]
    <;> aesop

  have h_first : (Triple (x) h_precond) / 3 = x := by
    rw [h_main]
    <;>
    (try omega) <;>
    (try
      {
        -- Use the property of integer division to prove that (3 * x) / 3 = x
        have h := Int.emod_add_ediv (3 * x) 3
        have h₁ : (3 * x) % 3 = 0 := by
          norm_num [Int.mul_emod]
        omega
      }) <;>
    (try
      {
        -- Use the property of integer division to prove that (3 * x) / 3 = x
        have h := Int.emod_add_ediv (3 * x) 3
        have h₁ : (3 * x) % 3 = 0 := by
          norm_num [Int.mul_emod]
        omega
      })
    <;>
    (try omega)
    <;>
    (try
      {
        simp_all [Int.mul_emod]
        <;>
        omega
      })
    <;>
    (try
      {
        ring_nf at *
        <;>
        omega
      })
    <;>
    (try
      {
        norm_num at *
        <;>
        omega
      })
    <;>
    aesop

  have h_second : (Triple (x) h_precond) / 3 * 3 = (Triple (x) h_precond) := by
    rw [h_main] at *
    <;>
    (try omega) <;>
    (try
      {
        have h := Int.emod_add_ediv (3 * x) 3
        have h₁ : (3 * x) % 3 = 0 := by
          norm_num [Int.mul_emod]
        omega
      }) <;>
    (try
      {
        simp_all [Int.mul_emod]
        <;>
        omega
      })
    <;>
    (try
      {
        ring_nf at *
        <;>
        omega
      })
    <;>
    (try
      {
        norm_num at *
        <;>
        omega
      })
    <;>
    aesop

  constructor <;> simp_all [Triple_postcond]
  <;>
  (try omega) <;>
  (try
    {
      have h := Int.emod_add_ediv (3 * x) 3
      have h₁ : (3 * x) % 3 = 0 := by
        norm_num [Int.mul_emod]
      omega
    }) <;>
  (try
    {
      aesop
    }) <;>
  (try
    {
      ring_nf at *
      <;>
      omega
    }) <;>
  (try
    {
      norm_num at *
      <;>
      omega
    })
  -- !benchmark @end proof
