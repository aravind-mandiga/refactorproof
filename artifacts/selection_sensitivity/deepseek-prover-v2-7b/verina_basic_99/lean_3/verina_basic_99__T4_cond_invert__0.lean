-- !benchmark @start import type=solution
import Mathlib
import Aesop
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
  if ¬ (x < 18) then
    let y := 2 * x
    x + y
  else
    let a := 2 * x
    let b := 4 * x
    (a + b) / 2
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
    have h₀ : Triple (x) h_precond = 3 * x := by
      -- Unfold the definition of Triple to see the actual computation
      unfold Triple
      -- Consider the two cases based on the condition x < 18
      split_ifs <;> simp_all [Triple_precond, Int.mul_emod, Int.add_emod, Int.emod_emod]
      <;> ring_nf at *
      <;> omega
    -- The result from the previous step
    exact h₀

  have h_div : (Triple (x) h_precond) / 3 = x := by
    rw [h_main]
    <;>
    (try decide) <;>
    (try ring_nf at * <;> omega) <;>
    (try
      {
        rw [show (3 * x : ℤ) = x + x + x by ring]
        simp [Int.add_emod, Int.mul_emod, Int.emod_emod] <;>
        (try omega) <;>
        (try ring_nf at * <;> omega)
      }) <;>
    (try
      {
        omega
      }) <;>
    (try
      {
        simp_all [Int.emod_eq_of_lt]
        <;>
        omega
      }) <;>
    (try
      {
        norm_num at * <;>
        ring_nf at * <;>
        omega
      })
    <;>
    (try
      {
        simp_all [Int.emod_eq_of_lt]
        <;>
        omega
      })
    <;>
    (try
      {
        omega
      })
    <;>
    (try
      {
        omega
      })

  have h_mul : ((Triple (x) h_precond) / 3) * 3 = Triple (x) h_precond := by
    rw [h_div]
    <;>
    simp_all [h_main]
    <;>
    ring_nf at * <;>
    linarith

  constructor <;> simp_all [Triple_postcond, h_main, h_div, h_mul]
  <;>
  (try omega) <;>
  (try ring_nf at *) <;>
  (try simp_all) <;>
  (try omega) <;>
  (try linarith)
  <;>
  (try omega)
  <;>
  (try
    {
      cases Int.emod_two_eq_zero_or_one x <;>
      simp_all [Int.mul_emod, Int.add_emod, Int.sub_emod, Int.emod_emod]
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
      simp_all [Int.mul_emod, Int.add_emod, Int.sub_emod, Int.emod_emod]
      <;>
      omega
    })
  <;>
  (try
    {
      cases Int.emod_two_eq_zero_or_one x <;>
      simp_all [Int.mul_emod, Int.add_emod, Int.sub_emod, Int.emod_emod]
      <;>
      omega
    })
  <;>
  omega
  -- !benchmark @end proof
