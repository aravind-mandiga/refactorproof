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

private def Triple__rp_helper_5b862de8 (x : Int) (h_precond : Triple_precond (x)) : Int :=
  if x < 18 then
    let a := 2 * x
    let b := 4 * x
    (a + b) / 2
  else
    let y := 2 * x
    x + y
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  Triple__rp_helper_5b862de8 x h_precond
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
  have h_main : Triple x h_precond = 3 * x := by
    have h₁ : Triple x h_precond = 3 * x := by
      dsimp only [Triple]
      split_ifs <;> simp_all [Triple_precond, Int.mul_emod, Int.add_emod]
      <;> ring_nf at * <;>
      (try omega) <;>
      (try {
        omega
      }) <;>
      (try {
        simp_all [Int.mul_emod, Int.add_emod]
        <;> omega
      }) <;>
      (try {
        simp_all [Int.mul_emod, Int.add_emod]
        <;> omega
      })
      <;>
      omega
    exact h₁

  have h_post1 : (Triple x h_precond) / 3 = x := by
    rw [h_main]
    <;>
    (try omega) <;>
    (try {
      apply Int.ediv_eq_of_eq_mul_right (by omega)
      <;> ring
    }) <;>
    (try omega)
    <;>
    (try {
      omega
    })

  have h_post2 : (Triple x h_precond) / 3 * 3 = Triple x h_precond := by
    rw [h_main]
    <;>
    (try omega) <;>
    (try {
      simp_all [Int.mul_emod, Int.add_emod]
      <;> omega
    }) <;>
    (try {
      omega
    })

  constructor <;> simp_all [Triple_postcond]
  <;> norm_num
  <;>
  (try omega) <;>
  (try
    {
      aesop
    }) <;>
  (try
    {
      norm_num at *
      <;> omega
    })
  -- !benchmark @end proof
