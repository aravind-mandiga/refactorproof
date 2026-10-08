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

private def Triple__rp_helper_574d859a (x : Int) (h_precond : Triple_precond (x)) : Int :=
  if x = 0 then 0 else
    let y := 2 * x
    x + y
-- !benchmark @end code_aux


def Triple (x : Int) (h_precond : Triple_precond (x)) : Int :=
  -- !benchmark @start code
  Triple__rp_helper_574d859a x h_precond
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
  have h_main : Triple_postcond (x) (Triple (x) h_precond) h_precond := by
    simp only [Triple_precond, Triple, Triple_postcond, Triple__rp_helper_574d859a]
    split_ifs <;>
    (try { contradiction }) <;>
    (try { simp_all [Int.mul_ediv_cancel_left, Int.mul_emod, Int.add_emod, Int.emod_emod] }) <;>
    (try {
      ring_nf at * <;>
      norm_num at * <;>
      omega
    }) <;>
    (try {
      cases x <;> simp_all [Int.mul_ediv_cancel_left, Int.mul_emod, Int.add_emod, Int.emod_emod] <;>
      ring_nf at * <;>
      norm_num at * <;>
      omega
    }) <;>
    (try {
      aesop
    }) <;>
    (try {
      omega
    })
    <;>
    (try {
      simp_all [Int.mul_ediv_cancel_left, Int.mul_emod, Int.add_emod, Int.emod_emod]
      <;> ring_nf at * <;> norm_num at * <;> omega
    })
    <;>
    (try {
      aesop
    })
    <;>
    (try {
      omega
    })
  exact h_main
  -- !benchmark @end proof
