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
  if x = 0 then 0 else
    let y := 2 * x
    y + x
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
    dsimp only [Triple_postcond, Triple, Triple_precond] at *
    split_ifs <;>
    (try cases x <;> simp_all) <;>
    (try
      {
        norm_num at *
        <;>
        ring_nf at * <;>
        omega
      }) <;>
    (try
      {
        omega
      }) <;>
    (try
      {
        norm_num
        <;>
        ring_nf
        <;>
        omega
      })
    <;>
    (try
      {
        norm_num
        <;>
        ring_nf
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
        norm_num
        <;>
        ring_nf
        <;>
        omega
      })
    <;>
    (try
      {
        omega
      })
  exact h_main
  -- !benchmark @end proof
